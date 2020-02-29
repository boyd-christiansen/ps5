all: orderedcoll tests

orderedcoll: orderedcoll.ml 
	ocamlbuild -use-ocamlfind orderedcoll.byte

tests: tests.ml 
	ocamlbuild -use-ocamlfind tests.byte

clean:
	rm -rf _build *.byte