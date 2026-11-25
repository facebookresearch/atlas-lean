# LTL model checking is emptiness of an intersection

All initial infinite runs of a transition system satisfy an LTL formula $\varphi$ iff
$L_\omega(A_P) \cap L_\omega(A_{\neg\varphi}) = \emptyset$.

The automaton $A_{\neg\varphi}$ of the negated formula takes the place of the complement of
$A_\varphi$: complementing $A_\varphi$ by a general construction would cost a second
exponential, whereas $A_{\neg\varphi}$ has $2^{O(|\varphi|)}$ states. The intersection is the
synchronized product, and its emptiness is decided by the lasso test.

## Informally uses

- [LTL satisfaction iff the counterexample language is empty](models-iff-language-empty.md):
  the counterexample product is the intersection.
- [Product accepts exactly the runs accepted by the recognizer](mem-product-iff.md): the product
  computes the intersection.

## Background

- [LTL model checking is language inclusion](models-iff-language-le.md): the inclusion form,
  from which Vardi derives this emptiness form.

- [Büchi automata are closed under complementation](../../../TheoryOfComputation/omega-automata-and-games/boolean-closure-of-b-chi-automata/exists-buchi-compl.md):
  the general complementation that the negated formula avoids.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 4.2.
