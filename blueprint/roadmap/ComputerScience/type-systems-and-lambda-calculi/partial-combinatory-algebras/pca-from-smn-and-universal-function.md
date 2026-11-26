# A pca from an s-m-n theorem and a universal function

Let $A$ be a set with a partial application $e \cdot a$ given by a numbering of partial functions. Suppose (i) *pairing*: there is a computable injective pairing on $A$ that the numbered functions can compose with; (ii) *s-m-n*: for every index $e$ of a two-argument function there is an index $s(e, a)$, depending computably on $(e, a)$, with $s(e,a)\cdot b \simeq e\cdot\langle a, b\rangle$; and (iii) a *universal function*: application itself is computed by some index. Then there are elements $\mathsf{k}, \mathsf{s}$ making $(A, \cdot)$ a partial combinatory algebra.

## Proof sketch

Take $\mathsf{k}$ to be an index that on input $a$ returns $s(\mathrm{fst}, a)$ for an index $\mathrm{fst}$ of the first projection. For $\mathsf{s}$, use s-m-n twice to curry an index of the function $\langle\langle a,b\rangle, c\rangle \mapsto (a\cdot c)\cdot(b\cdot c)$, which exists by the universal function; totality of the curried stages gives definedness of $\mathsf{s}\,a\,b$.

## Depends on

- [Partial combinatory algebra](partial-combinatory-algebra.md)
- [Parametrized s-m-n theorem](../../../TheoryOfComputation/computability/exists-computable-code.md)

## Sources

- J. van Oosten, "Realizability: An Introduction to its Categorical Side", Studies in Logic and the Foundations of Mathematics 152, Elsevier, 2008.
- S. C. Kleene, "Introduction to Metamathematics", North-Holland and Van Nostrand, 1952.
