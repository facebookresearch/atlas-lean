# The prefix class ∀³∃* with one binary relation is undecidable

Satisfiability is undecidable for prenex sentences with three universal quantifiers followed by a block of existential quantifiers, without equality and function symbols, using a single binary relation symbol.

**Theorem (Kalmár and Surányi).** The [prefix-vocabulary class](prefix-vocabulary-classes.md) $[\forall^3\exists^*, (0, 1), (0)]$ is undecidable: no algorithm decides satisfiability of sentences $\forall x \forall y \forall z\, \exists u_1 \cdots \exists u_n\, \varphi$ with $\varphi$ quantifier-free in one binary relation symbol, without equality.

With two universal quantifiers in place of three the class falls inside the decidable Gödel class $[\exists^*\forall^2\exists^*, \mathrm{all}, (0)]$.

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

Satisfiability of arbitrary first-order sentences is undecidable, and the class is shown undecidable by effectively transforming arbitrary sentences, or a known undecidable class, into sentences of the class while preserving satisfiability. The classification places the class among its undecidable cases, together with the decidable boundary it borders.

## Sources

- L. Kalmár and J. Surányi, "On the reduction of the decision problem", *The Journal of Symbolic Logic* 12(3):65–73, 1947, doi:[10.2307/2267211](https://doi.org/10.2307/2267211) (original source, cited beside the copies read).
- Yu. Sh. Gurevich, "The decision problem for the logic of predicates and of operations", *Algebra and Logic* 8(3):160–174, 1969, doi:[10.1007/BF02306690](https://doi.org/10.1007/BF02306690), read in the author's copy of the English translation at <https://web.eecs.umich.edu/~gurevich/Opera/13en.pdf>: Theorem 6, class $\Phi_6 = \Phi(\forall^3\exists^\infty, (0, 1), \emptyset)$, and the criterion of Theorem 6 that a class without function symbols is decidable when its prefixes lie in $\exists^*\forall^*$ or $\exists^*\forall^2\exists^*$.
- E. Grädel, "Decidable fragments of first-order and fixed-point logic", lecture slides, also read at <https://iccl.inf.tu-dresden.de/w/images/1/15/FMT-Lecture9.pdf>: class (6) on the slide "The complete classification: undecidable cases A: Pure predicate logic (without functions, without =)" and class (2) on the slide "The complete classification: decidable cases".
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, cited beside the copies read.
