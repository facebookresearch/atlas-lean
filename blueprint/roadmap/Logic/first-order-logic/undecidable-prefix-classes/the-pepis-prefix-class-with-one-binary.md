# The prefix class ∀*∃ with one binary relation is undecidable

Satisfiability is undecidable for prenex sentences with a block of universal quantifiers followed by one existential quantifier, without equality and function symbols, using a single binary relation symbol and nothing else.

**Theorem (Kalmár and Surányi).** The [prefix-vocabulary class](prefix-vocabulary-classes.md) $[\forall^*\exists, (0, 1), (0)]$ is undecidable: no algorithm decides satisfiability of sentences $\forall x_1 \cdots \forall x_k \exists y\, \varphi$ with $\varphi$ quantifier-free in one binary relation symbol, without equality.

The number of universal quantifiers is not bounded in this class. The title of the original paper names its prefix, which has a single existential quantifier, after Pepis.

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

Satisfiability of arbitrary first-order sentences is undecidable, and the class is shown undecidable by effectively transforming arbitrary sentences, or a known undecidable class, into sentences of the class while preserving satisfiability. The classification places the class among its undecidable cases, together with the decidable boundary it borders.

## Sources

- L. Kalmár and J. Surányi, "On the reduction of the decision problem. Third paper. Pepis prefix, a single binary predicate", *The Journal of Symbolic Logic* 15(3):161–173, 1950, doi:[10.2307/2266781](https://doi.org/10.2307/2266781) (original source, cited beside the copies read).
- Yu. Sh. Gurevich, "The decision problem for the logic of predicates and of operations", *Algebra and Logic* 8(3):160–174, 1969, doi:[10.1007/BF02306690](https://doi.org/10.1007/BF02306690), read in the author's copy of the English translation at <https://web.eecs.umich.edu/~gurevich/Opera/13en.pdf>: Theorem 6, class $\Phi_3 = \Phi(\forall^\infty\exists, (0, 1), \emptyset)$ among the nine minimal undecidable classes without equality.
- E. Grädel, "Decidable fragments of first-order and fixed-point logic", lecture slides, also read at <https://iccl.inf.tu-dresden.de/w/images/1/15/FMT-Lecture9.pdf>: class (3) on the slide "The complete classification: undecidable cases A: Pure predicate logic (without functions, without =)".
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, cited beside the copies read.
