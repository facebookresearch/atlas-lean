# Sentences with two universal quantifiers and one function symbol are undecidable

Satisfiability is undecidable, without equality, for sentences with prefix ∀∀ over one binary relation and one unary function, and over one monadic relation and one binary function.

**Theorem (Gurevich).** The [prefix-vocabulary classes](prefix-vocabulary-classes.md) $[\forall^2, (0, 1), (1)]$ and $[\forall^2, (1), (0, 1)]$ are undecidable: no algorithm decides satisfiability of sentences $\forall x \forall y\, \varphi$, without equality, with $\varphi$ quantifier-free over one binary relation symbol and one unary function symbol, respectively over one monadic relation symbol and one binary function symbol.

Monadic relation symbols together with unary function symbols give the decidable class $[\mathrm{all}, (\omega), (\omega)]$ (Löb; Gurevich), so a binary symbol, relation or function, is needed.

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

Satisfiability of arbitrary first-order sentences is undecidable, and the class is shown undecidable by effectively transforming arbitrary sentences, or a known undecidable class, into sentences of the class while preserving satisfiability. The classification places the class among its undecidable cases, together with the decidable boundary it borders.

## Sources

- Yu. Sh. Gurevich, "The decision problem for the logic of predicates and of operations", *Algebra and Logic* 8(3):160–174, 1969, doi:[10.1007/BF02306690](https://doi.org/10.1007/BF02306690) (original source), read in the author's copy of the English translation at <https://web.eecs.umich.edu/~gurevich/Opera/13en.pdf>: Theorem 7, the strongly reducing classes $\Phi_{10} = \Phi(\forall^2, (0, 1), (1))$ and $\Phi_{11}$, and Theorems 8 and 9.
- Y. Gurevich, "The decision problem for standard classes", *The Journal of Symbolic Logic* 41(2):460–464, 1976, doi:[10.2307/2272244](https://doi.org/10.2307/2272244), read in the author's copy at <https://web.eecs.umich.edu/~gurevich/Opera/21.pdf>: the Main Theorem in Section 2, which lists $K(\forall^2, 2^1, 1^1)$ among the conservative classes and refers to the 1969 paper for the subclass without equality.
- E. Grädel, "Decidable fragments of first-order and fixed-point logic", lecture slides, also read at <https://iccl.inf.tu-dresden.de/w/images/1/15/FMT-Lecture9.pdf>: classes (12) and (13) on the slide "The complete classification: undecidable cases B: Classes with functions or equality" and class (3) on the slide "The complete classification: decidable cases".
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, cited beside the copies read.
