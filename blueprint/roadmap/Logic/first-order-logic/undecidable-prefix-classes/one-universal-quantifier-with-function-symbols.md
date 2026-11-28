# Sentences with one universal quantifier and two unary functions or one binary function are undecidable

Satisfiability is undecidable for sentences with a single universal quantifier and equality, with no relation symbols, over either two unary function symbols or one binary function symbol.

**Theorem (Gurevich).** The [prefix-vocabulary classes](prefix-vocabulary-classes.md) $[\forall, (0), (2)]_=$ and $[\forall, (0), (0, 1)]_=$ are undecidable: no algorithm decides satisfiability of sentences $\forall x\, \varphi$ with $\varphi$ a quantifier-free formula built with equality from two unary function symbols, respectively from one binary function symbol, and no relation symbols. Both are conservative reduction classes, into which all first-order sentences are effectively translated preserving both satisfiability and finite satisfiability (Main Theorem of the source; Theorem 4.0.1 of Börger, Grädel and Gurevich).

With unary function symbols but only one of them, the class $[\mathrm{all}, (\omega), (1)]_=$ is decidable (Rabin).

## Depends on

- [Prefix-vocabulary classes](prefix-vocabulary-classes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Gurevich encodes the domino (tiling) problem: from a sentence one computes a set of domino types that tiles the quadrant exactly when the sentence is satisfiable, and periodically exactly when it is finitely satisfiable. A tiling is described by a sentence $\forall x\, P(x)$ with two unary functions moving right and up and one unary function per domino type, so the class with one universal quantifier and unary functions is conservative. The unary functions are then coded by two of them, and the two unary functions by one binary function, each step preserving satisfiability and finite satisfiability.

## Sources

- Y. Gurevich, "The decision problem for standard classes", *The Journal of Symbolic Logic* 41(2):460–464, 1976, doi:[10.2307/2272244](https://doi.org/10.2307/2272244) (original source), read in the author's copy at <https://web.eecs.umich.edu/~gurevich/Opera/21.pdf>: the Main Theorem in Section 2 (the conservative classes $K(\forall, 0, 1^2)$ and $K(\forall, 0, 2^1)$, and the decidable class $K(\mathrm{all}, 1^\omega, 1^1)$) and Theorems 3.1–3.3 in Section 3 with their proofs.
- E. Grädel, "Decidable fragments of first-order and fixed-point logic", lecture slides, also read at <https://iccl.inf.tu-dresden.de/w/images/1/15/FMT-Lecture9.pdf>: classes (10) and (11) on the slide "The complete classification: undecidable cases B: Classes with functions or equality" and class (6) on the slide "The complete classification: decidable cases".
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, doi:[10.1007/978-3-642-59207-2](https://doi.org/10.1007/978-3-642-59207-2), the standard reference for the classification, read in the authors' copy at <https://web.eecs.umich.edu/~gurevich/Books/00.pdf>: Theorem 4.0.1 and Table 1.2 (class (6)).
