# The monadic theory of the real line is undecidable under CH

Assuming the continuum hypothesis, the set of monadic second-order sentences true in the real line $(\mathbb{R}, <)$ is undecidable, and so is the monadic theory of the class of all linear orders.

**Theorem (Shelah).** Assume the continuum hypothesis. Then:

1. the [monadic theory](monadic-second-order-theory-of-linear-orders.md) of the real order $(\mathbb{R}, <)$, with set quantifiers ranging over all subsets of $\mathbb{R}$, is undecidable;
2. the monadic theory of order, that is, of the class of all linear orders, is undecidable.

The source states that the continuum hypothesis can be weakened to the hypothesis that $\mathbb{R}$ is not the union of fewer than $2^{\aleph_0}$ sets of the first category, a consequence of Martin's axiom. In the same section it proves (under the same hypothesis) that the monadic theory of the binary tree $(2^{\leq\omega}, \trianglelefteq, \prec)$ of finite and infinite $0$-$1$ sequences, with the initial-segment and lexicographic orders, is undecidable (Theorem 7.3). By Rabin's theorem, restricting the set quantifiers to closed or $F_\sigma$ sets gives a decidable theory.

## Depends on

- [Monadic second-order theory of linear orders](monadic-second-order-theory-of-linear-orders.md)
- [Continuum hypothesis](../../../../SetTheory/cardinal-arithmetic/continuum-hypothesis/continuum-hypothesis.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Tarski's undefinability theorem](../../../proof-theory/g-del-s-incompleteness-theorems/tarski-s-undefinability-theorem.md)

## Expansion

The proof shows that true first-order arithmetic is recursive in the monadic theory of order (Conclusion 7.15): for every first-order sentence $\theta$ it effectively builds a monadic sentence $G(\theta)$ such that $(\mathbb{R}, <) \models G(\theta)$ iff $\theta$ has an $\omega$-model, a model whose universe with its first binary relation is isomorphic to $(\omega, x + 1 = y)$ (Theorem 7.14). The construction codes, inside $\mathbb{R}$, a family of $2^{\aleph_0}$ pairwise disjoint countable dense sets and a set $Q$ that meets perfect sets in a prescribed way (Lemmas 7.4 and 7.5); building $Q$ by transfinite recursion over an enumeration of the perfect sets is where the continuum hypothesis, or the weaker covering hypothesis, is used. Since true arithmetic is not decidable (it is not even arithmetical, by Tarski's undefinability theorem), neither is the monadic theory of the reals or of the class of all orders.

## Sources

- S. Shelah, "The monadic theory of order", *Annals of Mathematics* (2) 102(3):379–419, 1975, doi:10.2307/1971037; read as the slightly corrected version arXiv:2305.00968v1, <https://arxiv.org/abs/2305.00968v1>: Theorem 7.1 of arXiv:2305.00968v1, with Theorems 7.3 and 7.14, Conclusion 7.15 and Lemmas 7.4–7.5.
