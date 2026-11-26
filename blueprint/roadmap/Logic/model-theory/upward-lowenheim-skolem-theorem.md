# Upward Löwenheim–Skolem theorem

Let $L$ be a first-order language, $M$ an infinite $L$-structure and $\kappa$ a cardinal with $|L| \le \kappa$ and $|M| \le \kappa$. Then $M$ has an elementary extension of cardinality exactly $\kappa$: there are an $L$-structure $N$ with $|N| = \kappa$ and an elementary embedding of $M$ into $N$.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.12, the remark after Theorem 3.38 (a set of formulas with an infinite model has a model of every cardinality at least that of the signature), p. 80.
- Mathlib, `FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_ge` in `Mathlib/ModelTheory/Satisfiability.lean`.
