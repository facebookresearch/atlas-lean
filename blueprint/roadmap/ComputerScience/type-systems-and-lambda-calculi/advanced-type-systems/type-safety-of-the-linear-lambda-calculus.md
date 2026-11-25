# Type safety of the linear lambda calculus

In the linear lambda calculus with multiplicative connectives ($\otimes$, $\multimap$, unit) and additive connectives ($\&$, $\oplus$, $\top$, $0$), typing contexts are split among premises by the multiplicative rules, shared by both premises of $\&$-introduction and by both branches of $\oplus$-elimination (whose discriminant uses a separate part of the context), and discarded by $\top$-introduction and $0$-elimination. Under call-by-value semantics, well-typed closed terms satisfy progress and preservation. In the purely multiplicative fragment every variable of the context occurs exactly once in a well-typed term; the affine variant additionally admits weakening.

## Proof depends on

- [Structural lemmas for typing judgments](../type-soundness/structural-lemmas-for-typing-judgments.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Syntactic type safety (proof prerequisite; not yet stated)

## Sources

- F. Pfenning, *Lecture notes on linear functional programming*, 15-814 Types and Programming Languages, Carnegie Mellon University
- P. Wadler, "A taste of linear logic", *MFCS 1993*, LNCS 711, Springer, 1993
