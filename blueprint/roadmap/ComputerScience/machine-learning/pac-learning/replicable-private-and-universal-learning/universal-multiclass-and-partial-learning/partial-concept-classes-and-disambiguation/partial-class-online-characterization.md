# Littlestone dimension characterizes online learnability of partial classes

For every partial concept class $H$, the following are equivalent: $\mathrm{LD}(H) < \infty$; $H$ is online learnable in the realizable mistake-bound model (with mistake bound exactly $\mathrm{LD}(H)$, attained by the Standard Optimal Algorithm restricted to realizable sequences); and $H$ is agnostically online learnable. There is also a partial class with teaching dimension at most $2$ and infinite Littlestone dimension, so small teaching dimension does not imply online learnability for partial classes.

## Proof sketch

The Standard Optimal Algorithm predicts the label whose version space has larger Littlestone dimension; each mistake strictly decreases the Littlestone dimension of the realizable version space, exactly as for total classes, because only realizability of finite labelled sequences enters the argument. The agnostic case follows by running experts that simulate the Standard Optimal Algorithm on subsequences, as in the Ben-David–Pál–Shalev-Shwartz construction.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Online classification protocol, mistakes and regret](../../../../online-learning-and-boosting/online-classification-protocol-mistakes-and-regret.md)

## Proof depends on

- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)
- [Agnostic online learnability is characterized by the Littlestone dimension](../../../../online-learning-and-boosting/agnostic-online-learnability-is-characterized-by-the-littlestone-dimension.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Theorems 8 and 15 and Section E.
- S. Ben-David, D. Pal, S. Shalev-Shwartz, "Agnostic Online Learning", COLT (2009), Sections 3 and 4.
