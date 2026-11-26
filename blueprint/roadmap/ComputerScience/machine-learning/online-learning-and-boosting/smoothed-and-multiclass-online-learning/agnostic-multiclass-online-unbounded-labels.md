# Agnostic multiclass online learnability for unbounded label spaces

Let $H \subseteq Y^X$ with $Y$ arbitrary (possibly infinite). Then $H$ is agnostically online learnable (sublinear expected regret against every adaptive adversary) if and only if its multiclass Littlestone dimension $d$ is finite, and in that case regret $\tilde O(\sqrt{d T})$ is attained by a learner running multiplicative weights over experts that simulate the multiclass Standard Optimal Algorithm on subsequences of length $d$. Moreover, online learnability and online uniform convergence separate: there is a multiclass class with Littlestone dimension one whose sequential Rademacher complexity is unbounded.

## Proof sketch

Experts are indexed by subsequences of at most $d$ rounds together with labels to feed the multiclass SOA on those rounds; unlike the binary case, the best expert is not perfect, but it errs at most $d$ times more than the best fixed concept, because the SOA's version space Littlestone dimension drops on each fed round. The number of experts is $\binom{T}{\le d}$ times label choices restricted to labels actually predicted, which keeps the multiplicative-weights regret at $\tilde O(\sqrt{dT})$ even for infinite $Y$. The separation uses a class whose concepts spread over infinitely many labels so that sequential Rademacher averages diverge while the SOA still makes at most one mistake.

## Proof depends on

- [Agnostic online learnability is characterized by the Littlestone dimension](../agnostic-online-learnability-is-characterized-by-the-littlestone-dimension.md)
- [The Littlestone dimension is the optimal mistake bound](../the-littlestone-dimension-is-the-optimal-mistake-bound.md)
- [The $\sqrt{T}$ regret bound of Hedge](../hedge-algorithm/regret-le-two-sqrt.md)

## Sources

- S. Hanneke, S. Moran, V. Raman, U. Subedi, A. Tewari, "Multiclass Online Learning and Uniform Convergence", COLT (2023), arXiv:2303.17716.
- S. Ben-David, D. Pal, S. Shalev-Shwartz, "Agnostic Online Learning", COLT (2009).
