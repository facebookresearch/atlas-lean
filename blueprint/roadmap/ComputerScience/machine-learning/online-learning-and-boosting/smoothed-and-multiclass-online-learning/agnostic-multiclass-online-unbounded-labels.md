# Agnostic multiclass online learnability for unbounded label spaces

Let $H \subseteq Y^X$ with $Y$ arbitrary (possibly infinite). Then $H$ is agnostically online learnable (sublinear expected regret against every adaptive adversary) if and only if its multiclass Littlestone dimension $d$ is finite, and in that case, for $T \ge 2d$, regret $O\big(\sqrt{dT\log(T/d)}\big)$ is attained by a learner running multiplicative weights over experts that simulate the multiclass Standard Optimal Algorithm updated only on at most $d$ prescribed rounds; this is optimal up to the logarithmic factor. Moreover, online learnability and online uniform convergence separate: there is a multiclass class with Littlestone dimension one whose sequential Rademacher complexity does not vanish (its sequential graph dimension is infinite).

## Proof sketch

Experts are indexed by sets $J$ of at most $d$ rounds; expert $J$ predicts what the multiclass SOA would predict after being updated only on the rounds of $J$ before the current one, with their true (revealed) labels. Let $h^*$ be a best concept and consider the realizable subsequence of rounds where $h^*$ is correct; the expert whose $J$ is the set of rounds where the SOA run on that subsequence errs has $|J| \le d$ and makes at most $d$ more mistakes than $h^*$. Since experts use the revealed labels, there are only $\sum_{i \le d}\binom{T}{i} \le (eT/d)^d$ of them whatever the size of $Y$, and multiplicative weights gives regret $O(\sqrt{T\,d\log(T/d)}) + d$. The separation uses a class with Littlestone dimension one whose concepts use infinitely many labels, so that its sequential graph dimension is infinite and sequential Rademacher averages do not converge.

## Depends on

- [Agnostic online learnability is characterized by the Littlestone dimension](../agnostic-online-learnability-is-characterized-by-the-littlestone-dimension.md)
- [The Littlestone dimension is the optimal mistake bound](../the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [The $\sqrt{T}$ regret bound of Hedge](../hedge-algorithm/regret-le-two-sqrt.md)

## Sources

- S. Hanneke, S. Moran, V. Raman, U. Subedi, A. Tewari, "Multiclass Online Learning and Uniform Convergence", COLT (2023), arXiv:2303.17716, Theorems 1, 4 and 7.
- S. Ben-David, D. Pal, S. Shalev-Shwartz, "Agnostic Online Learning", COLT (2009).
