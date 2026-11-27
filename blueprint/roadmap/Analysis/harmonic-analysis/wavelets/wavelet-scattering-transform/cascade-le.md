# Cascade inequality

Let $X$ be a set, $a, c : X \to [0, \infty]$ and $u_\lambda : X \to X$ for $\lambda \in \Lambda$. If $a(x) + \sum_\lambda c(u_\lambda x) \le c(x)$ for every $x$, then for every depth $m$,

$$\sum_{n < m} \sum_{|p| = n} a(u[p]\, x) + \sum_{|p| = m} c(u[p]\, x) \le c(x),$$

by induction on $m$, splitting each path along its first index. This is the bookkeeping of the proofs of Proposition 2.5 and Theorem 2.6 in S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), applied below to pairs of signals (nonexpansiveness) and to single signals (energy).
