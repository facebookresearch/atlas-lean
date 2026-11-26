# Shortening a set of independent vectors with an incremental GDD oracle

Let $S$ be a set of $n$ linearly independent vectors of a lattice $L$ with $\|S\| = \max_i\|s_i\| > 8\gamma\,\phi(L)$. Given an $\mathrm{IncGDD}^{\phi}_\gamma$ oracle, one can compute in polynomial time $n$ linearly independent lattice vectors $S'$ with $\|S'\| \le \|S\|/2$, by replacing each vector of $S$ longer than $\|S\|/2$, one at a time, by the lattice vector the oracle returns (at most $n$ oracle calls). Iterating solves $\mathrm{GIVP}^{\phi}_{8\gamma}$ starting from any basis.

## Proof sketch

Let $s_n$ be a longest vector, $u$ a unit vector orthogonal to $s_1, \dots, s_{n-1}$ and $t = \tfrac{\|S\|}{4}u$, and call the oracle with some $r \in (\gamma\phi(L), \|S\|/8)$. The returned $s$ satisfies $\|s - t\| \le \|S\|/8 + r < \|S\|/4$, so $\langle s, u\rangle > 0$ (hence $s$ is independent of $s_1, \dots, s_{n-1}$) and $\|s\| < \|S\|/2$; replace $s_n$ by $s$. Repeat for every remaining vector longer than $\|S\|/2$, with $u$ a unit vector orthogonal to the other current vectors, $t = \tfrac{\|S\|}{4}u$ for the original $\|S\|$ and the same $r$: the oracle's bound $\|S_{\mathrm{cur}}\|/8 + r \le \|S\|/8 + r$ keeps each new vector shorter than $\|S\|/2$.

## Depends on

- [Shortest vector, independent vectors and guaranteed distance decoding problems](svp-sivp-givp-and-gdd.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007, Lemma 5.10.
