# Shortening a set of independent vectors with an incremental GDD oracle

Let $S$ be a set of $n$ linearly independent vectors of a lattice $L$ with $\|S\| = \max_i\|s_i\| > 8\gamma\,\phi(L)$. Given an $\mathrm{IncGDD}^{\phi}_{\gamma,8}$ oracle, one can compute in polynomial time $n$ linearly independent lattice vectors $S'$ with $\|S'\| \le \|S\|/2$ (Micciancio and Regev, Lemma 5.10). Iterating solves $\mathrm{GIVP}^{\phi}_{8\gamma}$ starting from any basis.

## Proof sketch

Let $s_n$ be a longest vector, $u$ a unit vector orthogonal to $s_1, \dots, s_{n-1}$ and $t = \tfrac{\|S\|}{2}u$, and call the $\mathrm{IncGDD}^{\phi}_{\gamma,8}$ oracle with the computable radius $r = \|S\|/8 > \gamma\phi(L)$. The returned lattice vector $s$ satisfies $\|s - t\| \le \|S\|/8 + r = \|S\|/4$, so $\langle s, u\rangle > 0$ (hence $s$ is independent of $s_1, \dots, s_{n-1}$) and $\|s\| \le \tfrac{3}{4}\|S\|$. Replacing $s_n$ by $s$ lowers $\prod_i \|s_i\|$ by a factor of at least $3/4$; repeating until every vector has length at most $\|S\|/2$ takes $O(n)$ oracle calls.

## Depends on

- [Shortest vector, independent vectors and guaranteed distance decoding problems](svp-sivp-givp-and-gdd.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007, Lemma 5.10.
