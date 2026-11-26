# Shortening a set of independent vectors with an incremental GDD oracle

Let $S$ be a set of $n$ linearly independent vectors of a lattice $L$ with $\|S\| = \max_i\|s_i\| > 8\gamma\,\phi(L)$. Given an $\mathrm{IncGDD}^{\phi}_{\gamma,8}$ oracle, one can compute in polynomial time $n$ linearly independent lattice vectors $S'$ with $\|S'\| \le \|S\|/2$; this halving step is the core of the proof of Micciancio and Regev, Lemma 5.10. Iterating it solves $\mathrm{GIVP}^{\phi}_{8\gamma}$ starting from any basis, which is the reduction from $\mathrm{GIVP}^{\phi}_{8\gamma}$ to $\mathrm{IncGDD}^{\phi}_{\gamma,8}$ that Lemma 5.10 states.

## Proof sketch

Start with $S_{\mathrm{cur}} = S$ and keep the computable radius $r = \|S\|/8 > \gamma\phi(L)$ of the original $S$. While $\|S_{\mathrm{cur}}\| > \|S\|/2$, let $s_n$ be a longest vector of $S_{\mathrm{cur}}$, $u$ a unit vector in the span of $L$ orthogonal to the other $n - 1$ vectors of $S_{\mathrm{cur}}$ and $t = \tfrac{\|S_{\mathrm{cur}}\|}{2}u$, and call the $\mathrm{IncGDD}^{\phi}_{\gamma,8}$ oracle on $S_{\mathrm{cur}}$, $t$ and $r$. The returned lattice vector $s$ satisfies $\|s - t\| \le \|S_{\mathrm{cur}}\|/8 + \|S\|/8 < \tfrac38\|S_{\mathrm{cur}}\|$, so $\langle s, u\rangle > \tfrac18\|S_{\mathrm{cur}}\| > 0$ (hence $s$ is independent of the other vectors) and $\|s\| < \tfrac78\|S_{\mathrm{cur}}\|$; replace $s_n$ by $s$. Each replacement shrinks the replaced vector by a factor $7/8$ and $(7/8)^6 < 1/2$, so at most $6n$ oracle calls bring every vector to length at most $\|S\|/2$.

## Depends on

- [Shortest vector, independent vectors and guaranteed distance decoding problems](svp-sivp-givp-and-gdd.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007, Lemma 5.10.
