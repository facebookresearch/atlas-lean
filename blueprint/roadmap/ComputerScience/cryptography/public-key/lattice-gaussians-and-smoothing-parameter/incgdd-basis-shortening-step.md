# Shortening a set of independent vectors with an incremental GDD oracle

Let $S$ be a set of $n$ linearly independent vectors of a lattice $L$ with $\|S\| = \max_i\|s_i\| > \gamma\,\phi(L)$. Given an $\mathrm{IncGDD}^{\phi}_\gamma$ oracle, one can compute in polynomial time a new set $S'$ of $n$ linearly independent lattice vectors with $\|S'\| \le \|S\|/2$ (replacing a longest vector by the difference between a target point and its decoded lattice point). Iterating solves $\mathrm{GIVP}^{\phi}_{\gamma}$ starting from any basis.

## Proof sketch

Choose a target $t$ orthogonal-ish to the span of the other vectors at distance about $\|S\|/2$ beyond them; the oracle returns a lattice vector within distance $\|S\|/8$ of $t$, whose difference with a suitable combination is a short vector independent of the remaining ones.

## Depends on

- [Shortest vector, independent vectors and guaranteed distance decoding problems](svp-sivp-givp-and-gdd.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
