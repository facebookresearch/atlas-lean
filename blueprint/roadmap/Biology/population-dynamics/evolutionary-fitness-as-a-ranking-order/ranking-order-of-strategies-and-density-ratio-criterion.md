# Evolutionary fitness as a ranking order of strategies

**Setting.** Inherited units (strategies) $v$ range over a compact metric space $V$ with Borel $\sigma$-algebra $\Sigma$. The presence of a set $A \in \Sigma$ at time $t$ is a finite Borel measure $\mu^{(t)}(A)$, smooth in $t$, uniformly bounded ($\mu^{(t)}(V) \le c$), with $\mu^{(t)}(A) \to 0$ meaning extinction of $A$.

**Definitions.**
- $A$ is **selected** if $\mu^{(t)}(V \setminus A) \to 0$ while $\mu^{(t)}(A) \not\to 0$.
- $A$ is **better than** $B$ ($A \succ B$) if $\mu^{(t)}(B)/\mu^{(t)}(A) \to 0$; $A$ is **strongly better** than $B$ if every subset of $A$ of positive measure is better than $B$. Both relations are transitive and antisymmetric (partial orders).
- A strategy $v$ is better than $w$ if some neighbourhoods $O(v)$, $O(w)$ satisfy $O(v)$ strongly better than $O(w)$.
- A functional $J$ on $V$ is an **evolutionary fitness** if $J(v) > J(w)$ implies $v \succ w$.

Under boundedness, $v \succ w$ forces the measure of some neighbourhood of $w$ to vanish, and only global maximisers of an evolutionary fitness survive in the long run (the variational principle of selection).

**Theorem (density criterion).** Suppose $\mu^{(t)}$ has a density $\eta(v, t)$ with respect to a fixed measure $\mu^*$. If there are neighbourhoods $O(v)$ and $O(w)$ such that

$$\frac{\eta(w', t)}{\eta(v', t)} \to 0 \quad \text{uniformly in } v' \in O(v),\ w' \in O(w), \quad t \to \infty,$$

then $v \succ w$.

## Expansion

Uniform convergence lets the ratio bound pass under the integral $\mu^{(t)}(B) = \int_B \eta\, d\mu^*$ for every positive-measure subset of $O(v)$, which is exactly the strong ranking. Uniformity cannot be dropped: for $\partial_t \rho = k(v,t)\rho - \rho\int_0^1 k\rho\,dv$ with $k = vt\,e^{-vt}$, the density tends to $0$ at every $v$ while $\mu^{(t)}([0,1]) \equiv 1$. The ranking may depend on initial conditions, as a cyclic three-species replicator example shows.

## Sources

- O. Kuzenkov, A. Morozov, *Towards the construction of a mathematically rigorous framework for the modelling of evolutionary fitness*, Bull. Math. Biol. 81 (2019), 4675–4700 (Assumptions 1–5, Definitions 1–5, Theorem 1, Example 2). <https://doi.org/10.1007/s11538-019-00602-3> (PMCID: PMC6874698)
