# Parsimony is inconsistent in the Felsenstein zone

Let $\mu$ be a probability measure, $0 \le Q < \frac12$ and $Q(1 - Q) < P^2$, and let $\sigma_0, \sigma_1, \dots$ be measurable random site patterns that are pairwise independent and identically distributed, with $\Pr(\sigma_0 = \tau)$ the [pattern probability](pattern-prob.md) of $\tau$ for parameters $P$ on the branches to $A$, $C$ and $Q$ on the others. Then almost surely, for all sufficiently large $n$,

$$\sum_{i<n} s_{AC|BD}(\sigma_i) < \sum_{i<n} s_{AB|CD}(\sigma_i) \quad\text{and}\quad \sum_{i<n} s_{AC|BD}(\sigma_i) < \sum_{i<n} s_{AD|BC}(\sigma_i),$$

where $s$ is the [parsimony score](parsimony-score.md) (Felsenstein 1978).

## Sources

- J. Felsenstein, *Cases in which parsimony or compatibility methods will be positively misleading*, Syst. Zool. 27 (1978), 401–410.
