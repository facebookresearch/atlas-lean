# Domination graph of a candidate

Given a ranking profile $\sigma$ over candidates $C$ for voters $V$, let $\mathrm{top}(v)$ be the first choice of voter $v$. The domination graph of a candidate $a$ is the bipartite graph $G_\sigma(a)$ with two copies of $V$ as its sides and an edge between $v$ (left) and $v'$ (right) if and only if $v$ ranks $a$ at least as high as $\mathrm{top}(v')$, i.e. $a = \mathrm{top}(v')$ or $a \succ_v \mathrm{top}(v')$. A perfect matching of $G_\sigma(a)$ is a bijection $\pi : V \to V$ with $a \succeq_v \mathrm{top}(\pi(v))$ for every $v$.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Sources

- V. Gkatzelis, D. Halpern, N. Shah, "Resolving the Optimal Metric Distortion Conjecture", FOCS 2020, arXiv:2004.07447.
