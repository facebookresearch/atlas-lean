# A perfect matching in the domination graph certifies distortion three

If the domination graph $G_\sigma(a)$ of candidate $a$ has a perfect matching, then for every metric $d$ consistent with $\sigma$ and every candidate $b$,

$$
\mathrm{SC}(a, d) \le 3\, \mathrm{SC}(b, d).
$$

## Proof sketch

Let $\pi$ be the matching. For each voter $v$, consistency and $a \succeq_v \mathrm{top}(\pi(v))$ give $d(v, a) \le d(v, \mathrm{top}(\pi(v)))$, and by the triangle inequality this is at most $d(v, b) + d(b, \pi(v)) + d(\pi(v), \mathrm{top}(\pi(v)))$. Since $\mathrm{top}(\pi(v))$ is the closest candidate to $\pi(v)$, the last term is at most $d(\pi(v), b)$. Summing over $v$ and using that $\pi$ is a bijection gives $\mathrm{SC}(a) \le \mathrm{SC}(b) + 2\,\mathrm{SC}(b)$.

## Depends on

- [Domination graph of a candidate](domination-graph-of-a-candidate.md)
- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Sources

- V. Gkatzelis, D. Halpern, N. Shah, "Resolving the Optimal Metric Distortion Conjecture", FOCS 2020, arXiv:2004.07447.
