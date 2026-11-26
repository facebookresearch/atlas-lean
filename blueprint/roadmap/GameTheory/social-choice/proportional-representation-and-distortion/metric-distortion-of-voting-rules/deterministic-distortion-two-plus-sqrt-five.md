# A deterministic rule with metric distortion 2 + sqrt(5)

There is a polynomial-time deterministic voting rule with metric distortion at most $2 + \sqrt 5 \approx 4.236$; in particular the uncovered-set bound $5$ is not optimal. The rule selects a candidate minimizing a weighted tournament quantity derived from the matrix of pairwise majority margins.

## Proof sketch

Define for each pair $(a, b)$ the fraction of voters preferring $a$ to $b$, and choose a candidate $a$ such that for every $b$ either $a$ beats $b$ by a large margin or some $c$ dominates $b$ strongly while being dominated weakly by $a$. A linear-programming characterization of the worst-case metric (the dual of the distortion problem for fixed candidate pair) shows that the optimal tradeoff of these margins yields the golden-ratio-type constant $2 + \sqrt5$.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Proof depends on

- [Metric distortion of plurality, Borda and Copeland](plurality-borda-copeland-distortion.md)

## Sources

- K. Munagala, K. Wang, "Improved Metric Distortion for Deterministic Social Choice Rules", EC 2019, arXiv:1905.01401.
- D. Kempe, "An Analysis Framework for Metric Voting based on LP Duality", AAAI 2020, arXiv:1911.07162.
