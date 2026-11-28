# Plurality matching achieves the optimal deterministic metric distortion three

The deterministic voting rule PluralityMatching, which outputs a candidate $a$ whose domination graph $G_\sigma(a)$ has a perfect matching, is well defined, computable in polynomial time, and has metric distortion exactly $3$. Consequently the optimal distortion of deterministic voting rules is $3$.

## Proof sketch

Existence of such a candidate is the ranking-matching lemma, and the distortion bound is the matching certificate lemma; matching against the lower bound $3$ for all deterministic rules gives optimality. Polynomial time follows by testing, for each of the $m$ candidates, whether a bipartite graph on $2n$ vertices has a perfect matching.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)
- [Domination graph of a candidate](domination-graph-of-a-candidate.md)

## Proof depends on

- [Ranking-matching lemma: some candidate has a perfectly matchable domination graph](ranking-matching-lemma.md)
- [A perfect matching in the domination graph certifies distortion three](domination-matching-certifies-distortion-three.md)
- [No deterministic voting rule has metric distortion below three](deterministic-distortion-lower-bound-three.md)

## Sources

- V. Gkatzelis, D. Halpern, N. Shah, "Resolving the Optimal Metric Distortion Conjecture", FOCS 2020, arXiv:2004.07447.
