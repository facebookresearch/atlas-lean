# Ranking-matching lemma: some candidate has a perfectly matchable domination graph

For every ranking profile $\sigma$ there exists a candidate $a$ whose domination graph $G_\sigma(a)$ has a perfect matching. More generally, for any weights $p : V \to \mathbb{R}_{\ge 0}$ and $q : C \to \mathbb{R}_{\ge 0}$ with $\sum_v p(v) = \sum_c q(c)$, there is a candidate $a$ admitting a fractional perfect matching between voters (weights $p$) and candidates (weights $q$) in which voter $v$ is matched only to candidates $c$ with $a \succeq_v c$; the case $q(c) = \lvert \{ v' : \mathrm{top}(v') = c \}\rvert$ gives the domination statement.

## Proof sketch

By Hall's theorem it suffices to find $a$ such that for every set $S$ of candidates, the voters ranking $a$ above some member of $S$ (or equal to it) have total weight at least $q(S)$. Argue by induction on the number of candidates: remove a candidate whose violation of Hall's condition is witnessed by a minimal deficient set, redistribute its weight, and use the induction hypothesis on the smaller election; a careful choice of the removed candidate ensures the resulting candidate satisfies Hall's condition in the original election.

## Depends on

- [Domination graph of a candidate](domination-graph-of-a-candidate.md)

## Proof depends on

- [Domination graph of a candidate](domination-graph-of-a-candidate.md)

## Sources

- V. Gkatzelis, D. Halpern, N. Shah, "Resolving the Optimal Metric Distortion Conjecture", FOCS 2020, arXiv:2004.07447.
