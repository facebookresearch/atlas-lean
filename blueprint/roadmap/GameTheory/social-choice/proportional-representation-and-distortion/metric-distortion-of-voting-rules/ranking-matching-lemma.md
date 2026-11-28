# Ranking-matching lemma: some candidate has a perfectly matchable domination graph

For every ranking profile $\sigma$ there exists a candidate $a$ whose domination graph $G_\sigma(a)$ has a perfect matching. More generally, for any weights $p : V \to \mathbb{R}_{\ge 0}$ and $q : C \to \mathbb{R}_{\ge 0}$ with $\sum_v p(v) = \sum_c q(c)$, there is a candidate $a$ admitting a fractional perfect matching between voters (weights $p$) and candidates (weights $q$) in which voter $v$ is matched only to candidates $c$ with $a \succeq_v c$; the case $q(c) = \lvert \{ v' : \mathrm{top}(v') = c \}\rvert$ gives the domination statement.

## Proof sketch

By a weighted version of Hall's theorem, a fractional perfect matching exists exactly when every set of voters has total weight at most the weight of the candidates it may be matched to. Suppose the lemma fails and take a counterexample election with the smallest number of voters. For each candidate $a$ fix a minimal set of voters violating Hall's condition for $a$, and study how these violating sets for different candidates intersect. Removing a suitable violating set of voters together with the candidates they dominate, and renormalizing the weights, gives a smaller election; by minimality it has a candidate with a fractional perfect matching, and combining that matching with the removed part contradicts the choice of the counterexample. A suitable candidate can be found in strongly polynomial time by testing each candidate.

## Depends on

- [Domination graph of a candidate](domination-graph-of-a-candidate.md)

## Sources

- V. Gkatzelis, D. Halpern, N. Shah, "Resolving the Optimal Metric Distortion Conjecture", FOCS 2020, arXiv:2004.07447.
