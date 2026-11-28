# No finite protocol finds contiguous envy-free divisions for three or more agents

For $n \ge 3$ agents with nonatomic valuations on $[0, 1]$, there is no finite (bounded or unbounded but always terminating) protocol in the Robertson–Webb query model that always outputs an envy-free allocation in which every agent receives a single interval, even though such allocations always exist by Stromquist's moving-knife theorem.

## Proof sketch

For three agents, construct rigid measure systems: families of valuations for which every envy-free division into intervals must cut at two specific points determined by hidden parameters. One agent's measure, together with the answers to any finite set of queries, does not determine these parameters, so for any finite protocol there are valuations in the family consistent with all answers for which the protocol's output cuts at the wrong points and is therefore not envy-free. The construction extends to every $n \ge 3$.

## Depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)

## Sources

- W. Stromquist, "Envy-free cake divisions cannot be found by finite protocols", Electronic Journal of Combinatorics 15 (2008), R11.
