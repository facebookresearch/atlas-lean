# Every position has a unique innermost strict container

Let $P$ be a [secondary structure](../nussinov-algorithm-for-rna-secondary-structure/is-structure.md) and $x$ a natural number. Then either

- no pair $(p_1, p_2) \in P$ has $p_1 < x < p_2$, or
- there is exactly one pair $p \in P$ with $p_1 < x < p_2$ such that no [branch](branches.md) $(q_1, q_2)$ of $p$ has $q_1 < x < q_2$.

This is an innermost-container assignment, not a decomposition of positions into loops: an endpoint of a pair $q$ is assigned to the loop of which $q$ is a branch, never to the loop closed by $q$.
