# Query hypergraph and fractional vertex covering number

For a full conjunctive query $q$ without self-joins whose atoms each have at least one variable, the
query hypergraph has one vertex per variable
and one hyperedge, the set of its variables, per atom. A fractional vertex cover assigns $v_x \ge 0$ to
every variable so that $\sum_{x \in \mathrm{vars}(S)} v_x \ge 1$ for every atom $S$; $\tau^*(q)$ is the
minimum of $\sum_x v_x$. By linear-programming duality it equals the maximum weight of a fractional
edge packing (weights $u_S \ge 0$ on atoms with $\sum_{S \ni x} u_S \le 1$ for every variable). This
covering problem is the one in the MPC lower bound; it is not the fractional edge cover of the AGM
bound.

## Expansion

This node states a precise definition.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Sources

- Communication Steps for Parallel Query Processing (Beame, Koutris, Suciu, PODS 2013) — Beame, Koutris, Suciu; ACM PODS, author copy, Section 2, "Vertex Cover and Edge Packing" and Figure 1. <https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf>
