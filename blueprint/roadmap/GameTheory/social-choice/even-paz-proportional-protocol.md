# Even-Paz proportional protocol

Let $n = 2^m$ agents, $m \ge 0$, have valuations on the cake $[0,1]$ as in the Robertson–Webb model (nonatomic
measures with $V_i([0,1]) = 1$), accessed through evaluation and cut queries. The Even–Paz protocol on a piece $[s,t]$ with a set of agents
gives the whole piece to the agent if there is one; otherwise each agent $i$ marks the point $z_i$ that
splits $[s,t]$ into two pieces of equal value to $i$, the marks are ordered with ties broken by agent
index, $z^*$ is the $(n/2)$-th mark, the $n/2$ agents with the first $n/2$ marks recurse on $[s, z^*]$
and the other $n/2$ agents recurse on $[z^*, t]$. Then every agent $i$ receives a piece of value at
least $1/n$, and the protocol uses $O(n \log n)$ queries.

The equal-halves split requires the number of agents in each recursive call to be even, which holds
for powers of two. For other $n$ it fails: with three agents having the same uniform valuation, a half
of the cake shared by two of them cannot give both value $1/3$.

The statement covers $n$ a power of two. The general-$n$ protocol is a separate page and is not
covered by this one: with $n_1 = \lfloor n/2 \rfloor$, each agent marks the point $z_i$ with
$V_i([s, z_i]) = (n_1/n) V_i([s,t])$, the $n_1$ agents with the first $n_1$ marks recurse on $[s, z^*]$ for the $n_1$-th mark
$z^*$, and the others recurse on $[z^*, t]$.

## Depends on

- [Cake cutting in the Robertson-Webb query model](cake-cutting-in-the-robertson-webb-query-model.md)

## Sources

- A. Procaccia, *Harvard CS 1360 (Spring 2025) notes: cake cutting*, Section 3.2.3 (Even–Paz algorithm
  for $n = 2^k$ players, proportionality and $O(n \log n)$ operations).
  <https://procaccia.info/courses/CS1360-S25/notes10.pdf>
