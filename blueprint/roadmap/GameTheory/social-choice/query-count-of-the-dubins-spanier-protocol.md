# Query count of the Dubins-Spanier protocol

For $n \ge 1$ agents with valuations and queries as in the [Robertson–Webb model](cake-cutting-in-the-robertson-webb-query-model.md), the
discrete Dubins-Spanier protocol (while at least two agents remain, each remaining agent $i$ answers the cut query $y_i = \mathrm{cut}_i(s, 1/n)$
from the current left end $s$; an agent with the least $y_i$ receives $[s, y_i]$ and leaves, and $s := y_i$; the last agent receives the rest)
asks only cut queries that are defined, and it asks exactly $n + (n-1) + \dots + 2 = n(n+1)/2 - 1$ cut queries and no evaluation queries; for
$n = 1$ it asks none. Every cut asks for the value $1/n$, for the original number $n$ of agents, and the allocation into contiguous intervals
that the protocol returns is proportional by [Cut-and-choose and Dubins-Spanier](cut-and-choose-and-dubins-spanier.md), item 2. With the
value $1/k$ for the number $k$ of remaining agents, the protocol need not be proportional: with three agents whose valuations are uniform,
the last agent gets value $1/6$.

## Proof

When $k \ge 2$ agents remain, the round asks $k$ cut queries, for $k = n, n-1, \dots, 2$, and the last agent is asked nothing. Each of the
$n - k$ pieces removed before that round is worth at most $1/n$ to every remaining agent, because that agent's mark in the round of the
removal was at or to the right of the least mark. So every remaining agent values the rest of the cake at least $k/n \ge 1/n$, and its cut
query for the value $1/n$ is defined.

## Depends on

- [Cake cutting in the Robertson-Webb query model](cake-cutting-in-the-robertson-webb-query-model.md)
- [Cut-and-choose and Dubins-Spanier](cut-and-choose-and-dubins-spanier.md)

## Sources

- A. D. Procaccia, *Cake cutting algorithms*, in F. Brandt et al. (eds.), *Handbook of Computational Social Choice*, Cambridge University Press, 2016, Chapter 13: Section 13.2, pp. 311–312 (normalization, divisibility, nonnegativity and additivity of valuations), Section 13.3.2, p. 314 (the discrete Dubins-Spanier protocol, with marks at value $1/n$) and Section 13.4, p. 316 (the Robertson-Webb queries, and the simulation of Dubins-Spanier by $\mathrm{cut}_i(x, 1/n)$ queries, $\sum_{k=0}^{n-2} (n - k)$ in total). <https://www.cse.unsw.edu.au/~haziz/comsoc.pdf>
