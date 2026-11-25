# The k-server problem

An instance of the $k$-server problem consists of a metric space $(M, d)$, initial positions $s_1, \dots, s_k \in M$ of $k$ servers, and a sequence of requests $r_1, \dots, r_T \in M$ revealed one at a time. Each request must be served, before the next is revealed, by moving some server to the requested point; the cost is the total distance moved. A configuration is a multiset of $k$ points, and the offline optimum is the cheapest sequence of configurations $C_0 = \{s_1, \dots, s_k\}, C_1, \dots, C_T$ with $r_t \in C_t$, where moving between configurations costs the minimum-cost matching distance.

## Expansion

This page becomes ready once these prerequisites are stated:

- Online algorithms as causal request-answer strategies (statement prerequisite; not yet stated)
- The statement must be checked against the cited sources, which have not been opened

## Sources

- M. S. Manasse, L. A. McGeoch and D. D. Sleator, "Competitive algorithms for server problems", *Journal of Algorithms* 11(2):208–230, 1990
- E. Koutsoupias and C. H. Papadimitriou, "On the k-server conjecture", *Journal of the ACM* 42(5):971–983, 1995
