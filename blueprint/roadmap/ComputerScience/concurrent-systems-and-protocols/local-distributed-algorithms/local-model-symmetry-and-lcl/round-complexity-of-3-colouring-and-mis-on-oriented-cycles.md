# Round complexity of 3-colouring and MIS on oriented cycles

Deterministic LOCAL algorithms 3-colour oriented $n$-cycles with identifiers $\{0, \dots, n-1\}$ in $\lceil \log^* n / 2 \rceil + 3$ rounds, and every $t$-round 3-colouring algorithm satisfies $\log^* n \le 2t + 2$; the upper and lower bounds on the optimal number of rounds differ by at most $4$. A maximal independent set is computable within $\lceil \log^* n / 2 \rceil + 5$ rounds, and MIS and 3-colouring reduce to each other in a constant number of rounds, so MIS also has round complexity $\Theta(\log^* n)$.

## Proof sketch

Performing two Cole–Vishkin reductions per round halves the iteration count. An MIS gives a 3-colouring in one round (members, successors of members, others), and a $k$-colouring gives an MIS by greedily adding colour classes. Linial's bound in the Laurinharju–Suomela form gives the lower bound.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Cole–Vishkin coloring in O(log* n) rounds](../colevishkin-coloring-in-o-log-n-rounds.md)
- [Linial's lower bound for coloring a ring](../linial-s-lower-bound-for-coloring-a-ring.md)

## Sources

- Richard Cole and Uzi Vishkin, "Deterministic Coin Tossing with Applications to Optimal Parallel List Ranking", Information and Control, 1986.
- Nathan Linial, "Locality in Distributed Graph Algorithms", SIAM Journal on Computing, 1992.
- Juhana Laurinharju and Jukka Suomela, "Brief Announcement: Linial's Lower Bound Made Easy", Proceedings of the 2014 ACM Symposium on Principles of Distributed Computing (PODC), 2014.
