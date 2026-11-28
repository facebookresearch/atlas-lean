# Round complexity of 3-colouring and MIS on oriented cycles

Consider deterministic LOCAL algorithms on oriented $n$-cycles whose nodes carry distinct identifiers from $\{1, \dots, n\}$. Every $T$-round 3-colouring algorithm satisfies $T \ge \tfrac12 \log^* n - 1$ (Laurinharju and Suomela, inequality (1); Linial, Theorem 2.1, gives $\tfrac12(\log^* n - 3)$ with his convention for $\log^*$), and every $T$-round maximal independent set algorithm satisfies $T \ge \tfrac12(\log^* n - 1)$ (Linial, Theorem 2.1, with his convention for $\log^*$; both bounds hold even with a common orientation). Conversely, the Cole–Vishkin algorithm finds a maximal independent set of the $n$-cycle in $O(\log^* n)$ rounds, and a maximal independent set yields a 3-colouring in one more round (Linial, §1 and the proof of Theorem 2.1). Hence both problems have deterministic round complexity $\Theta(\log^* n)$.

## Proof sketch

An MIS gives a 3-colouring in one round (members, successors of members, others), and a $k$-colouring gives an MIS by greedily adding colour classes. For the lower bound, a $T$-round 3-colouring algorithm is a $(2T + 1)$-ary 3-colouring function on increasing identifier sequences, and each removal of an argument at most exponentiates the number of colours, so $2T + 2 \ge \log^* n$. A derived count, not stated in the cited sources, sharpens the upper bounds: performing two Cole–Vishkin reductions per round 3-colours the cycle in $\lceil \log^* n / 2 \rceil + 3$ rounds, within $4$ of the lower bound, and an MIS follows within $\lceil \log^* n / 2 \rceil + 5$ rounds.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Cole–Vishkin coloring in O(log* n) rounds](../colevishkin-coloring-in-o-log-n-rounds.md)
- [Linial's lower bound for coloring a ring](../linial-s-lower-bound-for-coloring-a-ring.md)

## Sources

- Richard Cole and Uzi Vishkin, "Deterministic Coin Tossing with Applications to Optimal Parallel List Ranking", Information and Control, 1986.
- Nathan Linial, "Locality in Distributed Graph Algorithms", SIAM Journal on Computing 21(1), 1992, §1 and Theorem 2.1.
- Juhana Laurinharju and Jukka Suomela, "Brief Announcement: Linial's Lower Bound Made Easy", Proceedings of the 2014 ACM Symposium on Principles of Distributed Computing (PODC), 2014, inequality (1).
