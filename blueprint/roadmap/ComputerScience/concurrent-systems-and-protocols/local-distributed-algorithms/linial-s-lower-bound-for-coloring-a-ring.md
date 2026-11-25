# Linial's lower bound for coloring a ring

In the [LOCAL model](../distributed-execution-models/the-local-model.md), consider directed rings of $n$ nodes with distinct identities from $\{1, \dots, n\}$.

1. Every deterministic distributed algorithm that colors every such ring with at most $3$ colors needs at least $(\log^* n)/2 - 1$ rounds.
2. Every deterministic distributed algorithm that computes a maximal independent set of every such ring needs at least $(\log^* n)/2 - O(1)$ rounds.

**Proof idea.** A deterministic $r$-round algorithm may be put in canonical form: every node first collects its $r$-neighborhood and then computes its output from it. On a directed ring the output of a node is then a function of the $2r + 1$ identities around it, and the coloring property says that this function properly colors the graph $B_{2r+1}$. The nodes of $B_k$ are the increasing $k$-tuples of identities, with an edge between $(x_1, \dots, x_k)$ and $(x_2, \dots, x_{k+1})$. Here $\chi(B_1) = n$, and $\chi(B_k) \ge \log^{(k-1)} n$ for $n \ge k \ge 2$, by a lemma relating the chromatic numbers of consecutive $B_k$. So $\chi(B_{2r+1}) > 3$ whenever $r < (\log^* n)/2 - 1$. A maximal independent set of a ring yields a $3$-coloring in a constant number of further rounds, which gives part 2.

The bound matches, up to constants, the $O(\log^* n)$ upper bound of [Cole–Vishkin coloring](colevishkin-coloring-in-o-log-n-rounds.md).

## Depends on

- [The LOCAL model](../distributed-execution-models/the-local-model.md)

## Sources

- R. Wattenhofer, *Principles of Distributed Computing*, lecture notes, ETH Zürich, 2023, Chapter 5, "Locality Lower Bounds", <https://disco.ethz.ch/courses/fs23/podc/lecturenotes/chapter5.pdf>: Algorithm 5.1 and Lemma 5.2 (canonical form), Lemma 5.14 (chromatic number of $B_k$), Theorem 5.15 and Corollary 5.16.
- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992, <https://courses.csail.mit.edu/6.852/08/papers/Linial.pdf>, Theorem 2.1.
