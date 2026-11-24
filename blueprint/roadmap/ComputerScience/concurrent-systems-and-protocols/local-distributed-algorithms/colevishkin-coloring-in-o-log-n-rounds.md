# Cole–Vishkin coloring in O(log* n) rounds

In the [LOCAL model](../distributed-execution-models/the-local-model.md), consider a directed graph of maximum out-degree $1$, such as a directed cycle or a rooted tree with edges pointing to the parent, whose nodes carry distinct identities in $\{0, \dots, N\}$. A proper $3$-coloring can be computed deterministically in $O(\log^* N)$ synchronous rounds.

1. **Color reduction.** View a color $x$ as a bit string $x_k \cdots x_0$. In each round, every node with color $x$ and successor color $y$ finds the smallest index $i$ with $x_i \ne y_i$ and adopts the new color $2i + x_i$. A node without a successor pretends that its successor differs from it in bit $0$. Adjacent nodes keep distinct colors. If a node and its successor use different indices, the new colors differ in their leading part $i$; if they use the same index $i$, they differ in the last bit, because $y_i \ne x_i$. Colors up to $N$ become colors up to $2\lfloor \lg N\rfloor + 1$. Iterating, after $O(\log^* N)$ rounds only the six colors $0, \dots, 5$ remain.
2. **Six to three colors.** For each $c \in \{3, 4, 5\}$, first shift colors down: each node takes its successor's color, and a node without a successor picks a color in $\{0, 1, 2\}$ other than its current color. Afterwards all predecessors of a node share one color. Then each node of color $c$ picks the smallest color in $\{0, 1, 2\}$ that does not occur among its neighbors. This takes a constant number of extra rounds.

To know when to switch to the second stage, the nodes need an upper bound on $\log^* N$.

## Depends on

- [The LOCAL model](../distributed-execution-models/the-local-model.md)

## Proof depends on

- [A Cole–Vishkin step keeps the coloring proper](../../parallel-algorithms/cole-vishkin-deterministic-coin-tossing/cv-color-proper.md)
- [A Cole–Vishkin step shrinks the palette](../../parallel-algorithms/cole-vishkin-deterministic-coin-tossing/cv-color-lt.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, <https://cs.yale.edu/homes/aspnes/classes/4650/notes.pdf>, Section 33.2.1 (coloring graphs with out-degree 1: the bit-index color reduction, its correctness, the $O(\log^* N)$ bound and the reduction from six to three colors).
- R. Cole and U. Vishkin, "Deterministic coin tossing with applications to optimal parallel list ranking", *Information and Control* 70(1):32–53, 1986.
- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992.
