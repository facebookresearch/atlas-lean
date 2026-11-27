# Asynchronous distributed Bellman–Ford converges

Let $(I, A)$ be a directed graph with nodes $I = \{1, \dots, n\}$, positive arc lengths $a_{ij}$, and a directed path from every node to node $1$; let $N(i)$ be the set of successors of $i$. The shortest distances $x^*_i$ to node $1$ are the unique solution of $x^*_1 = 0$ and $x^*_i = \min_{j \in N(i)}\{a_{ij} + x^*_j\}$ for $i \ne 1$. Run the [totally asynchronous iteration](the-totally-asynchronous-iteration-model.md) with one node per coordinate and $f_1(x) = 0$, $f_i(x) = \min_{j \in N(i)}\{a_{ij} + x_j\}$, each node recomputing its distance from the latest estimates received from its neighbours, and with arbitrary initial estimates $x_1 = 0$, $x_i \in [0, \infty]$. Then every node's estimates converge to the shortest distances $x^*$, whatever the timing of computations and messages, as long as no node stops computing or sending.

The theorem assumes a fixed topology and positive lengths; compare [count-to-infinity in distance-vector routing](../count-to-infinity-in-distance-vector-routing.md), where the topology changes.

## Depends on

- [The totally asynchronous iteration model](the-totally-asynchronous-iteration-model.md)

## Proof depends on

- [Asynchronous iteration of monotone mappings](asynchronous-iteration-of-monotone-mappings.md): $f$ is monotone, with $\underline x = 0$ and $\bar x_i = \infty$ for $i \ne 1$, $\bar x_1 = 0$.

## Sources

- D. P. Bertsekas, "Distributed asynchronous computation of fixed points", *Mathematical Programming* 27:107–120, 1983; <https://web.mit.edu/dimitrib/OldFiles/www/Distr_Comp_Fixed.pdf>, Section 2 (the shortest path problem as a fixed point problem) and Section 4.3 (the shortest path example).
- D. P. Bertsekas, "Distributed dynamic programming", *IEEE Transactions on Automatic Control* 27(3):610–616, 1982, where the asynchronous distributed Bellman–Ford algorithm is first analyzed.
