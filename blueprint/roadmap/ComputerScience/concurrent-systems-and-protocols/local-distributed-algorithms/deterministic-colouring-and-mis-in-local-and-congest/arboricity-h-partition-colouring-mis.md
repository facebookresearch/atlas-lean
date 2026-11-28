# Colouring and MIS in graphs of bounded arboricity via H-partitions

Let $G = (V, E)$ be a simple connected graph with $n \ge 2$ vertices (for $n = 1$ the class bound below would be $0$) and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$, and let $a = a(G)$; assume $n$ and $a$ are known to all vertices. For every $\varepsilon$ with $0 < \varepsilon \le 2$ there is a deterministic LOCAL algorithm that computes an H-partition with $\ell \le \lceil (2/\varepsilon) \log n \rceil$ classes ($\log$ to base $2$) and degree bound $A = \lfloor (2 + \varepsilon)\, a \rfloor$ in $\ell = O(\log n / \varepsilon)$ rounds. Consequently, deterministically: an $(A+1)$-colouring, hence an $O(a)$-colouring, can be computed in $O(a \log n)$ rounds; for every $1 \le t \le a$, an $O(a t)$-colouring in $O((a/t) \log n + a \log a)$ rounds; and an $O(a^2)$-colouring in $O(\log n)$ rounds. A maximal independent set can be computed in $o(\log n)$ rounds when $a = o(\sqrt{\log n})$, in $O(\log n / \log\log n)$ rounds when $a = O(\log^{1/2 - \delta} n)$ for a constant $0 < \delta < 1/2$, and in $O(a \sqrt{\log n} + a \log a)$ rounds when $a = \Omega(\sqrt{\log n})$. In particular, planar graphs ($a \le 3$) admit deterministic $O(\log n)$-round colouring with $O(1)$ colours and $O(\log n / \log\log n)$-round MIS.

## Proof sketch

In each round, all remaining vertices with at most $(2 + \varepsilon) a$ remaining neighbours join the next class and are removed. Every subgraph has average degree below $2a$, so at least a $\varepsilon/(2+\varepsilon)$ fraction of the remaining vertices qualifies, and $\log_{(2+\varepsilon)/2} n \le (2/\varepsilon) \log n$ classes suffice for $0 < \varepsilon \le 2$. Orienting each edge towards the higher class (by identifier within a class) gives an acyclic orientation with out-degree at most $A$ and hence a decomposition into $A$ forests. For the $O(a)$-colouring, colour each class with $A + 1$ colours by a degree-based algorithm and recolour the classes from the last to the first, one colour class per round, each vertex avoiding its at most $A$ already recoloured neighbours in later classes; the trade-off recolours $t$ colour classes per round with disjoint palettes. The $O(a^2)$-colouring runs Linial's colour reduction in which each vertex only avoids its parents in the $A$ forests. MIS follows from these colourings by the standard reduction that adds one colour class per round.

## Depends on

- [Arboricity and H-partitions](arboricity-and-h-partitions.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds](linial-colour-reduction.md)

## Sources

- L. Barenboim, M. Elkin, "Sublogarithmic distributed MIS algorithm for sparse graphs using Nash-Williams decomposition", Distributed Computing 22 (2010); PODC 2008, Lemmas 3.1–3.4, Theorems 3.5, 4.4, 5.1, 5.5, 6.2 and 6.3.
