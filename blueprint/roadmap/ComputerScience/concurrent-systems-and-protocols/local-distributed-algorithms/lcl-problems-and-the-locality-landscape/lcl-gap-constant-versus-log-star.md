# No LCL complexities between constant and log-star

For every LCL problem $\Pi$ on bounded-degree graphs, if $D_\Pi(n) = o(\log^* n)$ then $D_\Pi(n) = O(1)$; the same gap holds for randomized complexity. Moreover, an LCL problem solvable in $O(1)$ rounds can be solved in $O(1)$ rounds by an order-invariant algorithm, whose output depends only on the relative order of identifiers in its view.

## Proof sketch

By Ramsey's theorem, an algorithm with locality $t$ restricted to identifiers from a sufficiently large set behaves order-invariantly on some infinite subset of identifiers. An order-invariant algorithm can be run with identifiers replaced by a proper colouring of a sufficiently large power of the graph that respects local orders, which costs $O(\log^* n)$ rounds in general but only $O(1)$ once the locality bound does not grow with $n$; the speedup yields the gap.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [Cole–Vishkin coloring in O(log* n) rounds](../colevishkin-coloring-in-o-log-n-rounds.md)

## Sources

- M. Naor, L. Stockmeyer, "What Can Be Computed Locally?", SIAM Journal on Computing 24(6) (1995); STOC 1993.
