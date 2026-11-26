# Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic LOCAL algorithm, which also runs in CONGEST, that computes a proper colouring of $G$ with $O(\Delta^2)$ colours in $\log^* n + O(1)$ rounds. Each round reduces a proper $k$-colouring to a proper $O(\Delta^2 \log k)$-colouring.

## Proof sketch

Associate to each colour $c \in \{1, \dots, k\}$ a set $S_c \subseteq \{1, \dots, q\}$ from a family of $k$ sets such that no set is covered by the union of any $\Delta$ others; such $\Delta$-cover-free families exist with $q = O(\Delta^2 \log k)$ by the probabilistic method, or explicitly via polynomials over finite fields with $q = O(\Delta^2 \log^2 k)$. A vertex of colour $c$ picks a new colour in $S_c$ not contained in the sets of its at most $\Delta$ neighbours. Iterating $\log^* n$ times reduces $k$ from $\mathrm{poly}(n)$ to $O(\Delta^2)$.

## Depends on

- [Degree-plus-one list colouring instance](degree-plus-one-list-colouring.md)
- [Linial's lower bound for coloring a ring](../linial-s-lower-bound-for-coloring-a-ring.md)

## Proof depends on

- [Cole–Vishkin coloring in O(log* n) rounds](../colevishkin-coloring-in-o-log-n-rounds.md)

## Sources

- N. Linial, "Locality in Distributed Graph Algorithms", SIAM Journal on Computing 21(1) (1992).
