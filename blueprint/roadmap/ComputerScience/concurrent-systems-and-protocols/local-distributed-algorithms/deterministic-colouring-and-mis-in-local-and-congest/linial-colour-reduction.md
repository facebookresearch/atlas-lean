# Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic LOCAL algorithm, which also runs in CONGEST, that computes a proper colouring of $G$ with $O(\Delta^2)$ colours in $\log^* n + O(1)$ rounds. Each round reduces a proper $k$-colouring to a proper $O(\Delta^2 \log k)$-colouring.

## Proof sketch

Associate to each colour $c \in \{1, \dots, k\}$ a set $S_c \subseteq \{1, \dots, q\}$ from a family of $k$ sets such that no set is covered by the union of any $\Delta$ others; such $\Delta$-cover-free families exist with $q = O(\Delta^2 \log k)$ by the probabilistic method. A vertex of colour $c$ picks a new colour in $S_c$ not contained in the sets of its at most $\Delta$ neighbours. The recurrence $k \mapsto O(\Delta^2 \log k)$ alone does not reach $O(\Delta^2)$ colours: after $\log^* n + O(1)$ iterations it stalls at $O(\Delta^2 \log \Delta)$ colours, which is at most $\Delta^3$ for large $\Delta$ (for bounded $\Delta$ the bound is $O(1) = O(\Delta^2)$ already). One final round uses the polynomial size of this palette in $\Delta$: fix a prime $p$ with $2\Delta < p = O(\Delta)$, identify each of the at most $p^3$ colours with a distinct polynomial $f_c$ of degree at most $2$ over $\mathbb{F}_p$, and let $S_c = \{(x, f_c(x)) : x \in \mathbb{F}_p\}$. Two distinct such polynomials agree in at most $2$ points, so $\Delta$ neighbours cover at most $2\Delta < p$ elements of $S_c$, and the vertex picks an uncovered pair; the new palette $\mathbb{F}_p \times \mathbb{F}_p$ has $O(\Delta^2)$ colours.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [The CONGEST model of distributed computing](../deterministic-network-decomposition/the-congest-model.md)

## Sources

- N. Linial, "Locality in Distributed Graph Algorithms", SIAM Journal on Computing 21(1) (1992).
