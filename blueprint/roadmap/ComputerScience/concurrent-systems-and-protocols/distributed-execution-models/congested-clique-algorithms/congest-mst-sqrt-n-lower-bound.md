# MST and verification require $\tilde\Omega(\sqrt{n} + D)$ rounds in CONGEST

In the CONGEST model with $O(\log n)$-bit messages on $n$-vertex networks of diameter $D$, there are networks with $D = O(\log n)$ on which the following lower bounds of $\Omega\bigl(\sqrt{n}/\log n + D\bigr)$ rounds hold. (i) Every Monte Carlo randomized algorithm with sufficiently small constant error that verifies whether a given subgraph is a spanning connected subgraph, or whether a given edge set is a cut, needs this many rounds. (ii) For every polynomially bounded approximation ratio $\alpha(n) \ge 1$, every such randomized algorithm that outputs a spanning tree of weight at most $\alpha$ times the minimum (in particular, every algorithm computing a minimum spanning tree) needs this many rounds. (iii) Every deterministic algorithm that verifies whether a given subgraph is a spanning tree needs this many rounds; for spanning-tree verification the bound is proved only for deterministic algorithms. These bounds are tight up to polylogarithmic factors, since MST and almost all of these verification problems can be solved in $\tilde O(\sqrt n + D)$ rounds, while in the congested clique MST takes $O(1)$ rounds.

## Proof sketch

Build a network of $\sqrt n$ long paths of length $\sqrt n$ joined by a shallow tree, so the diameter is small but any short route between the two ends of the paths passes through few tree edges. A simulation argument shows that a fast distributed algorithm would yield a two-party communication protocol for a function on $\sqrt n$ bits with $o(\sqrt n)$ communication. For the randomized bounds (i) and (ii) the function is set disjointness, contradicting its $\Omega(\sqrt n)$ randomized communication lower bound; spanning connected subgraph and cut verification embed disjointness through subgraph membership on the paths, and approximate MST reduces to spanning connected subgraph verification by giving the subgraph's edges weight $1$ and the other edges weight $n\,\alpha(n)$, so a spanning tree of weight below $n\,\alpha(n)$ exists exactly when the subgraph is spanning and connected. For the deterministic bound (iii) the function is equality, whose deterministic communication complexity is linear; this reduction gives no randomized bound, since equality has cheap randomized protocols.

## Depends on

- [The CONGEST model of distributed computing](../../local-distributed-algorithms/deterministic-network-decomposition/the-congest-model.md)
- [The congested clique model](the-congested-clique-model.md)

## Proof depends on

- [Randomized communication complexity of disjointness](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-disj-fn-ge.md)
- [Deterministic communication complexity of equality](../../../../TheoryOfComputation/communication-complexity/deterministic-communication-protocols/comm-complexity-eq-fn.md)

## Sources

- A. Das Sarma, S. Holzer, L. Kor, A. Korman, D. Nanongkai, G. Pandurangan, D. Peleg, R. Wattenhofer, "Distributed Verification and Hardness of Distributed Approximation", STOC 2011; SIAM Journal on Computing 41(5) (2012), arXiv:1011.3049, Sections 1.3, 5, 6 and 7 (Theorems 6.1 and 7.1).
- D. Peleg, V. Rubinovich, "A Near-Tight Lower Bound on the Time Complexity of Distributed Minimum-Weight Spanning Tree Construction", SIAM Journal on Computing 30(5) (2000).
