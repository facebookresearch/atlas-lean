# MST and verification require roughly sqrt(n) + D rounds in CONGEST

In the CONGEST model on $n$-vertex networks of diameter $D$, computing a minimum spanning tree requires $\Omega\bigl(\sqrt{n}/\log n + D\bigr)$ rounds for some networks even when $D = O(\log n)$, and the same lower bound (up to polylogarithmic factors) holds for randomized algorithms and for many verification problems such as checking whether a given subgraph is a spanning tree, connected, or a cut, and for $\alpha$-approximating MST weight for any polynomially bounded $\alpha$. These bounds are tight up to polylogarithmic factors, since MST can be computed in $\tilde O(\sqrt n + D)$ rounds, while in the congested clique MST takes $O(1)$ rounds.

## Proof sketch

Build a network of $\sqrt n$ long paths of length $\sqrt n$ joined by a shallow tree, so the diameter is small but any short route between the two ends of the paths passes through few tree edges. A simulation argument shows that a fast distributed algorithm would yield a two-party communication protocol for set disjointness on $\sqrt n$ bits with $o(\sqrt n)$ communication, contradicting the $\Omega(\sqrt n)$ randomized communication lower bound; MST and verification problems embed disjointness through edge weights or subgraph membership on the paths.

## Depends on

- [The CONGEST model of distributed computing](../../local-distributed-algorithms/deterministic-network-decomposition/the-congest-model.md)
- [The congested clique model](the-congested-clique-model.md)

## Proof depends on

- [Randomized communication complexity of disjointness](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-disj-fn-ge.md)

## Sources

- A. Das Sarma, S. Holzer, L. Kor, A. Korman, D. Nanongkai, G. Pandurangan, D. Peleg, R. Wattenhofer, "Distributed Verification and Hardness of Distributed Approximation", STOC 2011; SIAM Journal on Computing 41(5) (2012), arXiv:1011.3049.
- D. Peleg, V. Rubinovich, "A Near-Tight Lower Bound on the Time Complexity of Distributed Minimum-Weight Spanning Tree Construction", SIAM Journal on Computing 30(5) (2000).
