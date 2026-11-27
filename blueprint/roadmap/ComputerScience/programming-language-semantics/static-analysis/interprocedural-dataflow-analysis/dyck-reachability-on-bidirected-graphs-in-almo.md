# Dyck reachability on bidirected graphs in almost-linear time

Let $k$ be fixed and let $G$ be a bidirected $\Sigma_k$-labeled graph, in the sense of [Dyck reachability](dyck-reachability.md), with $n$ nodes and $m \ge n$ edges. The partition of the nodes into maximal Dyck SCCs, which represents the set of all Dyck-reachable pairs without enumerating it, can be computed in time $O(m + n \cdot \alpha(n))$ and space $O(m)$, where $\alpha$ is the inverse Ackermann function. The algorithm first merges the two endpoints of every $\epsilon$-labeled edge, in linear time. Next, in a linear-time pass, wherever a node has two outgoing edges with the same closing parenthesis it merges their targets and keeps one edge, leaving $O(n)$ edges. It then repeatedly merges, with a disjoint-set structure, the targets of two edges labeled with the same closing parenthesis that leave one current class. Without the first step two nodes joined by opposite $\epsilon$-edges, which form one Dyck SCC, would stay apart, since no closing-parenthesis edge leaves them.

## Depends on

- [Dyck reachability](dyck-reachability.md)

## Proof depends on

- [Dyck reachability on bidirected graphs is symmetric](dyck-reachability-on-bidirected-graphs-is-symm.md)

## Sources

- K. Chatterjee, B. Choudhary and A. Pavlogiannis, "Optimal Dyck reachability for data-dependence and alias analysis", *Proceedings of the ACM on Programming Languages* 2(POPL):30, 2018, <https://arxiv.org/abs/1910.00241>, Section 3.1, Remarks 1 and 2 (the Dyck SCCs as output, and the linear-time merging of the endpoints of $\epsilon$-labeled edges); Section 3.2: the algorithm BidirectedReach, the speedup for non-sparse graphs, Lemmas 3.1 and 3.2 (soundness and completeness), Lemmas 3.3–3.5 (complexity) and Theorem 3.6.
