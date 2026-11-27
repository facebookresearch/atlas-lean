# The multiphase conjecture implies polynomial dynamic lower bounds

Let $N$ be the number of bits needed to describe the current state of a dynamic problem. If the multiphase conjecture holds, then for each of dynamic reachability in directed graphs, dynamic shortest paths in undirected graphs, subgraph connectivity, Langerman's zero-partial-sum problem, Pagh's set-intersection problem and Erickson's row/column-increment maximum problem there is a constant $\varepsilon > 0$ such that the problem cannot be solved in the word-RAM model with $o(N^{\varepsilon})$ time per operation and $o(N^{1+\varepsilon})$ preprocessing time (Pătraşcu, Theorem 2). Moreover, under the 3SUM conjecture (Pătraşcu, Conjecture 6: in the word-RAM model with $O(\lg n)$-bit words, every zero-error randomized algorithm that decides whether a set $S \subseteq \{-n^3, \dots, n^3\}$ of $|S| = n$ integers contains distinct $x, y, z \in S$ with $x + y = z$ needs $n^{2 - o(1)}$ expected time), the multiphase problem with $k = \Theta(n^{2.5})$ requires $\tau \ge n^{0.5 - o(1)}$ (Pătraşcu, Theorem 3), so the multiphase conjecture holds with $\gamma = 2.5$ and any $\delta < 1/2$.

## Proof sketch

Each reduction encodes $S_1, \dots, S_k$ in the Phase I preprocessing, applies $O(n)$ updates encoding $T$ in Phase II, and in Phase III applies $O(1)$ updates and one query whose answer says whether $S_i \cap T \neq \emptyset$. For Erickson's problem: preprocess the $k \times n$ incidence matrix of the $S_i$, increment column $j$ for each $j \in T$, then increment row $i$ and ask whether the maximum is $3$. With $O((nk)^{1+\varepsilon})$ preprocessing and $O((nk)^{\varepsilon})$ per operation this gives $\tau = (nk)^{\varepsilon}$, contradicting the conjecture once $(\gamma + 1)\varepsilon < \delta$. For 3SUM, Pătraşcu reduces 3SUM to Convolution-3SUM using Dietzfelbinger's almost-linear multiplicative hashing, Convolution-3SUM to listing triangles in a structured graph, and triangle listing to the multiphase problem.

## Depends on

- [Multiphase conjecture](multiphase-conjecture.md)
- [Pătraşcu's multiphase problem](multiphase-problem.md)
- [Dynamic graph problems](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)

## Sources

- Mihai Pătraşcu, "Towards Polynomial Lower Bounds for Dynamic Problems", STOC (2010).
