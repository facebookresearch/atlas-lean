# Every graph has a phi-expander decomposition with O(phi m log m) crossing edges

For every undirected multigraph $G = (V, E)$ with $m \ge 2$ edges and every $\varphi \in (0, 1)$ there is a partition $V = V_1 \sqcup \dots \sqcup V_k$ with $\Phi_{G[V_i]} \ge \varphi$ for all $i$ and

$$
\sum_{i=1}^{k} \delta_G(V_i) = O(\varphi \, m \log m).
$$

Equivalently, $G$ has a $(\varphi, \varepsilon)$-expander decomposition with $\varepsilon = O(\varphi \log m)$.

## Proof sketch

Recursively: if the current piece $H$ has $\Phi_H \ge \varphi$, output it; otherwise cut along a set $S$ with $\Phi_H(S) < \varphi$, taking $S$ to be the side of smaller volume, and recurse on both sides. Charge the at most $\varphi \cdot \mathrm{vol}_H(S)$ cut edges to the edge endpoints on the smaller side. An endpoint lies on the smaller side at most $O(\log m)$ times, since the volume of its piece halves each time, so the total charge is $O(\varphi m \log m)$.

## Depends on

- [(phi, epsilon)-expander decompositions of an undirected graph](phi-epsilon-expander-decomposition.md)
- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](conductance-and-phi-expanders.md)

## Sources

- Thatchaphol Saranurak, Di Wang, "Expander Decomposition and Pruning: Faster, Stronger, and Simpler", SODA (2019), arXiv:1812.08958.
- Ravi Kannan, Santosh Vempala, Adrian Vetta, "On Clusterings: Good, Bad and Spectral", J. ACM 51(3) (2004).
