# Saranurak-Wang near-linear-time strong expander decomposition

There is a randomized algorithm that, given an undirected graph $G = (V, E)$ with $m$ edges and $\varphi \in (0, 1)$, runs in time $O(m \log^4 m / \varphi)$ and with high probability outputs a partition $V = V_1 \sqcup \dots \sqcup V_k$ such that

$$
\Phi_{G\{V_i\}} \ge \varphi \quad \text{for all } i, \qquad \sum_{i=1}^{k} \delta_G(V_i) = O(\varphi \, m \log^3 m).
$$

That is, $G$ admits a strong $(\varphi, O(\varphi \log^3 m))$-expander decomposition computable in time $\tilde O(m/\varphi)$, which is near-linear whenever $\varphi \ge 1/\log^{O(1)} m$.

## Proof sketch

Apply the cut-matching step to the current piece. In case 1 output it; in case 2 recurse on both sides of the balanced cut, which happens along a recursion of depth $O(\log^3 m)$ since volumes drop by a $1 - \Omega(1/\log^2 m)$ factor; in case 3 trim the nearly expanding large side to an induced $\varphi/6$-expander and recurse only on the small remainder. Running with parameter $6\varphi$ gives the stated guarantee, and the charging argument of the existence proof bounds the crossing edges.

## Depends on

- [(phi, epsilon)-expander decompositions of an undirected graph](phi-epsilon-expander-decomposition.md)
- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](conductance-and-phi-expanders.md)

## Proof depends on

- [Every graph has a phi-expander decomposition with O(phi m log m) crossing edges](existence-of-expander-decompositions.md)
- [Cut-matching step: certify expansion, find a balanced sparse cut, or isolate a nearly expanding side](cut-matching-step-trichotomy.md)
- [Trimming a nearly expanding set into a degree-preserving phi/6-expander](trimming-lemma.md)

## Sources

- Thatchaphol Saranurak, Di Wang, "Expander Decomposition and Pruning: Faster, Stronger, and Simpler", SODA (2019), arXiv:1812.08958.
