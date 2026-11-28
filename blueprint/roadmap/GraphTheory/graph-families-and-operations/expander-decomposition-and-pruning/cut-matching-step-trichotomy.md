# Cut-matching step: certify expansion, find a balanced sparse cut, or isolate a nearly expanding side

There is a constant $c_0 > 0$ and a randomized algorithm that, given an undirected graph $G = (V, E)$ with $m$ edges and $\varphi \in (0, 1)$, runs in time $O((m \log m)/\varphi)$ and with high probability ends in one of the following three cases:

1. it certifies $\Phi_G \ge \varphi$;
2. it returns a cut $A$ with $\Phi_G(A) = O(\varphi \log^2 m)$ and $\mathrm{vol}_G(A), \mathrm{vol}_G(V \setminus A) = \Omega(m / \log^2 m)$;
3. it returns a cut $A$ with $\Phi_G(A) \le c_0 \varphi \log^2 m$ and $\mathrm{vol}_G(A) \le m/(10 c_0 \log^2 m)$, such that $V \setminus A$ is nearly $\varphi$-expanding in $G$.

## Proof sketch

Run the cut-matching game for $O(\log^2 m)$ rounds, routing each round's matching by a bounded-height local flow with capacities $1/\varphi$ per edge. Rounds whose flow fails produce sparse cuts that are accumulated; if their total volume becomes large, the accumulated set is a balanced sparse cut (case 2). Otherwise the matching player's matchings embed an expander into $G$ with congestion $O(\log^2 m / \varphi)$ on the vertices outside the small accumulated set, which certifies near expansion of the large side (case 3), or of all of $G$ when nothing was cut (case 1).

## Depends on

- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](conductance-and-phi-expanders.md)

## Proof depends on

- [The Khandekar-Rao-Vazirani cut-matching game](krv-cut-matching-game.md)
- [Random-projection cut strategies win the cut-matching game in O(log^2 n) rounds](krv-cut-strategy-theorem.md)

## Sources

- Thatchaphol Saranurak, Di Wang, "Expander Decomposition and Pruning: Faster, Stronger, and Simpler", SODA (2019), arXiv:1812.08958.
- Rohit Khandekar, Satish Rao, Umesh Vazirani, "Graph Partitioning using Single Commodity Flows", STOC (2006); J. ACM 56(4) (2009).
