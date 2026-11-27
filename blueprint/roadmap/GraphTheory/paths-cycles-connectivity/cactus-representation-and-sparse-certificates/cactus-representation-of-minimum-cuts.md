# Cactus representations of all minimum cuts

Let $G = (V, E, w)$ be a connected undirected graph with positive weights and edge connectivity $\lambda$. A *cactus representation* of $G$ is a pair $(H, \varphi)$ where $H$ is a cactus with its $\lambda$-weighting and $\varphi : V \to V(H)$ is a map (nodes with empty preimage are allowed) such that

$$
\{\, \varphi^{-1}(X) : X \text{ is a side of a minimum cut of } H \,\} = \{\, S \subseteq V : S \text{ is a side of a global minimum cut of } G \,\}.
$$

More generally, for a terminal set $R \subseteq V$, a *Steiner cactus* represents exactly the partitions $\{S \cap R, R \setminus S\}$ induced by the $R$-Steiner minimum cuts.

## Depends on

- [Weighted cactus graphs with tree edges and cycle edges](weighted-cactus-graph.md)
- [Steiner minimum cuts of a terminal set](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Sources

- Efim A. Dinits, Alexander V. Karzanov, Michael V. Lomonosov, "On the Structure of a System of Minimum Edge Cuts of a Graph", Studies in Discrete Optimization (1976).
- Zhongtian He, Shang-En Huang, Thatchaphol Saranurak, "Cactus Representations in Polylogarithmic Max-flow via Maximal Isolating Mincuts", SODA (2024), doi:10.1137/1.9781611977912.60, arXiv:2311.10706.
