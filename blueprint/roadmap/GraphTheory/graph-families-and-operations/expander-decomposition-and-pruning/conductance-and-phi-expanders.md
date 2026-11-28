# Cut conductance, phi-expanders and degree-preserving induced subgraphs

Let $G = (V, E)$ be a finite undirected multigraph with $m = |E|$, where each self-loop contributes $1$ to the degree of its vertex. For $S \subseteq V$ let $\mathrm{vol}_G(S) = \sum_{v \in S} \deg_G(v)$ and let $\delta_G(S) = |E_G(S, V \setminus S)|$ be the number of edges with exactly one endpoint in $S$. For $S \subseteq V$ with $\mathrm{vol}_G(S) > 0$ and $\mathrm{vol}_G(V \setminus S) > 0$, so in particular $\emptyset \ne S \subsetneq V$, the *conductance* of the cut $S$ is

$$
\Phi_G(S) = \frac{\delta_G(S)}{\min\{\mathrm{vol}_G(S), \mathrm{vol}_G(V \setminus S)\}},
$$

and the conductance $\Phi_G$ of $G$ is the minimum of $\Phi_G(S)$ over all such cuts, with $\Phi_G = 1$ when there is none (for instance when $|V| = 1$ or $G$ has no edges). Cuts with a side of volume $0$, such as an isolated vertex against the rest, are excluded, as their conductance would be $0/0$. For $\varphi \in (0, 1]$, the graph $G$ is a *$\varphi$-expander* if $\Phi_G \ge \varphi$.

For $S \subseteq V$, $G[S]$ is the induced subgraph, and $G\{S\}$ is obtained from $G[S]$ by attaching $\deg_G(v) - \deg_{G[S]}(v)$ self-loops at every $v \in S$, so that $\deg_{G\{S\}}(v) = \deg_G(v)$. Since adding self-loops only increases volumes, $\Phi_{G[S]} \ge \Phi_{G\{S\}}$. A set $A \subseteq V$ is *nearly $\varphi$-expanding in $G$* if $\delta_G(T) \ge \varphi \cdot \mathrm{vol}_G(T)$ for every $T \subseteq A$ with $\mathrm{vol}_G(T) \le \mathrm{vol}_G(A)/2$ (cut edges leaving $A$ count).

## Depends on

- [Volume of a vertex set](../../algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/volume.md)
- [Weighted degree](../../algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/weighted-degree.md)

## Sources

- Thatchaphol Saranurak, Di Wang, "Expander Decomposition and Pruning: Faster, Stronger, and Simpler", SODA (2019), arXiv:1812.08958.
- Ravi Kannan, Santosh Vempala, Adrian Vetta, "On Clusterings: Good, Bad and Spectral", J. ACM 51(3) (2004).
