# Trimming a nearly expanding set into a degree-preserving phi/6-expander

Let $G = (V, E)$ have $m$ edges, let $\varphi \in (0, 1)$, and let $A \subseteq V$ be nearly $\varphi$-expanding in $G$ with $\delta_G(A) \le \varphi \cdot \mathrm{vol}_G(A)/10$. There is a deterministic algorithm running in time $O(\delta_G(A) \log m / \varphi^2)$ that outputs $A' \subseteq A$ such that

1. $\Phi_{G\{A'\}} \ge \varphi/6$;
2. $\mathrm{vol}_G(A') \ge \mathrm{vol}_G(A) - 4\,\delta_G(A)/\varphi$;
3. $\delta_G(A') \le 2\,\delta_G(A)$.

## Proof sketch

Place $2/\varphi$ units of source mass on each endpoint inside $A$ of an edge leaving $A$, let every vertex $v$ absorb up to $\deg(v)$ units, and route inside $G[A]$ with edge capacities $2/\varphi$ by a bounded-height push-relabel (unit-flow) procedure. Whenever the flow cannot be completed, the level structure exposes a set of low expansion near the boundary, which is removed from $A$ and whose new boundary edges become new sources. Near expansion of $A$ bounds the total removed volume by $4\delta_G(A)/\varphi$, and a completed flow certifies $\Phi_{G\{A'\}} \ge \varphi/6$ because every small set in $A'$ can push its boundary mass out through its own cut edges. The work is local, proportional to the total source mass times the height $O(\log m/\varphi)$.

## Depends on

- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](conductance-and-phi-expanders.md)

## Proof depends on

- [Max-flow min-cut theorem](../../matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)

## Sources

- Thatchaphol Saranurak, Di Wang, "Expander Decomposition and Pruning: Faster, Stronger, and Simpler", SODA (2019), arXiv:1812.08958.
