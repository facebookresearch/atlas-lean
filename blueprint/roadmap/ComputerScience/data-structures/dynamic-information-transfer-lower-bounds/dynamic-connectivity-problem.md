# Dynamic graph connectivity

The *dynamic connectivity problem* maintains an undirected graph on a fixed vertex set $[n]$, initially without edges, under $\mathrm{insert}(u, v)$, $\mathrm{delete}(u, v)$ and $\mathrm{connected}(u, v)$, which reports whether $u$ and $v$ lie in the same connected component. Restricted versions require the graph to remain a forest, or a disjoint union of paths, at all times.

## Depends on

- [Dynamic graph problems](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
