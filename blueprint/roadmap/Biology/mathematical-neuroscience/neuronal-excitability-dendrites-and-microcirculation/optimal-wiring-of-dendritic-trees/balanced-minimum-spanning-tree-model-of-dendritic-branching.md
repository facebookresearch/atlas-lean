# Balanced minimum spanning tree model of dendritic branching

**Setting.** Let $r \in \mathbb{R}^d$ be a root (the soma) and $P = \{p_1, \dots, p_m\} \subset \mathbb{R}^d \setminus \{r\}$ a finite set of distinct carrier points (target locations drawn from the density profile of the neuron's spanning field). Fix a balancing factor $\mathrm{bf} \ge 0$. The *balanced greedy tree* is built as follows. Start with the tree $T_0$ whose only node is $r$, with path length $\mathrm{PL}(r) = 0$. At step $j$, for every unconnected point $p$ and every tree node $v$ define

$$c(p, v) = \|p - v\| + \mathrm{bf}\cdot\bigl(\mathrm{PL}(v) + \|p - v\|\bigr),$$

the wiring cost of the new segment plus $\mathrm{bf}$ times the path length from the root to $p$ through $v$. Choose a pair $(p, v)$ minimizing $c$, add the edge $v \to p$, set $\mathrm{PL}(p) = \mathrm{PL}(v) + \|p - v\|$, and repeat until all points are connected. The result is a tree rooted at $r$, directed away from the root.

**Proposition.**

1. ($\mathrm{bf} = 0$) The procedure is Prim's algorithm on the complete Euclidean graph on $\{r\} \cup P$, so its output is a Euclidean minimum spanning tree: it minimizes total cable length $\sum_{\text{edges}} \|p - v\|$ among all trees spanning $\{r\} \cup P$.
2. (Path lengths are bounded below by distances) In every output tree, $\mathrm{PL}(p) \ge \|p - r\|$ for all $p$, with equality for all $p$ exactly when every root-to-point path is straight.
3. (Large $\mathrm{bf}$: stellate limit) Suppose no carrier point lies on a segment $[r, q]$ with $q \in P$ another carrier point. Then there is $\mathrm{bf}_0 < \infty$ such that for every $\mathrm{bf} > \mathrm{bf}_0$ the output is the star in which every $p \in P$ is joined directly to $r$; it minimizes $\sum_p \mathrm{PL}(p)$.

So $\mathrm{bf}$ trades total wiring (minimal at $\mathrm{bf} = 0$) against conduction distance to the root (minimal for large $\mathrm{bf}$).

## Proof depends on

- [Prim's tree is a minimum spanning tree](../../../../ComputerScience/approximation-algorithms/double-tree-approximation-for-metric-tsp/prim-tree-is-minimum-spanning-tree.md)

## Expansion

(1): with $\mathrm{bf} = 0$ the selected pair minimizes $\|p - v\|$ over unconnected $p$ and connected $v$, which is exactly Prim's rule started at $r$. Numbering the points of $\{r\} \cup P$ and taking the costs $d(u, v) = \tfrac12\|u - v\|$ makes the edge weight $d(u, v) + d(v, u) = \|u - v\|$ of [Prim's tree is a minimum spanning tree](../../../../ComputerScience/approximation-algorithms/double-tree-approximation-for-metric-tsp/prim-tree-is-minimum-spanning-tree.md) exactly the Euclidean edge length, so that result gives minimality of total cable length. (2) is the triangle inequality applied along the path. (3): while every connected node is joined to $r$, $\mathrm{PL}(v) = \|v - r\|$; for $v \neq r$ the general-position hypothesis gives a uniform gap $\eta = \min_{p \ne v} (\|p - v\| + \|v - r\| - \|p - r\|) > 0$ over the finite set. With $D = \max_{p, v} \|p - v\|$,

$$c(p, v) - c(p, r) = (1 + \mathrm{bf})(\|p - v\| - \|p - r\|) + \mathrm{bf}\,\|v - r\| \ge \mathrm{bf}\,\eta - D,$$

which is positive once $\mathrm{bf} > D/\eta$, so by induction every point attaches to the root. For neurons the authors chose $\mathrm{bf}$ by matching total cable length, mean path length and number of branch points of reconstructed cells (about $0.4$ for fly interneurons, $0.6$ for starburst amacrine cells, $0.4$–$0.7$ for cortical pyramidal dendrites); higher $\mathrm{bf}$ yields more stellate trees with stronger electrotonic segregation of sub-trees, which is how a single wiring parameter controls a computational property. The shape itself is set mainly by the density of carrier points, with extra weak constraints (suppressed multifurcations, spatial jitter) for particular cell types.

## Sources

- H. Cuntz, F. Forstner, A. Borst, M. Häusser, "One rule to grow them all: a general theory of neuronal branching and its practical application", PLoS Computational Biology 6 (2010) e1000877, Results, "Optimized graphs for implementing Cajal's laws" (Fig. 2) and Methods, "Extended minimum spanning tree", <https://doi.org/10.1371/journal.pcbi.1000877> (PMC2916857).
- R. C. Prim, "Shortest connection networks and some generalizations", Bell System Technical Journal 36 (1957) 1389–1401, <https://doi.org/10.1002/j.1538-7305.1957.tb01515.x>.
