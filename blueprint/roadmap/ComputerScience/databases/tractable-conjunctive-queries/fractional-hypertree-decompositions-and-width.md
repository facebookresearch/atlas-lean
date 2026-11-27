# Fractional hypertree decompositions and width

Let $H$ be a finite hypergraph with nonempty edges in which every vertex lies in some edge, as for the
hypergraph of a CSP instance. For $\gamma : E(H) \to [0, \infty)$ let $B(\gamma) = \{v \in V(H) : \sum_{e \ni v} \gamma(e) \ge 1\}$ and
$\mathrm{weight}(\gamma) = \sum_e \gamma(e)$. A *fractional hypertree decomposition* of $H$ is a triple
$(T, (B_t)_{t \in V(T)}, (\gamma_t)_{t \in V(T)})$ where $(T, (B_t))$ is a tree decomposition of $H$ and each $\gamma_t$ is a
map $E(H) \to [0, \infty)$ with $B_t \subseteq B(\gamma_t)$. Its width is $\max_t \mathrm{weight}(\gamma_t)$, and the
*fractional hypertree width* $\mathrm{fhw}(H)$ is the minimum width over all fractional hypertree decompositions;
equivalently $\mathrm{fhw}(H) \le r$ when some tree decomposition has $\rho^*(B_t) \le r$ for every bag. The minimum exists and
is rational, and

$$\mathrm{fhw}(H) \le \rho^*(H) \quad\text{and}\quad \mathrm{fhw}(H) \le \mathrm{ghw}(H).$$

There are families of hypergraphs of bounded fractional hypertree width whose fractional edge cover number and generalized
hypertree width are both unbounded. The fractional hypertree width of a conjunctive query or CSP instance is that of its
hypergraph.

## Depends on

- [Tree-decomposition](../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)
- [Natural join queries, their hypergraphs and fractional edge covers](../join-processing/natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)
- [Generalized hypertree decompositions and width](generalized-hypertree-decompositions-and-width.md)
- [Constraint satisfaction instances and their hypergraphs](constraint-satisfaction-instances-and-their-hypergraphs.md)

## Sources

- M. Grohe and D. Marx, "Constraint solving via fractional edge covers", *ACM Trans. Algorithms* 11(1) (2014) 4; arXiv:1711.04506 <https://arxiv.org/abs/1711.04506>, Definition 4.3, the remarks following it and Examples 4.1 and 4.2.
