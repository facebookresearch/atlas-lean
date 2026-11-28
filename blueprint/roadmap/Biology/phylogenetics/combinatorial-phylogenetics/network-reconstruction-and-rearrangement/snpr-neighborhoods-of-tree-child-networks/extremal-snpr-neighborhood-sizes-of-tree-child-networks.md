# Extremal SNPR neighborhood sizes of tree-child networks

**Setting.** Networks are rooted binary phylogenetic networks with $n\ge2$ labelled leaves, a root of out-degree one and $r$ reticulations (so $2n+3r-1$ edges); $\mathcal{TC}_n$ is the class of tree-child networks. For an edge $e=(u,v)$ with $u$ not a reticulation and an edge $f$ not below $e$, the **SubNet Prune and Regraft** moves are: SNPR$^0$ (prune $e$ and regraft it to $f$, generalizing rSPR), SNPR$+$ (add an edge from a subdivision of $f$ to a subdivision of $e$) and SNPR$-$ (delete a reticulation edge and suppress its endpoints). The unit tree-child neighborhood $U^{\mathcal{TC}}(N)$ is the set of tree-child networks $N'\ne N$ reachable by one move. For an edge $e$ let $\delta(e)$ be the number of edges below it and $\delta_T(e)$ the number of tree edges below it.

**Proposition.** For $n\ge2$,

$$
n-1\le\min_{N\in\mathcal{TC}_n}|U^{\mathcal{TC}}_{\mathrm{SNPR}}(N)|\le\tfrac32n^2-\tfrac72n+2,\qquad 8n^2-O(n\log_2n)\le\max_{N\in\mathcal{TC}_n}|U^{\mathcal{TC}}_{\mathrm{SNPR}}(N)|<16n^2-38n+26.
$$

The lower bound $n-1$ is attained for $n=2$, $r=1$. The upper bound on the minimum is attained by a chain of $n-1$ triangles, each the child of the one above: it has no SNPR$+$ neighbors (it already has the maximum $n-1$ reticulations), $n-1$ SNPR$-$ neighbors and $\sum_{i=1}^{n-2}3i=\frac32n^2-\frac92n+3$ SNPR$^0$ neighbors. The lower bound on the maximum comes from balanced trees: for $n=2^k$ the balanced tree has $8n^2-24n+20-\sum_{e}\delta(e)-\sum_{e\in E_{PS}}\delta_T(e)$ neighbors, which is $8n^2-O(n\log_2n)$; the balanced tree on $16$ leaves has at least $1518$.

So the minimum neighborhood size can be far below the maximum: at most about $\frac32n^2$ versus at least about $8n^2$, depending strongly on the topology.

## Depends on

- [Unit SNPR neighborhood size of tree-child networks](unit-snpr-neighborhood-size-of-tree-child-networks.md)

## Expansion

Every tree-child network has $2r-t_3$ SNPR$-$ neighbors, and a reticulation edge can be added from the root edge to each pure tree edge that is not the sibling of a reticulation edge, giving at least $2n-t_3-2\ge n-1$ neighbors since $t_3\le n-1$. In the triangle chain the only prunable non-critical edges are the long sides of the triangles, which may only be regrafted to tree edges not below them, half of which give trivial moves. For the maximum, the descendant sums are smallest for balanced shapes, where $\sum_e\delta(e)$ grows like $n\log_2n$, while the quadratic upper bound bounds each term of the exact formula.

## Sources

- Jonathan Klawitter, "The SNPR neighbourhood of tree-child networks", arXiv (2017), Section "Minimal and maximal neighbourhoods" (the proposition bounding minimum and maximum neighbourhood sizes and its proof via triangle chains and balanced trees), <https://doi.org/10.48550/arXiv.1707.09579> Published version: Journal of Graph Algorithms and Applications, vol. 22, no. 2, pp. 329-355 (2018), <https://doi.org/10.7155/jgaa.00472>.
