# Spectral approximation of graphs

Let $V$ be a finite vertex set, and let $G$ and $H$ be finite weighted multigraphs on $V$. Each is given by a finite set
of edges, two endpoint maps from its edges to $V$ and a nonnegative real weight on each edge; parallel edges count
separately, and the two graphs may have different edge sets. Let $L_G$ and $L_H$ be their weighted Laplacians, and let
$\varepsilon \in (0, 1)$. Then $H$ is an $\varepsilon$-*spectral approximation* of $G$ if

$$(1 - \varepsilon)\, x^{\mathsf T} L_G x \le x^{\mathsf T} L_H x \le (1 + \varepsilon)\, x^{\mathsf T} L_G x \qquad \text{for all } x \in \mathbb{R}^V.$$

The error is relative to $G$, the graph that $H$ approximates. If $H$ is an $\varepsilon$-spectral approximation of
$G$, scaling its weights by $1/(1 - \varepsilon)$ gives a graph $H'$ with $L_G \preceq L_{H'} \preceq \kappa L_G$ in the
Loewner order, where $\kappa = (1 + \varepsilon)/(1 - \varepsilon)$: the form in which this topic's
Batson–Spielman–Srivastava results are stated.

## Sources

- D. A. Spielman and N. Srivastava, "Graph sparsification by effective resistances", *SIAM Journal on Computing* 40(6):1913–1926, 2011
