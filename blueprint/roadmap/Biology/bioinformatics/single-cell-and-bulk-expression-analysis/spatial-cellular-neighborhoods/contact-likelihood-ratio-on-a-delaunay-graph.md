# Contact likelihood ratio on a Delaunay graph

Let the cells of a tissue section be the vertices of the Delaunay triangulation of their planar coordinates, and let each cell carry a type label in $\{1,\dots,T\}$. For types $i,j$ let $N_{ij}$ be the number of edges joining a cell of type $i$ to a cell of type $j$, and set

$$N_{i\cdot} = \sum_{j} N_{ij}, \qquad N_{\cdot j} = \sum_{i} N_{ij}, \qquad N_t = \sum_{i,j} N_{ij}.$$

The contact likelihood ratio and the relative contact frequency of the ordered pair $(i,j)$, defined when $N_{i\cdot} > 0$ and $N_{\cdot j} > 0$ (for $L_{ij}$) and when $N_{i\cdot} > 0$ (for $R_{ij}$), are

$$L_{ij} = \frac{N_{ij}\, N_t}{N_{i\cdot}\, N_{\cdot j}}, \qquad R_{ij} = \frac{N_{ij}}{N_{i\cdot}} .$$

$L_{ij} = 1$ exactly when the observed number of $i$-$j$ edges equals the number expected if edge endpoints were assigned independently with the marginal type frequencies $N_{i\cdot}/N_t$ and $N_{\cdot j}/N_t$; $L_{ij} > 1$ indicates enrichment of direct contact and $L_{ij} < 1$ depletion. A type absent from the section has zero margins and receives no ratio. Comparing two patient groups is done on $\log_2$ of the ratio of their $L_{ij}$ matrices, entrywise where both ratios are defined and positive.

## Depends on

- [Delaunay triangulation](../../../../ComputerScience/computational-geometry/delaunay-triangulations/delaunay-triangulation.md)

## Remarks

The statistic is the pointwise lift of a contingency table: it divides the joint edge frequency $N_{ij}/N_t$ by the product of marginals $(N_{i\cdot}/N_t)(N_{\cdot j}/N_t)$, so it is exactly the ratio of observed to expected counts under independence, and it is invariant to the overall number of edges. Using Delaunay adjacency rather than a distance threshold makes "direct neighbour" a combinatorial property of the point configuration, so the statistic does not require choosing a length scale. The normalization by both margins is what separates genuine preferential contact from mere abundance: a rare cell type that touches a common one often does so only because the partner is common, and that effect is divided out.

## Sources

- Schurch CM, Bhate SS, Barlow GL, et al. Coordinated cellular neighborhoods orchestrate antitumoral immunity at the colorectal cancer invasive front. *Cell* 182:1341-1359 (2020), STAR Methods, formulas for likelihood ratios and relative frequencies. DOI <https://doi.org/10.1016/j.cell.2020.07.005>. PMCID PMC7479520.
