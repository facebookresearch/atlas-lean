# Neighbourhood composition vector and cellular neighbourhoods

Let a tissue section be represented by cells $i = 1,\dots,n$ with planar coordinates $x_i \in \mathbb{R}^2$ and cell-type labels $c_i \in \{1,\dots,T\}$. Fix a window size $k \ge 1$ and let $W_i$ be the set containing $i$ together with its $k-1$ nearest neighbours in Euclidean distance. The composition vector of cell $i$ is

$$v_i = \big(v_{i1},\dots,v_{iT}\big) \in \Delta^{T-1}, \qquad v_{it} = \frac{1}{k}\sum_{j \in W_i} \mathbf{1}\{c_j = t\},$$

a point of the probability simplex recording the frequency of each cell type among the $k$ cells of the window. A partition of $\{v_1,\dots,v_n\}$ into $m$ groups by $k$-means minimizes $\sum_{r=1}^{m}\sum_{i \in C_r} \lVert v_i - \mu_r \rVert_2^2$ with $\mu_r$ the mean of cluster $C_r$; each cell is then assigned the label of the cluster containing its own composition vector, and the resulting classes are the cellular neighbourhoods of the tissue.

## Remarks

The construction describes a tissue by the local mixtures it contains rather than by its global cell-type proportions: two samples can have identical overall composition and entirely different organization, and only the window statistic separates them. Using a fixed count $k$ of nearest neighbours rather than a fixed radius adapts the window to local cell density, at the cost of making the physical window size vary. Because each $v_i$ lies in the simplex, Euclidean $k$-means on these vectors groups windows with similar proportions; the cluster centroids $\mu_r$ are themselves composition vectors and so are directly interpretable as recurrent local motifs.

## Sources

- Schurch CM, Bhate SS, Barlow GL, et al. Coordinated cellular neighborhoods orchestrate antitumoral immunity at the colorectal cancer invasive front. *Cell* 182:1341-1359 (2020), STAR Methods, "Neighborhood identification". DOI <https://doi.org/10.1016/j.cell.2020.07.005>. PMCID PMC7479520.
