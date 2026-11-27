# x-polynomial distribution of the number of shortest paths

**Setting.** Let $G = (V,E)$ be a probabilistic network in which each edge $e_j$ is present independently with probability $p_j$ (absent with $q_j = 1-p_j$). For nodes $s,t$ let $\mathcal H_{s,t} = \{H_1,H_2,\dots\}$ be the simple $s$–$t$ paths of the deterministic graph containing all edges, with $l_i$ the number of edges of $H_i$. In a random realization, let $B_{s\sim t}$ be the number of shortest $s$–$t$ paths, i.e. of present paths of minimum length (with $B_{s\sim t} = 0$ if no path is present).

**x-polynomial.** Build the bipartite graph between paths $H_i$ (variables $x_i$) and the edges they use. For each edge $e_j$ define the edge polynomial

$$Z_j = p_j \prod_{i:\, e_j \in H_i} x_i + q_j,$$

and the x-polynomial $Z_{s,t} = \prod_j Z_j$, whose $2^{|E'|}$ monomials ($E'$ the edges on some path) correspond to the presence/absence patterns of those edges, with coefficient equal to the pattern's probability. In each monomial $\alpha \prod_i x_i^{c_i}$:

- the *collapse* operator replaces $x_i$ by $t_{l_i}$ if $c_i = l_i$ (all edges of $H_i$ present) and by $1$ otherwise, giving monomials $\alpha \prod_\ell t_\ell^{c_\ell}$ where $c_\ell$ counts present paths of length $\ell$;
- the *select* operator replaces the variable $t_r$ of smallest index present by $y$ and deletes all other $t_\ell$ and any remaining $x_i$, giving $\alpha\,y^{c_r}$.

**Theorem.** After multiplying all edge polynomials, collapsing and selecting,

$$Z_{s,t} = \sum_{k=0}^{\pi^*_{s,t}} p_k\, y^k, \qquad p_k = \Pr\bigl[B_{s\sim t} = k\bigr],$$

where $\pi^*_{s,t}$ is the largest possible number of shortest paths; in particular $\mathbb{E}\,B_{s\sim t} = \sum_k k\,p_k$.

**Early collapse and select.** Collapse of $x_i$ may be applied as soon as the last edge polynomial containing $x_i$ has been multiplied, since later factors do not change its exponent. If paths are processed in increasing length and $k$ is the smallest unprocessed length, then after the last edge polynomial of length-$k$ paths has been multiplied, applying select to the monomials already containing $t_k$ produces exactly the terms that multiplying by all remaining edge polynomials, collapsing and then selecting would produce. Such monomials can therefore be finalized immediately, which keeps the number of live terms small.

## Expansion

Paths sharing edges are dependent, so path-wise probabilities cannot simply be multiplied; the x-polynomial is a generating function over edge states that records, through the exponent of $x_i$, how many edges of each path are present. A path exists exactly when its exponent reaches its length. Summing coefficients over monomials with the same number of shortest paths gives the distribution of $B_{s\sim t}$ because each monomial is one disjoint edge configuration. Early select is valid because, once all edges of length-$k$ paths are fixed and a length-$k$ path is present, the remaining edge polynomials can only add longer paths, which select discards, and their coefficients sum to $\prod_{j}(p_j + q_j) = 1$. The cost is exponential in the worst case (the problem generalizes two-terminal reliability), but the method is exact.

## Sources

- Y. Ren, A. Ay, T. Kahveci, "Shortest path counting in probabilistic biological networks", BMC Bioinformatics (2018), Methods: bipartite graph and x-polynomial (Eqs. (2)–(3), Definition 1), collapse and select operators (Eqs. (4)–(7)), Theorem 1, Corollary 1 (Eq. (8)), Lemma 1, <https://doi.org/10.1186/s12859-018-2480-z>, PMCID PMC6278053.
