# Maximal number of one-dimensional Vietoris–Rips persistence pairs

**Proposition (clique complexes).** Let $G=(V,E)$ be a simple graph on $n$ vertices and $X(G)$ its clique (flag) complex. Then

$$\beta_1(X(G))\le\Bigl\lfloor\frac n2\Bigr\rfloor\Bigl\lceil\frac n2\Bigr\rceil-(n-1),$$

with equality for the complete bipartite graph $K_{\lfloor n/2\rfloor,\lceil n/2\rceil}$.

**Proposition (Vietoris–Rips persistence).** Let $P\subset\mathbb R^d$ be a finite point cloud with $n$ points whose pairwise distances are distinct. Then the $1$-dimensional persistence diagram of the Vietoris–Rips filtration $\mathrm{VR}(P,\epsilon)$ has at most

$$N_1(n)=\Bigl\lfloor\frac n2\Bigr\rfloor\Bigl\lceil\frac n2\Bigr\rceil-(n-1)$$

birth–death pairs.

## Expansion

Deleting an edge that lies in a triangle never decreases $\beta_1$ of the clique complex: it removes one edge and at least one triangle. A maximizer can therefore be taken triangle-free. In that case $X(G)=G$ and $\beta_1=|E|-n+1$ for a connected graph, and Mantel's theorem caps triangle-free graphs at $\lfloor n/2\rfloor\lceil n/2\rceil$ edges, with $K_{\lfloor n/2\rfloor,\lceil n/2\rceil}$ attaining the cap. In the filtration, distinct distances mean edges enter one at a time. An edge that closes a triangle $123$ creates no new class, because any cycle through it is homologous, across that triangle, to a cycle that already existed. A filtration with the most pairs can thus be arranged so that all its $1$-cycles are alive at once, and the count reduces to the clique-complex bound. For $n<24$ this improves the general $5n$ bound on the first Betti number of a Vietoris–Rips complex at a fixed scale.

## Sources

- J. Aslam, S. Ardanza-Trevijano, J. Xiong, J. Arsuaga, R. Sazdanovic, "TAaCGH suite for detecting cancer-specific copy number changes using topological signatures", *Entropy* 24(7):896 (2022), Section 3, Propositions 3 and 4, <https://doi.org/10.3390/e24070896>, PMCID PMC9318413.
