# Local approximation of persistence fingerprints

Let a protein-ligand complex have $n$ protein atoms and $m$ ligand atoms, and let its persistence fingerprint be a fixed vector of bin integrals of internuclear persistence contours, sums of Gaussians centered at the critical values of opposition-distance Vietoris-Rips persistence (protein-ligand interatomic distances). Let $\omega \approx 2.4$ be the matrix multiplication exponent.

**Theorem.** Assume a fixed positive lower bound on interatomic distances. For every $0 < \varepsilon < 1$, after an $O(mn \log(mn))$ preprocessing step, an approximation of the persistence fingerprint can be computed in time $O\big(m \log^{6\omega}(m/\varepsilon)\big)$, independent of the protein size $n$, such that every component differs from the exact component by less than $\varepsilon$.

## Depends on

- [Bipartite structure of opposition-distance Rips persistence](bipartite-structure-of-opposition-distance-rips-persistence.md)

## Expansion

The argument uses the exponential decay of the Gaussian weight in the contours: the contribution to a fingerprint component attributable to a ligand atom converges as the protein grows, so for each $\varepsilon$ there is a radius $r_\varepsilon$ such that discarding all atoms farther than $r_\varepsilon$ from that ligand atom changes the component by less than $\varepsilon$. The lower bound on interatomic distances bounds the number of atoms within distance $r_\varepsilon$ of a ligand atom in terms of $r_\varepsilon$ alone, so the work per ligand atom depends only on $\varepsilon$ and $m$, not on $n$; the full accounting, which gives the stated polylogarithmic factor, is in the source's supplementary text, and the preprocessing sorts the $mn$ protein-ligand distances. Earlier persistent-homology affinity features computed full Rips persistence on the whole complex in $O((m+n)^{4.8})$ time or worse, so the bound removes the dependence on protein size; empirically the maximum approximation error over about 45,000 complexes was $4.8 \times 10^{-7}$.

## Sources

- Y. Long, B. R. Donald, "Predicting Affinity Through Homology (PATH): Interpretable binding affinity prediction with persistent homology", PLoS Computational Biology (2025), Methods (opposition distance, Eq. 2; internuclear persistence contours; persistence fingerprint; Theorem 1) and Results (computational complexity of the persistence fingerprint). <https://doi.org/10.1371/journal.pcbi.1013216> (PMC12226026)
