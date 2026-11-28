# Persistent homology barcodes of a Vietoris–Rips filtration

Let $X$ be a finite set of atoms and $d : X \times X \to [0, \infty]$ a symmetric function with $d(x, x) = 0$ (it need not satisfy the triangle inequality). For $r \ge 0$ the Vietoris–Rips complex $\mathrm{Rips}(X, r)$ is the simplicial complex whose simplices are the nonempty subsets $X' \subseteq X$ with $d(x, x') \le r$ for all $x, x' \in X'$; then $\mathrm{Rips}(X, r) \subseteq \mathrm{Rips}(X, r')$ for $r \le r'$. For a filtration $\varnothing = K_0 \subset K_1 \subset \cdots \subset K_m$ of simplicial complexes, with $\mathbb{Z}_2$ chain groups $C_k(K_i)$, boundary maps $\partial_k$, cycles $Z_k = \ker \partial_k$ and boundaries $B_k = \operatorname{im} \partial_{k+1}$ (so $B_k \subseteq Z_k$ because $\partial_k \circ \partial_{k+1} = 0$), the $p$-persistent $k$-th homology group of $K_i$ is

$$H_k^{p}(K_i) = Z_k(K_i) \big/ \bigl(B_k(K_{i+p}) \cap Z_k(K_i)\bigr),$$

the homology classes of $K_i$ still alive in $K_{i+p}$. Each class born at filtration value $x_i$ and dying at $x_j$ is recorded as an interval $[x_i, x_j)$; the multiset of intervals in dimension $k$ is the $k$-th barcode, and the Betti number $\beta_k(K_i) = \operatorname{rank} Z_k(K_i) - \operatorname{rank} B_k(K_i)$ counts the bars containing $x_i$. Element-specific (multi-component) persistent homology computes barcodes separately for the subsets of atoms of chosen element types, for example all carbons (hydrophobic network) or all nitrogens and oxygens (hydrophilic and hydrogen-bond network).

## Expansion

The Rips construction uses only pairwise values of $d$, so any symmetric dissimilarity, including kernel-transformed distances or matrices with entries deliberately set to a large constant, defines a valid filtration. For a molecule, $\beta_0$ bars record when atoms become connected (bond lengths appear as short $\beta_0$ bars), $\beta_1$ bars record rings and loops, and $\beta_2$ bars record cavities. Restricting to element types keeps chemical information that a single all-atom barcode discards; the resulting family of barcodes, vectorized by binned counts or by statistics of birth, death and persistence, or compared through Wasserstein distances between barcodes, gives fixed-length features for regression of protein–ligand binding affinity and for virtual screening.

## Sources

- Cang Z, Mu L, Wei GW. Representability of algebraic topology for biomolecules in machine learning based scoring and virtual screening. *PLoS Computational Biology* 14:e1005929 (2018), Methods, "Persistent homology", "Element specific persistent homology" and "Distance matrix induced persistent homology", equations (3)–(10). DOI <https://doi.org/10.1371/journal.pcbi.1005929>. PMCID PMC5774846.
