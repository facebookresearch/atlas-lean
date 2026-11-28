# Non-positive inverse of a non-singular perturbed Laplacian

**Setting.** Let $G$ be a digraph on $n$ vertices with non-negative edge labels, and let $\mathcal L(G)$ be its Laplacian in the column convention used for linear (Laplacian) dynamics $\dot{\mathbf x}=\mathcal L(G)\mathbf x$: for $i\ne j$, $\mathcal L(G)_{ij}\ge0$ is the label of the edge $j\to i$, and each diagonal entry makes its column sum zero, so $\mathbb 1^T\mathcal L(G)=0$. A *perturbed Laplacian* is

$$P=\mathcal L(G)-\Delta,\qquad \Delta=\operatorname{diag}(\delta_1,\dots,\delta_n),\ \delta_i\ge0 .$$

If $G$ is strongly connected and $\Delta\ne0$, then $P$ is non-singular; for general $G$ it may be singular.

**Theorem.** Every non-singular perturbed Laplacian has an entrywise non-positive inverse:

$$\big(P^{-1}\big)_{ij}\le0\qquad\text{for all } i,j .$$

If $G$ is strongly connected the inequality is strict and explicit:

$$\big(P^{-1}\big)_{ij}=-\frac{\big(\boldsymbol\rho^{G^{ji}}\big)_i}{\big(\boldsymbol\rho^{G^{n+1}}\big)_{n+1}}<0,$$

where $\boldsymbol\rho^{H}$ denotes the Matrix-Tree kernel vector of a strongly connected digraph $H$ (entry $k$ is the total weight of spanning trees rooted at $k$), $G^{ji}$ is a strongly connected digraph whose Laplacian agrees with $P$ outside its $j$-th row and $i$-th column (the value does not depend on the choice: up to sign it is the minor of $P$ obtained by deleting row $j$ and column $i$), and $G^{n+1}$ is the strongly connected digraph obtained by adding a vertex $n+1$ that absorbs the perturbation edges, so that $\det P$ is a minor of $\mathcal L(G^{n+1})$. The source's display (Section 4.1, (4.2)) transposes the indices: it rebuilds the $i$-th row and $j$-th column and uses $(\boldsymbol\rho^{G^{ij}})_i$, which is not determined by $P$.

## Expansion

Write $P^{-1}=\operatorname{adj}(P)/\det P$. In the strongly connected case, rebuild the $i$-th row and $j$-th column of $P$ into a Laplacian of a strongly connected digraph $G^{ij}$ with the same $(ij)$ minor; by the Matrix-Tree theorem that minor is, up to sign, the total weight of spanning trees rooted at $j$, so $(\operatorname{adj}P)_{ji}=(-1)^{n-1}(\boldsymbol\rho^{G^{ij}})_j$, and after renaming $(\operatorname{adj}P)_{ij}=(-1)^{n-1}(\boldsymbol\rho^{G^{ji}})_i$. Similarly, bordering $P$ by one row and column turns it into the Laplacian of a strongly connected $G^{n+1}$, so $\det P=(-1)^n(\boldsymbol\rho^{G^{n+1}})_{n+1}$. Spanning-tree weights of strongly connected digraphs are positive, which gives the strict sign. For an arbitrary digraph with $P$ non-singular, the vertices are grouped by strongly connected components so that $P$ is block lower-triangular with non-singular perturbed-Laplacian diagonal blocks, and the sign pattern propagates from the blocks through the non-negative couplings.

Equivalently, $-P$ is a non-singular M-matrix (a Z-matrix that is column diagonally dominant with non-singularity), and the result recovers $(-P)^{-1}\ge0$ with an explicit spanning-tree formula. The fact settles a claim left open in earlier work on Laplacian dynamics of biochemical networks and is what makes the existence criterion for steady states of synthesis–degradation dynamics purely graph-theoretic.

The statement and proof occupy the section on the inverse of non-singular perturbed matrices of the source.

## Sources

- I. Mirzaev, D. M. Bortz, *Analytical Equilibrium Solutions of Biochemical Systems with Synthesis and Degradation*, arXiv:1404.6477 (2014). <https://doi.org/10.48550/arXiv.1404.6477>
