# Laplacian score and eigenscore decomposition of gene signals

**Setting.** Let $G=(V,E)$ be a weighted undirected graph on cells (for example a $k$-nearest-neighbor graph of single-cell expression profiles) with symmetric adjacency $A$, degrees $d_u=\sum_vA_{uv}>0$ and $D=\mathrm{diag}(d)$. A gene defines a graph signal $g:V\to\mathbb R$ (its expression in each cell). The combinatorial, normalized and random-walk Laplacians are

$$L=D-A,\qquad\mathcal L=D^{-1/2}LD^{-1/2}=I-D^{-1/2}AD^{-1/2},\qquad L_{rw}=D^{-1}L .$$

The graph mean and variance are $\mu_G(g)=\sum_v d_vg(v)/\sum_ud_u$ and $\mathrm{Var}_G(g)=\sum_vd_v\,(g(v)-\mu_G(g))^2$.

**Rayleigh quotient and Laplacian score.** With $\langle g,h\rangle=\sum_vg(v)h(v)$ and sums over unordered adjacent pairs $u\sim v$,

$$R_{\mathcal L}(D^{1/2}g)=\frac{\langle g,Lg\rangle}{\langle g,Dg\rangle}=\frac{\sum_{u\sim v}A_{uv}\,(g(u)-g(v))^2}{\sum_ud_u\,g(u)^2},$$

which vanishes for constant signals. The *Laplacian score* of $g$ is the Rayleigh quotient of the degree-recentered signal $\tilde g=g-\mu_G(g)$:

$$\mathrm{LS}(g)=R_{\mathcal L}(D^{1/2}\tilde g)=\frac{\sum_{u\sim v}A_{uv}(g(u)-g(v))^2}{\mathrm{Var}_G(g)} .$$

Small scores mark genes whose expression varies smoothly along the cell graph.

**Eigenscores.** Let $\mathcal L=\sum_i\lambda_ie_ie_i^{\top}$ with orthonormal eigenvectors $e_i$ and $0=\lambda_1\le\lambda_2\le\dots\le 2$. The $i$th eigenscore of $g$ is

$$\mathrm{eig}_i(g)=\frac{\langle D^{1/2}g,e_i\rangle}{\|D^{1/2}g\|},$$

the cosine of the angle between $D^{1/2}g$ and $e_i$, and

$$R_{\mathcal L}(D^{1/2}g)=\sum_i\lambda_i\,\mathrm{eig}_i(g)^2,\qquad \sum_i\mathrm{eig}_i(g)^2=1 .$$

Applied to $\tilde g$, this writes the Laplacian score as a $\lambda$-weighted average of squared eigenscores, so each eigenscore isolates the contribution of one spatial scale of the graph.

## Expansion

The identity $\langle D^{1/2}g,\mathcal LD^{1/2}g\rangle=\langle g,Lg\rangle=\sum_{u\sim v}A_{uv}(g(u)-g(v))^2$ follows from $\mathcal L=D^{-1/2}LD^{-1/2}$ and the edge expansion of the quadratic form of $L$; the denominator is $\|D^{1/2}g\|^2=\langle g,Dg\rangle$. Since $\mathcal LD^{1/2}\mathbf 1=0$, the eigenvector $e_1$ is proportional to $D^{1/2}\mathbf 1$, and recentering by the degree-weighted mean makes $D^{1/2}\tilde g$ orthogonal to it, which is why the Laplacian score is undefined for constant genes and large for nearly constant ones. Expanding $D^{1/2}g$ in the orthonormal eigenbasis gives the eigenscore decomposition by Parseval's identity. Low-frequency eigenvectors correspond to the generalized eigenproblem $Lf=\lambda Df$ of Laplacian eigenmaps, so genes with mass on the first few eigenscores follow the dominant cell-state axes; the paper complements these with Markov-stability community scores and persistent Laplacians across a filtration.

## Sources

- Hoekzema RS, Marsh L, Sumray O, Carroll TM, Lu X, Byrne HM, Harrington HA, "Multiscale Methods for Signal Selection in Single-Cell Data", Entropy (Basel) 2022 Aug 13;24(8):1116, Definitions 1-4 and Equations (1)-(10), <https://doi.org/10.3390/e24081116>, PMCID PMC9407339.
