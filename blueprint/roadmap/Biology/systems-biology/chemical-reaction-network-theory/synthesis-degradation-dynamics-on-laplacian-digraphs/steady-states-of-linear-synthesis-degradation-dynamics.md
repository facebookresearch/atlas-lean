# Steady states of linear synthesis–degradation dynamics on a labeled digraph

**Setting.** Let $G$ be a digraph on vertices $1,\dots,n$ (species or states) with non-negative edge labels and column-convention Laplacian $\mathcal L(G)$ ($\mathbb 1^T\mathcal L(G)=0$). Add zeroth-order synthesis $\xrightarrow{s_i}i$ and first-order degradation $i\xrightarrow{d_i}$ at some vertices, giving the *synthesis–degradation (SD) dynamics*

$$\frac{d\mathbf x}{dt}=\mathcal L(G)\,\mathbf x-D\,\mathbf x+\mathbf s,\qquad D=\operatorname{diag}(d_i)\ne0,\ \ \mathbf s=(s_i)\ge0 .$$

Nonlinear networks fit this frame when nonlinearities are absorbed into edge labels. The *complementary digraph* $G^\star$ adds one vertex $\star$ with edges $\star\xrightarrow{s_i}i$ and $i\xrightarrow{d_i}\star$.

**Theorem.**

*(1)* The SD dynamics have a unique solution for each initial condition.

*(2)* *(Strongly connected case.)* If $G^\star$ is strongly connected, $F=\mathcal L(G)-D$ is non-singular with all eigenvalues in $\{\operatorname{Re}\lambda<0\}$, and there is a unique globally stable steady state

$$\mathbf x_{ES}=-(\mathcal L(G)-D)^{-1}\mathbf s,\qquad (\mathbf x_{ES})_i=\frac{(\boldsymbol\rho^{G^\star})_i}{(\boldsymbol\rho^{G^\star})_\star},$$

where $\boldsymbol\rho^{G^\star}$ is the Matrix-Tree kernel vector of $\mathcal L(G^\star)$ (entry $k$ is the total weight of spanning trees of $G^\star$ rooted at $k$). In particular synthesis and degradation balance, $\sum_id_ix_i=\sum_is_i$.

*(3)* *(General case.)* If $G^\star$ is not strongly connected, order the vertices so that

$$F=\begin{pmatrix}N&0\\B&T\end{pmatrix},\qquad \mathbf s=\begin{pmatrix}\mathbf s'\\ \mathbf s''\end{pmatrix},$$

where $N$ collects the (non-singular, perturbed-Laplacian) blocks of strongly connected components that leak to $\star$ or to other components, and $T$ collects the Laplacian blocks of the terminal components of $G^\star$ that carry no degradation. A steady state exists if and only if

$$\mathbf s''=0\qquad\text{and}\qquad B\,N^{-1}\mathbf s'=0 .$$

*(4)* Whenever a steady state exists, every solution converges to a steady state as $t\to\infty$, and the limit is computable from the graph through spanning-tree weights.

## Expansion

Existence and uniqueness of trajectories is immediate because the vector field is affine. In the strongly connected case, every diagonal block of $F$ is a perturbed Laplacian of a strongly connected digraph and hence non-singular; applying Gershgorin's theorem to the columns of $F$ puts the spectrum in the closed left half-plane, and non-singularity removes $0$, so the shifted variable $\mathbf y=\mathbf x-\mathbf x_{ES}$ decays to zero. The graph formula follows because $(\mathbf x,1)$ is a steady state of the Laplacian dynamics on $G^\star$ exactly when $\mathbf x$ is an SD steady state, and the kernel of a strongly connected Laplacian is spanned by $\boldsymbol\rho^{G^\star}$; normalizing the $\star$ entry to $1$ fixes the scale. In the general case, Gaussian elimination reduces existence to solvability of $\mathcal L_{r+i}\mathbf z^{(i)}=-\mathbf s^{(i)}+B_iN^{-1}\mathbf s'$ on each terminal block; summing with $\mathbb 1^T$ gives $\mathbb 1^T\mathbf s^{(i)}=\mathbb 1^TB_iN^{-1}\mathbf s'$, and since $\mathbf s^{(i)},B_i\ge0$ while $N^{-1}\le0$ entrywise, both sides vanish, forcing the two conditions. Convergence uses the Gershgorin bound again together with a representation of the limit through left and right null vectors of $F$.

The results are Proposition 3.1 and Theorems 3.2–3.4 of the source; the sign fact $N^{-1}\le0$ is proved in its section on the inverse of non-singular perturbed matrices. The framework is applied there to a model of insulin secretion in pancreatic $\beta$-cells.

## Depends on

- [Non-positive inverse of a non-singular perturbed Laplacian](non-positive-inverse-of-a-perturbed-laplacian.md)

## Sources

- I. Mirzaev, D. M. Bortz, *Analytical Equilibrium Solutions of Biochemical Systems with Synthesis and Degradation*, arXiv:1404.6477 (2014). <https://doi.org/10.48550/arXiv.1404.6477>
