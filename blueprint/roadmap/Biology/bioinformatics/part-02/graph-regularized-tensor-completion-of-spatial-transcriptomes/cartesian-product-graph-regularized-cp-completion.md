# Cartesian-product-graph-regularized CP completion

**Setting.** Spatial transcriptomics data form a tensor $\mathcal{T} \in \mathbb{R}^{n_p \times n_y \times n_x}_{\ge 0}$ (genes $\times$ array rows $\times$ array columns), observed only where the binary mask $\mathcal{M}$ equals $1$. Gene relations are given by a protein–protein interaction graph $G_p$, and spatial adjacency by path graphs $G_y$, $G_x$ along the two array axes; for $i \in \{p, y, x\}$ let $W_i$, $D_i$ and $L_i = D_i - W_i$ be the adjacency, degree and Laplacian matrices. The **Cartesian product graph** $G_{(x,y,p)}$ on $V_x \times V_y \times V_p$ joins two triples iff they differ in exactly one coordinate and that coordinate pair is an edge of the corresponding factor graph; its Laplacian is the Kronecker sum

$$L_{(x,y,p)} = L_x \oplus L_y \oplus L_p = L_x \otimes I \otimes I + I \otimes L_y \otimes I + I \otimes I \otimes L_p .$$

**Model.** With a rank-$r$ CP representation $\hat{\mathcal{T}} = [\![ A_p, A_y, A_x ]\!] = \sum_{s=1}^r a^{(s)}_p \circ a^{(s)}_y \circ a^{(s)}_x$ and nonnegative factors $A_i \in \mathbb{R}^{n_i \times r}_{\ge 0}$, solve

$$\min_{A_p, A_y, A_x \ge 0} \ \frac12 \big\| \mathcal{M} \circledast (\mathcal{T} - \hat{\mathcal{T}}) \big\|_F^2 + \frac{\lambda}{2}\, \operatorname{vec}(\hat{\mathcal{T}})^\top L_{(x,y,p)}\, \operatorname{vec}(\hat{\mathcal{T}}), \qquad \lambda \ge 0 .$$

**Proposition.**

1. *(Smoothness.)* $\operatorname{vec}(\hat{\mathcal T})^\top L_{(x,y,p)} \operatorname{vec}(\hat{\mathcal T}) = \sum_{\{u,v\} \in E(G_{(x,y,p)})} (\hat{\mathcal T}_u - \hat{\mathcal T}_v)^2$, which penalizes differences between spatially adjacent spots for the same gene and between interacting genes at the same spot.

2. *(Factorized evaluation.)* With $\Phi_i = A_i^\top A_i$ and $\Theta_i = A_i^\top L_i A_i$,

    $$\operatorname{vec}(\hat{\mathcal T})^\top L_{(x,y,p)} \operatorname{vec}(\hat{\mathcal T}) = \mathbf{1}^\top\big( \Theta_p \circledast \Phi_y \circledast \Phi_x + \Phi_p \circledast \Theta_y \circledast \Phi_x + \Phi_p \circledast \Phi_y \circledast \Theta_x \big)\mathbf{1},$$

    so the regularizer and its gradient $\partial J_2/\partial A_p = A_p(\Phi_x \circledast \Theta_y + \Phi_y \circledast \Theta_x) + L_p A_p (\Phi_x \circledast \Phi_y)$ cost $O\big(\sum_i (r^2 n_i + r\,|E_i|)\big)$ without forming the $n_p n_y n_x$-dimensional Laplacian.

3. *(Multiplicative updates.)* Splitting each gradient into nonnegative parts, $\nabla = [\nabla]^+ - [\nabla]^-$ (data term: $[\cdot]^+ = (\mathcal M \circledast \hat{\mathcal T})_{(1)}(A_x \odot A_y)$, $[\cdot]^- = (\mathcal M \circledast \mathcal T)_{(1)}(A_x \odot A_y)$; regularizer: $D_i$ parts positive, $W_i$ parts negative), the update $[A_p]_{ab} \leftarrow [A_p]_{ab}\, [\nabla]^-_{ab} / [\nabla]^+_{ab}$ (and likewise for $A_y$, $A_x$) keeps the factors nonnegative and has the stationarity condition $[A_p]_{ab}\,(\partial J / \partial A_p)_{ab} = 0$ as its fixed points.

## Expansion

The Kronecker-sum form follows because an edge of the product graph changes one coordinate along an edge of one factor, so the Laplacian acts on each mode separately. Item 1 is the standard identity $z^\top L z = \sum_{\{u,v\} \in E}(z_u - z_v)^2$ for a graph Laplacian. Item 2 uses $\langle \hat{\mathcal T}, \hat{\mathcal T} \times_p L_p\rangle = \sum_{s,s'} (a^{(s)\top}_p L_p a^{(s')}_p)(a^{(s)\top}_y a^{(s')}_y)(a^{(s)\top}_x a^{(s')}_x)$ and its analogues for the other modes; differentiating gives the gradient. The data-term gradient only needs entries of $\hat{\mathcal T}$ at observed positions, a sparse matricized-tensor-times-Khatri–Rao product of cost $O(r|\mathcal M|)$. Because $L = D - W$ with $D, W \ge 0$, the gradients split into nonnegative parts, and the Lee–Seung-type ratio update decreases the objective (the descent argument via auxiliary functions is given in the paper's supplement). Using the Cartesian rather than tensor or strong product keeps the regularization graph sparse, linking only entries that differ in one mode.

## Sources

- Z. Li, T. Song, J. Yong and R. Kuang, "Imputation of spatially-resolved transcriptomes by graph-regularized tensor completion", PLoS Computational Biology 17 (2021), e1008218, Materials and methods (Proposition 1, Eqs. (2)–(13), Algorithm 1), <https://doi.org/10.1371/journal.pcbi.1008218>, PMCID: PMC8055040.
