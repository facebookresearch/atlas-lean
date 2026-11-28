# Representer theorem for positive semidefinite metric learning

**Problem (Eqs. 8–9).** Genes are vectors $x_1,\dots,x_N\in\mathbb{R}^p$. A training set $\mathcal{T}=\mathcal{I}\cup\mathcal{N}$ of gene pairs is split into interacting pairs $\mathcal{I}$ (edges of a known network) and non-interacting pairs $\mathcal{N}$. For a symmetric positive semidefinite matrix $M\succeq0$ let $d_M(x,x')=(x-x')^\top M(x-x')$. Solve

$$\min_{\gamma,M,\zeta}\ \|M\|_{\mathrm{Fro}}^2+C\sum_{(i,j)\in\mathcal{T}}\zeta_{ij}$$

subject to $\zeta_{ij}\ge0$, $d_M(x_i,x_j)\le\gamma-1+\zeta_{ij}$ for $(i,j)\in\mathcal{I}$, $d_M(x_i,x_j)\ge\gamma+1-\zeta_{ij}$ for $(i,j)\in\mathcal{N}$, and $M\succeq0$.

**Theorem 1.** Every solution matrix can be written as

$$M=\sum_{(i,j)\in\mathcal{T}}\alpha_{ij}\,(x_i-x_j)(x_i-x_j)^\top,\qquad \alpha_{ij}\in\mathbb{R}.$$

## Expansion

Write $u_{ij}=x_i-x_j$ and $D_{ij}=u_{ij}u_{ij}^\top$, so $d_M(x_i,x_j)=\langle M,D_{ij}\rangle_{\mathrm{Fro}}$. Eliminating slacks with the hinge loss turns the problem into an SVM in the space of symmetric matrices with the Frobenius inner product, plus the constraint $M\succeq0$. Decompose $M=M_S+M_\perp$ with $M_S$ in the span of the $D_{ij}$ and $M_\perp$ orthogonal to all of them. The constraints see only $M_S$, and $\|M\|^2=\|M_S\|^2+\|M_\perp\|^2$, so a solution with $M_\perp\ne0$ could be improved, provided $M_S\succeq0$. That holds: splitting any $v=v_S+v_\perp$ with $v_S\in\mathrm{span}\{u_{ij}\}$ gives $M_Sv_\perp=0$ and $M_\perp v_S=0$, so $v^\top M_Sv=v_S^\top M v_S\ge0$.

## Sources

- J.-P. Vert, J. Qiu, W. S. Noble, "A new pairwise kernel for biological network inference with support vector machines", BMC Bioinformatics 8 (Suppl 10) (2007) S8. <https://doi.org/10.1186/1471-2105-8-S10-S8>, PMCID PMC2230501. Section "Distance metric learning", Eqs. (8)–(9) and Theorem 1.
