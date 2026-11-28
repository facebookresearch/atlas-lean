# Reduced homeostasis matrix criterion for infinitesimal homeostasis

**Setting.** A mass-action system $\dot{\mathbf{x}} = \mathbf{f}(\mathbf{x}) = \sum_{\mathbf{y}\to\mathbf{y}'} k_{\mathbf{y}\to\mathbf{y}'}\mathbf{x}^{\mathbf{y}}(\mathbf{y}' - \mathbf{y})$ on $\mathbb{R}^n_{>0}$ has stoichiometric subspace of dimension $n - d$, with conservation laws $\mathbf{u}_i\cdot\mathbf{x}(t) \equiv M_i$, $i = 1,\dots,d$, and $f_{d+1},\dots,f_n$ linearly independent so that equilibria solve $f_{d+1} = \dots = f_n = 0$, $\mathbf{u}_i\cdot\mathbf{x} = M_i$. The output is $x_n$. The *reduced Jacobian* $\tilde J$ is the $n\times n$ matrix with rows $\mathbf{u}_1,\dots,\mathbf{u}_d$ followed by $\nabla f_{d+1},\dots,\nabla f_n$; an equilibrium is *reduced hyperbolic* if $\det\tilde J \ne 0$ there. The $p$-th *reduced homeostasis matrix* $\tilde H_p$ is $\tilde J$ with its $p$-th row and its last (output) column deleted.

**Theorem (rate-constant input).** Let $\mathbf{x}^*$ be a reduced hyperbolic equilibrium at $k_{ij} = k_{ij}^*$, where the input reaction $\mathbf{y}_i \to \mathbf{y}_j$ satisfies $\mathbf{y}_j - \mathbf{y}_i \in \operatorname{span}\{\mathbf{e}_p\}$. If $\det\tilde H_p = 0$ at $\mathbf{x}^*$, the system exhibits infinitesimal homeostasis: $\frac{d}{dk_{ij}}x_n(k_{ij}^*) = 0$. For complex-balanced equilibria, in particular for weakly reversible deficiency-zero networks, reduced hyperbolicity holds automatically.

**Theorem (concentration robustness).** At a reduced hyperbolic equilibrium with totals $M^*$, if $\det\tilde H_i = 0$ then $\frac{\partial x_n}{\partial M_i}(M^*) = 0$ ($i$-th infinitesimal concentration robustness); if this holds for all $i$, the output is completely infinitesimally robust to all conserved totals. For first-order complex-balanced networks the source gives an analogous criterion for the stochastic model.

## Depends on

- [Unique complex-balanced equilibrium of a deficiency-zero network](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium-of-deficiency.md)

## Expansion

Because $\mathbf{y}_j - \mathbf{y}_i = c\,\mathbf{e}_p$, the rate constant $k_{ij}$ appears only in $f_p$, and $\partial f_p/\partial k_{ij} = c\,\mathbf{x}^{\mathbf{y}_i} \ne 0$. The implicit function theorem gives a smooth equilibrium branch, and differentiating the equilibrium system yields $\tilde J\,\partial\mathbf{x} = -\partial\mathbf{f}$, a vector supported on one row. Cramer's rule then gives $\partial x_n = \pm(\text{that entry})\det\tilde H_p/\det\tilde J$, so homeostasis is the vanishing of a single minor. Differentiating in $M_i$ instead puts the unit vector in the $i$-th conservation row, giving $\det\tilde H_i$. Permuting the homeostasis matrix to block upper-triangular form with irreducible blocks shows that the determinant vanishes iff one irreducible block is singular, which classifies the possible homeostasis types.

## Sources

- J. Jin, G. A. Rempala, "Infinitesimal Homeostasis in Mass-Action Systems", *Journal of Mathematical Biology* 92(3) (2026), 35, Definitions 4.1 and 4.4, Theorem 4.5, Corollaries 4.6-4.7, Theorem 4.9, Corollary 4.10 and Theorem 4.20, <https://doi.org/10.1007/s00285-026-02352-y> (preprint arXiv:2407.11248).
