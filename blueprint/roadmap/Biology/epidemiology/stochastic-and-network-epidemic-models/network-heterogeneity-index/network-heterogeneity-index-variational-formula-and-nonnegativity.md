# Network heterogeneity index: variational formula and nonnegativity

**Setting.** For an irreducible patch Laplacian $L$ (columns summing to zero) with normalized positive null vector $\boldsymbol\theta$ and group inverse $L^\# = (\ell^\#_{ij})$, and a vector of local growth rates $\mathbf q$, the network heterogeneity index is

$$\mathcal H = \mathbf q^\top L^\#\operatorname{diag}(\boldsymbol\theta)\,\mathbf q = \sum_{i,j} q_i\,\ell^\#_{ij}\,q_j\,\theta_j .$$

It is the coefficient of $1/\mu$ in the large-dispersal expansion $s(\operatorname{diag}(\mathbf q) - \mu L) = \mathcal A + \mathcal H/\mu + o(1/\mu)$.

**Lemma.** All row and column sums of $L^\#\operatorname{diag}(\boldsymbol\theta)$ vanish.

**Theorem (variational formula).**

$$\mathcal H = -\frac12\sum_{i=1}^n\sum_{j\ne i}\ell^\#_{ij}\,\theta_j\,(q_i - q_j)^2 .$$

**Theorem (nonnegativity).** $\mathcal H \ge 0$, with equality if and only if $\mathbf q$ is a scalar multiple of $\mathbf 1$, i.e. the environment is homogeneous.

**Theorem (one hot spot).** Let $L$ be irreducible and symmetric, so that $\theta_i = 1/n$. Suppose every patch has growth rate $q^{(\ell)}$ except patch $k$, which has $q^{(h)}$ (a hot spot in the SIS model, a source in the metapopulation model). Then

$$\mathcal H = \frac{\ell^\#_{kk}\,\big(q^{(h)} - q^{(\ell)}\big)^2}{n}.$$

With the network average fixed, at large dispersal the hot spot raises the network growth rate most when it sits at the patch with the largest diagonal group-inverse entry $\ell^\#_{kk}$.

## Depends on

- [Large-dispersal expansion of the patch-network growth rate](large-dispersal-expansion-of-the-patch-network-growth-rate.md)

## Expansion

The variational formula uses $\mathbf 1^\top L^\# = 0$, so $\ell^\#_{ii} = -\sum_{j\ne i}\ell^\#_{ji}$ removes the diagonal, and the row-sum identity symmetrizes the remaining terms into squared differences. For nonnegativity, put $\mathbf y = \operatorname{diag}(\boldsymbol\theta)^{-1}L^\#\operatorname{diag}(\boldsymbol\theta)\mathbf q$. Then $LL^\# = I_n - \boldsymbol\theta\mathbf 1^\top$ gives $\mathcal H = \mathbf y^\top\operatorname{diag}(\boldsymbol\theta)L^\top\mathbf y$. The symmetric part $\operatorname{diag}(\boldsymbol\theta)L^\top + L\operatorname{diag}(\boldsymbol\theta)$ is an irreducible symmetric Laplacian, hence positive semidefinite with kernel spanned by $\mathbf 1$. If $\mathcal H = 0$, then $\mathbf y \propto \mathbf 1$, so $\operatorname{diag}(\boldsymbol\theta)\mathbf q \in \ker L$ and $\mathbf q \propto \mathbf 1$. The one-hot-spot formula is the variational formula with a single nonzero difference pattern, using $\sum_{j}\ell^\#_{kj} = 0$ for symmetric $L$.

## Sources

- Poroshat Yazdanbakhsh, Mark Anderson and Zhisheng Shuai, "A New Perspective on Determining Disease Invasion and Population Persistence in Heterogeneous Environments", Journal of Mathematical Biology 91 (2025), 75, <https://doi.org/10.1007/s00285-025-02302-0>; numbering as in arXiv:2410.09154: Lemma 4.1, Theorem 4.2, Lemma 4.3, Theorem 4.4, Theorem 5.1.
