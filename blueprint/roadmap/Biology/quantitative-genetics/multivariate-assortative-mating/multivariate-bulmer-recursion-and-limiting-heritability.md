# Multivariate Bulmer recursion and limiting heritability

Use the infinitesimal additive model with mate cross-correlation matrix $R_{\sigma\times\varphi}$ and cross-covariance $\Sigma_{\sigma\times\varphi}$ from [local genotype invariance](local-genotype-invariance-under-assortative-mating.md), with the number of loci taken to infinity first. Write $\overline\Sigma_{\sigma\times\varphi} = \tfrac12(\Sigma_{\sigma\times\varphi} + \Sigma_{\sigma\times\varphi}^{\top})$ and $\overline R_{\sigma\times\varphi}$ for the symmetrized forms, $\Sigma_G^{(t)}$ for the genotypic covariance in generation $t$, $\Sigma_\Gamma^{(t)} = \Lambda^{\top}\Sigma_G^{(t)}\Lambda$ for the additive genetic covariance of the traits, and $\Sigma_X^{(t)} = \Sigma_\Gamma^{(t)} + \Sigma_E$. For positive definite $B$ let $A \oslash B = B^{-1/2}AB^{-1/2}$ and $A \circledast B = B^{1/2}AB^{1/2}$.

**Multivariate Bulmer recursion.** With $B_{G\mid X}^{(t)} = \Sigma_G^{(t)}\Lambda[\Sigma_X^{(t)}]^{-1}$,

$$\Sigma_G^{(t+1)} = \tfrac12\Sigma_G^{(0)} + \tfrac12\Sigma_G^{(t)} + \tfrac12 B_{G\mid X}^{(t)}\,\overline\Sigma_{\sigma\times\varphi}^{(t)}\,\big[B_{G\mid X}^{(t)}\big]^{\top},$$

so that any fixed point satisfies $\Sigma_G^{(\infty)} = \Sigma_G^{(0)} + B_{G\mid X}^{(\infty)}\overline\Sigma_{\sigma\times\varphi}^{(\infty)}[B_{G\mid X}^{(\infty)}]^{\top}$: positive definite assortment inflates genetic variance and negative definite assortment depresses it.

**Lemma A.3 (existence of a fixed point).** If $\bar\rho\,\vartheta\,\|\Sigma_G^{(0)}\| \le \tfrac14$, where $\bar\rho = \|\overline R_{\sigma\times\varphi}\| \le 1$ and $\vartheta = \lambda_{\max}(\Sigma_\Gamma^{(0)})/\lambda_{\min}(\Sigma_E)$, the iterates are uniformly bounded by $\mu I$ for some $\mu > 0$; by Brouwer's theorem the Bulmer map has a (not necessarily unique) fixed point $\Sigma_G^{(\infty)}$, which satisfies the trait-level identity $\Sigma_\Gamma^{(\infty)} = \Sigma_\Gamma^{(0)} + \Sigma_\Gamma^{(\infty)}\big(\overline R_{\sigma\times\varphi} \oslash \Sigma_X^{(\infty)}\big)\Sigma_\Gamma^{(\infty)}$.

**Theorem A.2 (limiting generalized heritability).** Let $H^{(t)} = \Sigma_\Gamma^{(t)} \oslash \Sigma_X^{(t)}$ be the generalized heritability matrix and $\Theta^{(0)}_{(\infty)} = \Sigma_\Gamma^{(0)} \oslash \Sigma_X^{(\infty)}$. If $\overline R_{\sigma\times\varphi}$ is positive or negative definite, or indefinite with $(\Sigma_\Gamma^{(0)}, \Sigma_E, \overline R_{\sigma\times\varphi})$ pairwise commuting, the matrix quadratic

$$H^{(\infty)}\,\overline R_{\sigma\times\varphi}\,H^{(\infty)} - H^{(\infty)} + \Theta^{(0)}_{(\infty)} = 0$$

has the solution

$$H^{(\infty)} = \tfrac12\,\mathrm{sgn}(\overline R_{\sigma\times\varphi})\Big[I - \big(I - 4\,\mathrm{sgn}(\overline R_{\sigma\times\varphi})(\Theta^{(0)}_{(\infty)} \circledast |\overline R_{\sigma\times\varphi}|)\big)^{1/2}\Big] \oslash |\overline R_{\sigma\times\varphi}|.$$

In the commuting case, with $\bar r_j$ and $h^2_{(0),j}$ the eigenvalues of $\overline R_{\sigma\times\varphi}$ and $H^{(0)}$ along a common eigenbasis, the eigenvalues of $H^{(\infty)}$ are

$$h^2_{(\infty),j} = \frac{1 - \sqrt{1 - 4\bar r_j h^2_{(0),j}(1 - h^2_{(0),j})}}{2\bar r_j(1 - h^2_{(0),j})} \quad (\bar r_j \ne 0), \qquad h^2_{(\infty),j} = h^2_{(0),j} \quad (\bar r_j = 0),$$

and the additive genetic variance along each axis grows by the factor $1/(1 - \bar r_j h^2_{(\infty),j})$, which requires $\bar r_j h^2_{(\infty),j} < 1$.

## Expansion

By the law of total covariance, offspring genetic covariance is the segregation covariance $\Sigma_S = \tfrac12\Sigma_G^{(0)}$, unchanged by assortment, plus the covariance of the midparent value; the midparent covariance is $\tfrac14(2\Sigma_G^{(t)} + \mathrm{Cov}(\mathbf G_\sigma,\mathbf G_\varphi) + \mathrm{Cov}(\mathbf G_\varphi,\mathbf G_\sigma))$, and regressing genotypes on phenotypes turns the mate cross-covariance into $B_{G\mid X}\Sigma_{\sigma\times\varphi}B_{G\mid X}^{\top}$. Multiplying the fixed-point equation by $\Lambda^{\top}$ and $\Lambda$ lifts it to trait level, and conjugating by $\Sigma_X^{-1/2}$ gives the matrix quadratic for $H^{(\infty)}$; choosing the branch of the square root continuous at $\overline R_{\sigma\times\varphi} = 0$ yields the stated solution. For $p = 1$ these reduce to the univariate Bulmer effect $\sigma^2_{\Gamma,(t+1)} = (1 + r h_{(t)}^2/2)\sigma^2_{\Gamma,(t)}$ in its infinitesimal form, Wright's limit $\sigma^2_{\Gamma,(\infty)}/\sigma^2_{\Gamma,(0)} = 1/(1 - r h^2_{(\infty)})$ and Gimelfarb's equilibrium heritability.

## Depends on

- [The Bulmer effect: selection reduces additive variance](../mendelian-segregation-and-the-infinitesimal-mode/bulmer-effect.md)
- [Local genotype invariance under assortative mating](local-genotype-invariance-under-assortative-mating.md)

## Sources

- K. Hlynsson, "A high-dimensional perspective of assortative mating: definition, dynamics, and limiting results" (2026), Section 2.1 (survey of univariate results), Section 3.3 (multivariate Bulmer recursion, limiting dynamics and heritability), Appendix A (Lemmas A.3 to A.5 and Theorem A.2), <https://doi.org/10.48550/arXiv.2611.29703>.
