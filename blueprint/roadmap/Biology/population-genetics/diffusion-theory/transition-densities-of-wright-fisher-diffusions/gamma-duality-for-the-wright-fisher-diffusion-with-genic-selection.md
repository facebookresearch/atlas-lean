# Gamma duality for the Wright-Fisher diffusion with genic selection

Let $\mathbf X = (\mathbf X_t)_{t \ge 0}$ be the $K$-allele Wright-Fisher diffusion on the simplex $\Delta_K$ with parent-independent mutation and genic selection, with generator

$$\mathcal A_K = \frac12\sum_{i,j=1}^K x_i(\delta_{ij} - x_j)\frac{\partial^2}{\partial x_i\partial x_j} + \frac12\sum_{i=1}^K\Big[\alpha_i - |\boldsymbol\alpha|x_i + x_i\Big(\tilde\sigma_i - \sum_{j}\tilde\sigma_jx_j\Big)\Big]\frac{\partial}{\partial x_i},$$

mutation parameters $\boldsymbol\alpha \in [0,\infty)^K$, $|\boldsymbol\alpha| = \sum_i\alpha_i$, and selection coefficients $\tilde\sigma_i$, shifted to $\sigma_i = \tilde\sigma_i - \min_k\tilde\sigma_k \ge 0$ without changing the model. For $\boldsymbol\alpha \in (0,\infty)^K$ the stationary density is $\pi^{\boldsymbol\sigma}_{\boldsymbol\alpha}(\mathbf x) = c_{\boldsymbol\alpha,\boldsymbol\sigma}^{-1}e^{\langle\boldsymbol\sigma,\mathbf x\rangle}\mathbf x^{\boldsymbol\alpha - \mathbf 1}$, and $c_{\boldsymbol\alpha,\mathbf 0} = \prod_j\Gamma(\alpha_j)/\Gamma(|\boldsymbol\alpha|)$ is the Dirichlet constant.

**Dual process.** Let $(\mathbf N_t)_{t \ge 0}$ be the birth-and-death process on $\mathbb Z_+^K$ with rates

$$q(\mathbf n, \mathbf n - \mathbf e_i) = \frac{n_i(|\boldsymbol\alpha| + |\mathbf n| - 1)}{2}, \qquad q(\mathbf n, \mathbf n + \mathbf e_i) = \frac{\sigma_i(\alpha_i + n_i)}{2}, \qquad i = 1, \dots, K.$$

**Proposition (gamma duality).** For $\boldsymbol\alpha \in (0,\infty)^K$ let

$$h(\mathbf x, \mathbf n) = \frac{c_{\boldsymbol\alpha,\boldsymbol\sigma}}{c_{\boldsymbol\alpha+\mathbf n,\mathbf 0}}\,e^{-\langle\boldsymbol\sigma,\mathbf x\rangle}\,\mathbf x^{\mathbf n}.$$

Then for all $\mathbf x \in \Delta_K$, $\mathbf n \in \mathbb Z_+^K$ and $t \ge 0$,

$$\mathbb E\big[h(\mathbf X_t, \mathbf n) \mid \mathbf X_0 = \mathbf x\big] = \mathbb E\big[h(\mathbf x, \mathbf N_t) \mid \mathbf N_0 = \mathbf n\big].$$

**Proposition (dual stationary law).** For $\boldsymbol\alpha \in (0,\infty)^K$ the dual is reversible with stationary distribution

$$\pi(\mathbf k) \propto \frac{\boldsymbol\alpha_{(\mathbf k)}}{|\boldsymbol\alpha|_{(|\mathbf k|)}}\,\frac{\boldsymbol\sigma^{\mathbf k}}{\mathbf k!}, \qquad \mathbf k \in \mathbb Z_+^K,$$

where $(\cdot)_{(m)}$ denotes rising factorials (componentwise for vectors); the normalizing constant is the confluent hypergeometric series $\Phi^{(K)}_2(\boldsymbol\alpha; |\boldsymbol\alpha|; \boldsymbol\sigma)$.

## Depends on

- [Transition density of the multi-allelic Wright-Fisher diffusion with selection](multi-allelic-transition-density-with-selection.md)
- [K-allele Wright-Fisher generator on the simplex](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)

## Expansion

Applying $\mathcal A_K$ to the tilted monomial $e^{-\langle\boldsymbol\sigma,\mathbf x\rangle}\mathbf x^{\mathbf n}$ produces only the monomials of degree $\mathbf n - \mathbf e_i$ and $\mathbf n + \mathbf e_i$, and the Dirichlet-constant identities $(\alpha_i + n_i - 1)/c_{\boldsymbol\alpha+\mathbf n,\mathbf 0} = (|\boldsymbol\alpha| + |\mathbf n| - 1)/c_{\boldsymbol\alpha+\mathbf n-\mathbf e_i,\mathbf 0}$ and $(|\boldsymbol\alpha| + |\mathbf n|)/c_{\boldsymbol\alpha+\mathbf n,\mathbf 0} = (\alpha_i + n_i)/c_{\boldsymbol\alpha+\mathbf n+\mathbf e_i,\mathbf 0}$ convert the coefficients into exactly the rates above, so $\mathcal A_K h(\cdot,\mathbf n)$ equals the dual generator applied to $h(\mathbf x, \cdot)$. Compared with the Barbour-Ethier-Griffiths dual, the exponential tilt removes all ratios of selection-dependent normalizing constants from the rates: deaths are Kingman coalescence plus mutation, births are selection events at rate $\sigma_i(\alpha_i + n_i)/2$. Detailed balance for the product-form weights gives the stationary law.

## Sources

- J. Sant, P. A. Jenkins and M. Ruggiero, "A tractable transition function for the Wright-Fisher diffusion with selection via gamma duality", arXiv preprint (2026), Definition 3.1, Proposition 3.2, Lemma 3.3 and Proposition 3.4. <https://doi.org/10.48550/arXiv.2611.08623>