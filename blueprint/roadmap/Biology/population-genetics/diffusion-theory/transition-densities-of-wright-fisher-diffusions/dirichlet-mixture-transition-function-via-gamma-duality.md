# Dirichlet-mixture transition function via gamma duality

Let $\mathbf X = (\mathbf X_t)_{t \ge 0}$ be the $K$-allele Wright-Fisher diffusion on the simplex $\Delta_K$ with parent-independent mutation and genic selection, with generator
$$\mathcal A_K = \frac12\sum_{i,j=1}^K x_i(\delta_{ij} - x_j)\frac{\partial^2}{\partial x_i\partial x_j} + \frac12\sum_{i=1}^K\Big[\alpha_i - |\boldsymbol\alpha|x_i + x_i\Big(\tilde\sigma_i - \sum_{j}\tilde\sigma_jx_j\Big)\Big]\frac{\partial}{\partial x_i},$$
mutation parameters $\boldsymbol\alpha \in [0,\infty)^K$, $|\boldsymbol\alpha| = \sum_i\alpha_i$, and selection coefficients $\tilde\sigma_i$, shifted to $\sigma_i = \tilde\sigma_i - \min_k\tilde\sigma_k \ge 0$ without changing the model. For $\boldsymbol\alpha \in (0,\infty)^K$ the stationary density is $\pi^{\boldsymbol\sigma}_{\boldsymbol\alpha}(\mathbf x) = c_{\boldsymbol\alpha,\boldsymbol\sigma}^{-1}e^{\langle\boldsymbol\sigma,\mathbf x\rangle}\mathbf x^{\boldsymbol\alpha - \mathbf 1}$, and $c_{\boldsymbol\alpha,\mathbf 0} = \prod_j\Gamma(\alpha_j)/\Gamma(|\boldsymbol\alpha|)$ is the Dirichlet constant.

Let $(\mathbf N_t)$ be the [gamma dual](gamma-duality-for-the-wright-fisher-diffusion-with-genic-selection.md), with transition probabilities $b_{\mathbf n\mathbf l}(t) = \mathbb P[\mathbf N_t = \mathbf l \mid \mathbf N_0 = \mathbf n]$, and let $\Pi^{\mathbf 0}_{\boldsymbol\beta}$ be the Dirichlet law with parameter $\boldsymbol\beta$ (defined through normalized independent $\Gamma(\beta_i, 1)$ variables, so zero parameters are allowed).

**Proposition (entrance law from infinity).** Writing $\rho(\mathbf n) = (|\mathbf n|, \mathbf n/|\mathbf n|)$, for $t > 0$, $\mathbf l \in \mathbb Z_+^K$ and $\mathbf x \in \Delta_K$,
$$b_{\mathbf l}(t; \mathbf x) := \liminf_{\rho(\mathbf n) \to (\infty, \mathbf x)} b_{\mathbf n\mathbf l}(t)$$
defines a probability mass function on $\mathbb Z_+^K$, weakly continuous in $\mathbf x$.

**Theorem (transition function).** The transition function of the diffusion with generator $\mathcal A_K$ is the mixture of standard Dirichlet laws
$$P^{\boldsymbol\sigma}_{\boldsymbol\alpha}(\mathbf x, d\mathbf y; t) = \sum_{\mathbf l \in \mathbb Z_+^K} b_{\mathbf l}(t; \mathbf x)\,\Pi^{\mathbf 0}_{\boldsymbol\alpha + \mathbf l}(d\mathbf y).$$

In the neutral case $\boldsymbol\sigma = \mathbf 0$ this reduces to the Griffiths-Tavare representation, with weights $d_{|\mathbf l|}(t)$ times a multinomial$(|\mathbf l|, \mathbf x)$ split. With selection the weights no longer factor, but they come from a dual with explicit rates, and the stationary law can be sampled approximately by truncating a total-degree expansion of $\Phi^{(K)}_2$ at level $M_{\max}$ with total variation error at most $2e^{|\boldsymbol\sigma|}\big(e|\boldsymbol\sigma|/(M_{\max}+1)\big)^{M_{\max}+1}$, where $|\boldsymbol\sigma| = \sum_i\sigma_i$.

## Depends on

- [Gamma duality for the Wright-Fisher diffusion with genic selection](gamma-duality-for-the-wright-fisher-diffusion-with-genic-selection.md)
- [Transition density of the multi-allelic Wright-Fisher diffusion with selection](multi-allelic-transition-density-with-selection.md)

## Expansion

Duality gives the exponentially tilted moments $\mathbb E[e^{-\langle\boldsymbol\sigma,\mathbf X_t\rangle}\mathbf X_t^{\mathbf n}]$ of the time-$t$ law in terms of the dual started at $\mathbf n$. Starting the dual from its entrance boundary in direction $\mathbf x$ and inverting the tilted moments recovers the law of $\mathbf X_t$ as a mixture over the dual's state $\mathbf l$, each component being the Dirichlet law conjugate to $\mathbf x^{\mathbf l}$. Because every component is a standard Dirichlet, no selection-dependent normalizing constant has to be computed, in contrast with the Barbour-Ethier-Griffiths expansion whose components are tilted laws $\Pi^{\boldsymbol\sigma}_{\boldsymbol\alpha+\mathbf l}$. As $t \downarrow 0$ the total size of the dual started from infinity is asymptotically normal around an explicit deterministic curve $v(t)$ (extending a result of Griffiths for the neutral line-count process), which supports simulation of the weights at small times.

## Sources

- J. Sant, P. A. Jenkins and M. Ruggiero, "A tractable transition function for the Wright-Fisher diffusion with selection via gamma duality", arXiv preprint (2026), Proposition 3.6, Theorem 3.7, Theorem 4.1 and Proposition 4.4. <https://doi.org/10.48550/arXiv.2611.08623>