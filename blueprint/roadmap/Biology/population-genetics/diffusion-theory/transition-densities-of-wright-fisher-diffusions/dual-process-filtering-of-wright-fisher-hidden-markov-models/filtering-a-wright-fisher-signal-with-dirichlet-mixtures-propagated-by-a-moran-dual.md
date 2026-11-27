# Filtering a Wright–Fisher signal with Dirichlet mixtures propagated by a Moran dual

Let $X_t$ be the $K$-type Wright–Fisher diffusion on the simplex $\Delta_K$ with parent-independent mutation, generator

$$
\mathcal A=\frac12\sum_{i,j=1}^Kx_i(\delta_{ij}-x_j)\partial_{x_i}\partial_{x_j}+\frac12\sum_{i=1}^K(\alpha_i-\theta x_i)\partial_{x_i},\qquad \theta=\sum_i\alpha_i,
$$

and stationary law $\mathrm{Dir}(\boldsymbol\alpha)$. A process $D_t$ is dual to $X_t$ with duality function $h$ if $\mathbb E[h(X_t,d)\mid X_0=x]=\mathbb E[h(x,D_t)\mid D_0=d]$.

**Moran duality.** Let $N_t\in\mathbb Z_+^K$ be the Moran-type chain that jumps from $\mathbf n$ to $\mathbf n-\mathbf e_i+\mathbf e_j$ at rate $n_i(\alpha_j+n_j)/2$, and let

$$
h(\mathbf x,\mathbf n)=\frac{\Gamma(\theta+|\mathbf n|)}{\Gamma(\theta)}\prod_{i=1}^K\frac{\Gamma(\alpha_i)}{\Gamma(\alpha_i+n_i)}x_i^{n_i},
$$

so that $h(\cdot,\mathbf n)\pi_{\boldsymbol\alpha}=\pi_{\boldsymbol\alpha+\mathbf n}$. Then the duality identity holds with $D_t=N_t$. The chain conserves $|\mathbf n|$.

**Filtering recursion.** Suppose the signal is observed at times spaced $\Delta$ apart through categorical (multinomial) samples. If the current filter is a finite mixture of Dirichlet laws $\sum_{\mathbf m}w_{\mathbf m}\pi_{\boldsymbol\alpha+\mathbf m}$, then:

- **Prediction.** Propagating over time $\Delta$ gives another such mixture, with weights $w'_{\mathbf n}=\sum_{\mathbf m}w_{\mathbf m}p_{\mathbf m,\mathbf n}(\Delta)$, where $p_{\mathbf m,\mathbf n}$ are the transition probabilities of the dual chain.
- **Update.** Conditioning on an observation $y$ with type counts $\mathbf y$ maps component $\mathbf m$ to $\mathbf m+\mathbf y$, with weight proportional to $w_{\mathbf m}\mu_{\mathbf m}(y)$, where $\mu_{\mathbf m}(y)=\int f_x(y)\pi_{\boldsymbol\alpha+\mathbf m}(x)\,dx$ is the Dirichlet–multinomial marginal.

So the exact filter stays a finite Dirichlet mixture indexed by dual states. Using the Moran dual, which preserves total size, instead of the Kingman death-process dual, which loses lineages, keeps the support bounded and makes accurate approximate filters cheap.

## Depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)
- [The Dirichlet law is stationary for parent-independent mutation](../../wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md)
- [Dirichlet–multinomial conjugacy](../../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/with-density-prod-pow-dirichlet-measure.md)

## Expansion

Duality turns the propagation of $h(\cdot,\mathbf m)\pi_{\boldsymbol\alpha}$ by the signal semigroup into a finite-state expectation over the dual. Reversibility of $\pi_{\boldsymbol\alpha}$ moves the semigroup onto $h$, and the duality identity then moves it onto the dual chain. Updates are Dirichlet–multinomial conjugacy. The same construction gives a birth-and-death dual for the Cox–Ingersoll–Ross diffusion with gamma mixtures.

## Sources

- Guillaume Kon Kam King, Andrea Pandolfi, Marco Piretto and Matteo Ruggiero, "Approximate filtering via discrete dual processes", *Stochastic Processes and their Applications* 168 (2024), 104268, <https://doi.org/10.1016/j.spa.2023.104268>. Numbering as in the preprint arXiv:2310.00599v2, <https://arxiv.org/abs/2310.00599v2>: Proposition 2.1, Corollary 3.1, Section 5 (generator, Proposition 5.1).
