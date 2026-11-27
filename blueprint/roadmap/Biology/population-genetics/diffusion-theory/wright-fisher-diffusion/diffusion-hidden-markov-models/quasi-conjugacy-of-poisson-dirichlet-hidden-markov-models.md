# Quasi-conjugacy of Poisson-Dirichlet hidden Markov models

**Setting.** Let $\nabla_\infty=\{x_1\ge x_2\ge\dots\ge0,\ \sum_i x_i\le1\}$ be the ranked infinite simplex and $\mathrm{PD}=\mathrm{PD}(\sigma,\theta)$ the two-parameter Poisson-Dirichlet law on it ($0\le\sigma<1$, $\theta>-\sigma$). The latent signal $X=(X(t))_{t\ge0}$ is a two-parameter Poisson-Dirichlet diffusion, a stationary reversible Markov process on $\nabla_\infty$ with invariant law $\mathrm{PD}$ (the infinite-alleles limit of Wright-Fisher frequency dynamics, $\sigma=0$ giving the Ethier-Kurtz infinitely-many-neutral-alleles model). At times $t_0<\dots<t_N$ one observes only the unlabelled partition $\Pi^k$ of a sample of size $n_k$ drawn exchangeably from $X(t_k)$ (paintbox sampling): $P(\omega\mid x)$ is the probability of block-size pattern $\omega$ given frequencies $x$, and integrating against $\mathrm{PD}$ gives the Ewens-Pitman sampling formula $\mathrm{psf}(\omega)$. For a partition $\lambda$, $\mathrm{PD}^\lambda$ denotes the posterior of $\mathrm{PD}$ given a sample with unlabelled partition $\lambda$. For partitions $\omega\in\mathcal P_n$, $\gamma\in\mathcal P_m$, $\mathrm{coag}(\omega,\gamma)$ is the set of partitions of $n+m$ obtained by merging blocks of $\omega$ with blocks of $\gamma$.

**Proposition 2 (product expansion).** For all $x\in\nabla_\infty$,

$$P(\omega\mid x)\,P(\gamma\mid x)=\sum_{\mu\in\mathrm{coag}(\omega,\gamma)}H(\omega,\gamma\mid\mu)\,P(\mu\mid x),$$

with explicit combinatorial coefficients $H\ge0$ (Proposition 4). Consequently the conditional predictive law of a further sample is $\Pr(\Pi_{n+1:n+m}=\gamma\mid\Pi_{1:n}=\omega)=\sum_{\mu\in\mathrm{coag}(\omega,\gamma)}H(\omega,\gamma\mid\mu)\,\mathrm{psf}(\mu)/\mathrm{psf}(\omega)$ (Proposition 1).

**Theorem 1 (exact inference).** Let $\mathcal F$ be the family of finite mixtures $\sum_{\lambda\in\Lambda}w_\lambda\,\mathrm{PD}^\lambda$ over finite sets $\Lambda$ of partitions. Then:
1. for every $k\le N$ and $h\ge0$ the filtering law of $X(t_k)$ given $\Pi^{0:k}$ and the forecast law of $X(t_k+h)$ lie in $\mathcal F$, computable recursively: prediction moves the weights by the transition probabilities of a dual partition-valued death process (a Chinese restaurant process with loss of customers), and updating with $\Pi^k=\pi$ replaces each component $\mathrm{PD}^\omega$ by a mixture over $\mathrm{coag}(\omega,\pi)$ (Theorems 2 and 3);
2. for every $k<N$ the smoothing law of $X(t_k)$ given $\Pi^{0:N}$ lies in $\mathcal F$ (Theorem 4);
3. the law of a new partition observed at any time $t$, given $\Pi^{0:N}$, is a finite mixture of conditional Ewens-Pitman sampling formulae (Corollary 3).

Forecasts converge to $\mathrm{PD}$ in total variation as the horizon grows (Corollary 1).

## Proof idea

The model is *quasi-conjugate*: without data $X(t)\sim\mathrm{PD}$, and each observed partition maps $\mathrm{PD}^\omega$ into finitely many components $\mathrm{PD}^\mu$, because the likelihood of a new partition given the current mixture component is a product of two sampling probabilities and the product expansion rewrites it as a finite combination of single sampling probabilities. Between observations, duality says that the diffusion acts on $\mathrm{PD}^\lambda$ by randomly deleting sampled individuals from $\lambda$ through the dual death process, which only reaches the finitely many sub-partitions of $\lambda$. Closure of $\mathcal F$ under both operations gives exact filtering with no need to enumerate type labels; smoothing combines this forward pass with a backward cost-to-go recursion of the same form (Proposition 6).

## Sources

- M. Dalla Pria, M. Ruggiero and D. Spanò, "Exact inference via quasi-conjugacy in two-parameter Poisson–Dirichlet hidden Markov models", Journal of the American Statistical Association (2026), 1–12, <https://doi.org/10.1080/01621459.2026.2676717>. Numbering as in the preprint arXiv:2512.22098v4, <https://arxiv.org/abs/2512.22098v4>: Propositions 1, 2, 4 and 6, Theorems 1–4, Corollaries 1 and 3.
