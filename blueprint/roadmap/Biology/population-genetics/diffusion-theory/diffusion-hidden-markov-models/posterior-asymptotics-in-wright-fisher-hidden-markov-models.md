# Posterior asymptotics in Wright-Fisher hidden Markov models

**Setting.** Let $\Delta_d$ be the probability simplex in $\mathbb R^d$, $\alpha=(\alpha_1,\dots,\alpha_d)\in(0,\infty)^d$ and $\theta=\sum_j\alpha_j$. The latent signal $X=(X_t)_{t\ge0}$ is the neutral $d$-type Wright-Fisher diffusion with parent-independent mutation, with generator

$$\mathcal Af(x)=\tfrac12\sum_{j}(\alpha_j-\theta x_j)\,\partial_jf(x)+\tfrac12\sum_{j,\ell}x_j(\delta_{j\ell}-x_\ell)\,\partial_j\partial_\ell f(x),$$

stationary and reversible with respect to the Dirichlet law $\mathrm{Dir}(\alpha)$ and started from it. At inspection times $t_1<\dots<t_k$ one observes $n$ categorical draws $Y_i^{(n)}$ which, given $X_{t_i}=x$, are i.i.d. with law $x$; $\hat x_i$ denotes the empirical type frequencies at time $t_i$ and $h_i=t_i-t_{i-1}$. By duality with Kingman's coalescent, all predictive and smoothing posteriors are finite or countable mixtures of Dirichlet laws. Write $P_{h}(\cdot\mid x)$ for the transition law of $X$ over time $h$ and $d_{\mathrm{TV}}$ for total variation.

**Proposition 3.1 (dual death process tail).** Let $p_{n,k}(t)$ be the probability that the block-counting process of Kingman's coalescent started from $n\le\infty$ lineages has $k$ lineages at time $t$. For each $t>0$ there are $c,R>0$ such that $\sum_{k>M}p_{n,k}(t)\le Re^{-cM^2t}$ for all $n$ and $M\ge0$.

**Theorem 3.2 and Corollary 3.3 (prediction).** There are constants $L_{h}$ such that, for every $i=2,\dots,k$, almost surely,

$$d_{\mathrm{TV}}\bigl(\mathcal L(X_{t_i}\mid Y_{i-1}^{(n)}),\,P_{h_i}(\cdot\mid\hat x_{i-1})\bigr)\le L_{h_i}\left(\frac{2\theta}{n+\theta}+\sqrt{\frac{d}{n+\theta+1}}\right).$$

If the data at time $t_{i-1}$ are generated i.i.d. from a fixed composition $x^*_{i-1}$, the one-step predictive law converges in total variation to $P_{h_i}(\cdot\mid x^*_{i-1})$ (Corollary 3.5), and the same holds when conditioning on all past data (Proposition 3.8).

**Theorem 3.9 (joint consistency and Bernstein-von Mises).** If the data at each $t_i$ are i.i.d. from fixed $x_i^*\in\Delta_d$, then the joint posterior of $(X_{t_1},\dots,X_{t_k})$ converges weakly to $\delta_{x_1^*}\otimes\cdots\otimes\delta_{x_k^*}$ almost surely. Split each $x_i^*=(x_i^{*+},0)$ into its $r_i$ positive coordinates and its zero coordinates, and similarly $X_{t_i}=(X_i^+,X_i^0)$. Then, in probability, the posterior law of $(\sqrt n(X_i^+-\hat x_i^+))_{i\le k}$ converges to $\mathcal N(0,\Sigma^+)$ with $\Sigma^+=\mathrm{diag}(\Sigma_1^+,\dots,\Sigma_k^+)$, $\Sigma_i^+=\mathrm{diag}(x_i^{*+})-x_i^{*+}x_i^{*+\top}$, while the posterior law of $(nX_i^0)_{i\le k}$ converges to independent $\Gamma(\alpha_j,1)$ coordinates, jointly with the Gaussian part.

## Depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)
- [The Dirichlet law is stationary for parent-independent mutation](../wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md)
- [Generator of Kingman's block-counting process](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md)

## Proof idea

Given $Y_{i-1}^{(n)}$, the posterior at $t_{i-1}$ is $\mathrm{Dir}(\alpha+n\hat x_{i-1})$, whose mean is within $2\theta/(n+\theta)$ of $\hat x_{i-1}$ and whose spread is of order $\sqrt{d/(n+\theta+1)}$; pushing it through the transition kernel, which is Lipschitz from $\ell^1$ to total variation with constant $L_{h}$ for $h>0$, gives the prediction bound. The Gaussian tail of the dual death process makes the Dirichlet mixtures effectively finite, uniformly in $n$. With large samples at every time, the likelihood dominates the transition kernel, so the posteriors decouple across times: interior coordinates behave like the multinomial MLE with the usual $\sqrt n$ Gaussian limit, and coordinates at the boundary of the simplex retain the Dirichlet prior shape, giving $1/n$-scale Gamma limits.

## Sources

- L. M. Malgieri, F. Ascolani, M. Giordano and M. Ruggiero, "Asymptotics and finite-sample bounds for prediction and smoothing in Wright–Fisher hidden Markov models", Bayesian Analysis (2026), advance publication, <https://doi.org/10.1214/26-BA1627>. Numbering as in the preprint arXiv:2609.22444v3, <https://arxiv.org/abs/2609.22444v3>: Proposition 3.1, Theorem 3.2, Corollaries 3.3 and 3.5, Proposition 3.8, Theorem 3.9.
