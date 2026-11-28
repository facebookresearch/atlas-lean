# Bayesian variable selection regression model

Let $y\in\mathbb{R}^n$ be phenotypes and $X=(x_{\cdot1},\dots,x_{\cdot p})\in\mathbb{R}^{n\times p}$ genotypes (allele counts), typically with $p\gg n$. Introduce inclusion indicators $\gamma=(\gamma_1,\dots,\gamma_p)\in\{0,1\}^p$ and write $X_\gamma$, $\beta_\gamma$ for the columns and coefficients with $\gamma_j=1$, and $|\gamma|=\sum_j\gamma_j$. Bayesian variable selection regression (BVSR) is the hierarchical model

$$y\mid\gamma,\mu,\tau,\beta,X\sim N_n\bigl(\mu\mathbf 1+X_\gamma\beta_\gamma,\ \tau^{-1}I_n\bigr),$$

$$\tau\sim\mathrm{Gamma}(\lambda/2,\kappa/2),\quad \mu\mid\tau\sim N(0,\sigma_\mu^2/\tau),\quad \gamma_j\overset{\text{iid}}{\sim}\mathrm{Bernoulli}(\pi),$$

$$\beta_\gamma\mid\tau,\gamma\sim N_{|\gamma|}\bigl(0,(\sigma_a^2/\tau)I_{|\gamma|}\bigr),\qquad \beta_{-\gamma}\mid\gamma\sim\delta_0,$$

with the limits $\sigma_\mu^2\to\infty$ and $\lambda,\kappa\to0$ taken in the posterior (equivalently the improper prior $p(\mu,\tau)\propto1/\tau$), so that posterior odds between models $\gamma$ are invariant to shifting and scaling $y$. The sparsity hyperparameter gets a log-uniform prior

$$\log\pi\sim U\bigl(\log(1/p),\ \log(M/p)\bigr),$$

so the expected number of included variants ranges from $1$ to $M$. The **posterior inclusion probability** of variant $j$ is $\Pr(\gamma_j=1\mid y)$, estimated from MCMC draws $\theta^{(i)}$, $i=1,\dots,M_{\mathrm{mc}}$, by the Rao–Blackwellized average

$$\Pr(\gamma_j=1\mid y)\approx\frac1{M_{\mathrm{mc}}}\sum_{i=1}^{M_{\mathrm{mc}}}\Pr\bigl(\gamma_j=1\mid y,\gamma_{-j}^{(i)},\beta_{-j}^{(i)},\tau^{(i)},h^{(i)},\pi^{(i)}\bigr).$$

## Expansion

Given $\gamma$ and the hyperparameters, $\beta$ and $\tau$ integrate out analytically (normal–gamma conjugacy), so the sampler only explores $(h,\pi,\gamma)$, where $h$ parameterizes $\sigma_a$ through the prior calibrated by the proportion of variance explained (companion article in this topic). The full conditional of $\gamma_j$ given everything else is a univariate regression of the current residual on $x_{\cdot j}$, so the Rao–Blackwell terms are cheap for all $j$ and have smaller Monte Carlo variance than the raw frequency of $\gamma_j=1$. A uniform prior on $\pi$ itself would put most mass on large models (on $[10^{-5},10^{-3}]$ about $90\%$ above $10^{-4}$), which the log-uniform prior avoids. Independent normal effects are preferred to Zellner's $g$-prior because causal effects need not mimic the correlation of the SNPs.

## Sources

- Y. Guan, M. Stephens, *Bayesian variable selection regression for genome-wide association studies and other large-scale problems*, The Annals of Applied Statistics 5 (2011), 1780–1815, <https://doi.org/10.1214/11-AOAS455>. Section 2, equations (2.1)–(2.8), and Section 3.1, equation (3.2).
