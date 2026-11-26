# Truncated Gaussian mixture equilibrium of block-structured random Lotka–Volterra systems

**Model.** Abundances $u\in\mathbb R^n_{\ge0}$ follow $\dot u=u\odot\big(r-(I_n-\Sigma)u\big)$ with growth rates $r$ and random interaction matrix $\Sigma=V^{\odot1/2}\odot X$, where $X$ has $\mathrm{Corr}(X_{ij},X_{ji})=\tau_{ij}$. Species are split into $K$ blocks of sizes $\alpha_1n,\dots,\alpha_Kn$ ($\sum\alpha_k=1$); on block pair $(i,j)$ the variance profile is $s_{ij}^2/n$ and the correlation profile $\rho_{ij}$, with $S=(s_{ij}^2)$ positive and $R=(\rho_{ij})$ symmetric in $[-1,1]$. The equilibrium $u^\star$ solves the linear complementarity problem $u^\star\odot(r-(I-\Sigma)u^\star)=0$, $u^\star\ge0$, together with non-invadability $r-(I-\Sigma)u^\star\le0$ on extinct species.

**Theorem.** Assume $\|S\|_\infty<\frac18$ (maximal row sum) and that, on each block $k$, the empirical measure of $r$ converges in Wasserstein-2 distance to the law of $\bar r_k$. Then the empirical measure of $u^\star$ converges in probability, in Wasserstein-2 distance, to
$$\mu_\infty=\sum_{k=1}^K\alpha_k\,\mathcal L\Big(\frac1{\delta_k^\star}\big(\sigma_k^\star\xi_k+\bar r_k\big)_+\Big),\qquad \xi_k\sim\mathcal N(0,1)\ \text{i.i.d.},$$
where $(\delta^\star,\sigma^\star)$ solves the $2K$ equations
$$1=\delta_i+\sum_{j=1}^K\alpha_j\rho_{ij}s_{ij}s_{ji}\,\frac{\mathbb P(\sigma_j\xi+\bar r_j\ge0)}{\delta_j},\qquad \sigma_i^2=\sum_{j=1}^K\alpha_js_{ij}^2\,\frac{\mathbb E(\sigma_j\xi+\bar r_j)_+^2}{\delta_j^2},\qquad i=1,\dots,K .$$
So each block's survivors are a truncated Gaussian, the surviving fraction of block $i$ is $\mathbb P(\sigma_i\xi+\bar r_i\ge0)$, and the reaction terms $\delta_i$ encode the feedback of correlated interactions.

## Expansion

Approximate message passing for matrices with variance and correlation profiles produces iterates whose empirical laws are described by a scalar Gaussian state evolution per block. An AMP iteration whose fixed point is the LCP solution has state evolution with fixed point $(\delta^\star,\sigma^\star)$: $\sigma_i^2$ is the variance of the field felt by species in block $i$, summing squared abundances of neighbours weighted by variance, and $\delta_i$ is a self-consistent response term in which correlated pairs ($\rho_{ij}\ne0$) feed back through the fraction of surviving species. The condition $\|S\|_\infty<\frac18$ is a sufficient condition used in the proof; simulations match the truncated Gaussian mixture also beyond it. For $K=1$ this reduces to the known single-community cavity solution of random Lotka–Volterra systems.

## Sources

- M. Clenet, M.-Y. Gueddari, "Approximate message passing for block-structured ecological systems", arXiv:2603.01774 (2026), Section 1.2 (model), Section 2 (model setup, Theorem 1, system (FPK)), Appendix (proof), <https://doi.org/10.48550/arXiv.2603.01774>.
