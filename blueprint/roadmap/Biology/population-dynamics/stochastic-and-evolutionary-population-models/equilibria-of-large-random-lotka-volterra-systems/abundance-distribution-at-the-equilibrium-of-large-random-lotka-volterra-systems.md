# Abundance distribution at the equilibrium of large random Lotka–Volterra systems

**Model.** The abundances $\mathbf x_N(t)\in(0,\infty)^N$ of $N$ interacting species follow

$$\frac{d\mathbf x_N}{dt}=\mathbf x_N\odot\big(\mathbf r_N-(I_N-\Sigma_N)\mathbf x_N\big),$$

with intrinsic growth rates $\mathbf r_N\ge0$ independent of the random interaction matrix $\Sigma_N$, and empirical law of $\mathbf r_N$ converging (in Wasserstein-2) to $\bar\mu\neq\delta_0$. When $\|\Sigma_N\|<1$ there is a unique globally stable equilibrium $\mathbf x^\star_N$, the solution of the linear complementarity problem $\mathbf x\ge0$, $(I-\Sigma_N)\mathbf x-\mathbf r_N\ge0$, $\mathbf x\odot((I-\Sigma_N)\mathbf x-\mathbf r_N)=0$; some coordinates may vanish ($x^\star_i=0$), and whether any does depends on $\mathbf r_N$ and $\Sigma_N$ (for $\Sigma_N=0$ and $\mathbf r_N=\mathbf 1$, $\mathbf x^\star_N=\mathbf 1$). The theorem below describes the proportion of surviving species as $N\to\infty$.

**Theorem (GOE interactions).** Let $\Sigma_N=A_N/(\kappa\sqrt N)$ with $A_N$ from the Gaussian Orthogonal Ensemble and $\kappa>2$. Let $\bar r\sim\bar\mu$ and $\bar Z\sim\mathcal N(0,1)$ be independent. The system

$$\kappa=\delta+\frac\gamma\delta,\qquad \sigma^2=\frac1{\delta^2}\mathbb E\big(\sigma\bar Z+\bar r\big)_+^2,\qquad \gamma=\mathbb P\big[\sigma\bar Z+\bar r>0\big]$$

has a unique solution $(\delta,\sigma,\gamma)\in(1/\sqrt2,\infty)\times(0,\infty)\times(0,1)$ (for any $\kappa>\sqrt2$), and almost surely the empirical distribution of the equilibrium abundances converges in Wasserstein-2:

$$\frac1N\sum_{i=1}^N\delta_{x^\star_i}\ \longrightarrow\ \mathcal L\Big(\big(1+\gamma/\delta^2\big)\big(\sigma\bar Z+\bar r\big)_+\Big).$$

In particular the fraction of surviving species tends to $\gamma$, and surviving abundances follow a truncated, shifted Gaussian mixture.

**Theorem (Wishart interactions).** Let $\Sigma_N=B_N^TB_N/(\kappa P)$ with $B_N$ a $P\times N$ standard Gaussian matrix, $N/P\to c\in(0,\infty)$ and $\kappa>(1+\sqrt c)^2$. With $(\delta,\tau,\gamma)$ the unique solution of

$$\kappa=(\delta+c\gamma)\Big(1+\frac1\delta\Big),\qquad \tau^2=\frac c{\delta^2}\mathbb E\big(\tau\bar Z+\bar r\big)_+^2,\qquad \gamma=\mathbb P\big[\tau\bar Z+\bar r>0\big],$$

the empirical law of $\mathbf x^\star_N$ converges almost surely to $\mathcal L\big((1+1/\delta)(\tau\bar Z+\bar r)_+\big)$.

## Expansion

The equilibrium is the fixed point of a projection onto the positive orthant, $\mathbf x=(\mathbf r+\Sigma\mathbf x)_+$, which is the form handled by Approximate Message Passing (AMP). An AMP iteration $\mathbf x^{t+1}=(\mathbf r+\Sigma\mathbf x^t-\text{Onsager correction})_+$ has, by state evolution, iterates whose empirical law is that of $(\sigma_t\bar Z+\bar r)_+$ up to scaling; the fixed point of the state evolution is the system above, with $\gamma$ the fraction of active coordinates entering the Onsager term. One then shows that the AMP iterates converge to the true LCP solution, so the empirical law of $\mathbf x^\star_N$ inherits the state-evolution limit. The condition $\kappa>2$ ensures $\|\Sigma_N\|<1$ (the GOE spectrum lies in $[-2,2]$), hence existence, uniqueness and global stability; these equations had been predicted by the cavity method in physics, and this is their first rigorous derivation.

## Sources

- Imane Akjouj, Walid Hachem, Mylène Maïda and Jamal Najim, "Equilibria of large random Lotka–Volterra systems with vanishing species: a mathematical approach", Journal of Mathematical Biology 89 (2024), 61, <https://doi.org/10.1007/s00285-024-02155-z>; numbering as in arXiv:2302.07820: Section 2 (Assumptions 1–5, Theorem 1 for the GOE case, Theorem 2 for the Wishart case, Theorems 3–4 on non-Gaussian universality).
