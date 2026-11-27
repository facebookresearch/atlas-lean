# Ewens law of latent mutations of a rare selected allele

**Setting.** A haploid population has two alleles $A_1,A_2$ at one locus with recurrent mutation and genic selection. The frequency $X$ of $A_1$ follows

$$dX=\Big[\tfrac{\theta_1}{2}(1-X)-\tfrac{\theta_2}{2}X+\tfrac{\alpha}{2}X(1-X)\Big]dt+\sqrt{X(1-X)}\,dW$$

at stationarity ($\alpha>0$ favours $A_1$). A sample of size $n=n_1+n_2$ has $n_1$ copies of $A_1$. Backward in time, conditional on the sample, the background frequency $p_t$ is the time-reversed diffusion, $A_1$ lineages coalesce at rate $\binom{a_1}{2}/p_t$ and undergo a latent mutation (are traced to an $A_2$ ancestor) at rate proportional to $\theta_1(1-p_t)/p_t$ per lineage, with symmetric rules for $A_2$ (coalescence in a random background). $K_1$ is the total number of latent mutations in the ancestry of the $n_1$ copies of $A_1$, and $\tau_{n_1}$ the time of the oldest one.

**Statements.**
1. *(Strong selection, fixed sample.)* With $(n_1,n_2)$ fixed and $\alpha\to\infty$: $p_t\to1$ uniformly on compacts, $K_1\to1$ and $K_2\to\sum_{k=1}^{n_2}\zeta_k$ with independent $\zeta_k\sim$ Bernoulli$\big(\frac{\theta_2}{\theta_2+k-1}\big)$, and $\tau_{n_1}/\alpha\to\mathrm{Exp}$ with mean $\frac{2}{\theta_1\theta_2}$.
2. *(Large samples, moderate selection.)* With $n_1$ fixed, $n\to\infty$ and $\tilde\alpha=\alpha/n_2\in(-\infty,1)$ fixed, the rescaled background $np_{t/n}$ converges to a diffusion $Z$ started from Gamma$(n_1+\theta_1,1-\tilde\alpha)$, the rescaled event times converge jointly, and

$$K_1\ \xrightarrow{d}\ 1+\sum_{k=2}^{n_1}\xi_k,\qquad \xi_k\sim\mathrm{Bernoulli}\Big(\frac{\theta_1}{\theta_1+k-1}\Big)\ \text{independent},$$

the number of alleles in an Ewens sample of size $n_1$ with parameter $\theta_1$: the same law as for a rare neutral allele, even for $\alpha\to\pm\infty$ as long as $\alpha/n_2<1$.
3. *(Strong positive selection relative to sample size.)* If $\tilde\alpha=\alpha/n_2>1$, then $p_t\to1$ on $[S,T]$, the $A_1$ lineages coalesce as Kingman's coalescent, $K_1\to1$ in probability, and $\tau_{n_1}/n\to\mathrm{Exp}$ with mean $2\tilde\alpha/(\theta_1\theta_2)$.

## Depends on

- [Absorption time of the Wright-Fisher diffusion](../../../population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md)
- [Kingman's coalescent](../../coalescents/merger-rate-dirac-zero.md)

## Expansion

Given $n_1$ copies of $A_1$ among $n$, the posterior frequency of $A_1$ is of order $n_1/n$, so on the time-scale $1/n$ the background $np$ is a branching-type diffusion and both coalescence ($\binom{a}{2}/p$) and latent mutation ($\theta_1/p$ per lineage) are accelerated by the same factor $1/p$. Their ratio, $\binom{a}{2}$ versus $a\theta_1/2$, is exactly the ratio in Hoppe's urn, so the sequence of coalescence and mutation events is that of the Ewens sampling formula regardless of the background path; selection only changes the time change, as long as the posterior frequency stays small, which is the condition $\alpha/n_2<1$. When $\alpha/n_2>1$ the favoured allele is common in the population despite being rare in the sample, the background frequency is near $1$, mutation into $A_1$ is negligible compared with coalescence, and a single origin remains.

## Sources

- Wai-Tong Louis Fan and John Wakeley, "Latent mutations in the ancestries of alleles under selection", Theor. Popul. Biol. 158 (2024), 1–20, <https://doi.org/10.1016/j.tpb.2024.04.008>. Numbering follows the arXiv version, arXiv:2306.08142 (2023): Proposition 1, Theorems 1–6, <https://doi.org/10.48550/arXiv.2306.08142>.
