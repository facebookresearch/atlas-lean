# Mittag-Leffler limits for sequential mutations in exponentially growing populations

**Model.** Cells of type $n$ (carrying $n-1$ sequential mutations) divide at rate $\alpha_n$, die at rate $\beta_n$, and produce a type-$(n+1)$ daughter at rate $\nu_n$:

$$(n)\to(n)(n)\ \text{at }\alpha_n,\qquad (n)\to\varnothing\ \text{at }\beta_n,\qquad (n)\to(n)(n+1)\ \text{at }\nu_n .$$

The process starts from one type-1 cell, with $\lambda_1=\alpha_1-\beta_1>0$, conditioned on survival. Let $\lambda_n=\alpha_n-\beta_n$ be the net growth rates (of any sign for $n\ge2$), $\delta_n=\max_{i\le n}\lambda_i$ the running-maximum fitness, and $r_n=\#\{i\le n:\lambda_i=\delta_n\}$ the number of times it is attained. Let $Z_n(t)$ be the number of type-$n$ cells.

**Theorem.**

1. For each $n$ there is a $(0,\infty)$-valued random variable $V_n$ with

$$\lim_{t\to\infty}t^{-(r_n-1)}e^{-\delta_nt}Z_n(t)=V_n\quad\text{a.s.},$$

and $V_1\sim\mathrm{Exp}(\lambda_1/\alpha_1)$.
2. If the running maximum does not increase at step $n+1$, then $V_{n+1}$ is a deterministic multiple of $V_n$: $V_{n+1}=\frac{\nu_n}{\delta_n-\lambda_{n+1}}V_n$ if $\delta_n>\lambda_{n+1}$, and $V_{n+1}=\frac{\nu_n}{r_n}V_n$ if $\delta_n=\lambda_{n+1}$.
3. *(Approximate model.)* Let $V_n^*$ be the amplitudes of the approximate model: $V_1^* = V_1$, and given $V_n^*$, type-$(n+1)$ clones are founded at the points of a Poisson process of rate $\nu_nV_n^*t^{r_n-1}e^{\delta_nt}$ and then evolve as independent birth–death processes with rates $\alpha_{n+1},\beta_{n+1}$; $V_{n+1}^* = \lim_{t\to\infty}t^{-(r_{n+1}-1)}e^{-\delta_{n+1}t}Z_{n+1}^*(t)$. Put $f_i(\nu_i) = \nu_i^{-1}$ if $\lambda_{i+1} \le \delta_i$ and $f_i(\nu_i) = \nu_i^{-1}(\log\nu_i^{-1})^{-(r_i-1)}$ if $\lambda_{i+1} > \delta_i$, $F_n(\nu) = \prod_{i=1}^nf_i(\nu_i)^{\delta_{n+1}/\delta_i}$, and $\kappa_i = (\delta_i - \lambda_{i+1})^{-1}$ if $\delta_i > \lambda_{i+1}$, $\kappa_i = r_i^{-1}$ if $\delta_i = \lambda_{i+1}$, and $\kappa_i$ the explicit constant of the source's equation (16) if $\delta_i < \lambda_{i+1}$. Then for $\theta \ge 0$

$$\lim_{\nu_1\to0}\cdots\lim_{\nu_n\to0}\mathbb E\exp\big(-\theta F_n(\nu)V_{n+1}^*\big) = \Big(1 + \frac{\alpha_1}{\lambda_1}\,\theta^{\lambda_1/\delta_{n+1}}\prod_{i=1}^n\kappa_i^{\lambda_1/\delta_i}\Big)^{-1},$$

so $F_n(\nu)V_{n+1}^*$ converges in law to a Mittag-Leffler distribution with tail index $\lambda_1/\delta_{n+1} \in (0,1]$. The source conjectures, but does not prove, that the amplitudes $V_{n+1}$ of the original model have the same small-mutation limit; this is known for two types.

## Proof sketch

Type-$(n+1)$ cells are seeded by a Poisson process with intensity $\nu_nZ_n(t)\approx\nu_nV_nt^{r_n-1}e^{\delta_nt}$. Each seed founds an independent birth–death clone. If the new type is no fitter than the current maximum, the immigrants dominate and their clones only add a deterministic factor, which gives perfect correlation of $V_{n+1}$ with $V_n$. If it is fitter, the earliest seeds dominate. The sum over a Poisson number of exponentially growing clones started at random early times gives a stable-type law, and the Mittag-Leffler distribution with index $\lambda_1/\delta_n$ appears. For index below $1$ it has infinite mean, which explains the huge variability between replicate populations (jackpots, as in Luria–Delbrück). The same scaling gives the distribution of the arrival time $\tau_n$ of the first type-$n$ cell. This applies to driver-mutation accumulation in tumours and to neoantigen accumulation with fitness costs.

## Sources

- Michael D. Nicholson, David Cheek and Tibor Antal, "Sequential mutations in exponentially growing populations", *PLOS Computational Biology* 19 (2023), e1011289, <https://doi.org/10.1371/journal.pcbi.1011289>. Preprint version: arXiv:2208.02088 (2022), Section 2 (model), Section 3 (Mittag-Leffler law and recursion for $\omega_n$), Proposition 5.1 and Lemma 5.3 (almost sure limits), Corollary 5.4 (perfect correlation), Section 5.2 (approximate model), Corollary 5.6 and Proposition 5.7 (small-mutation Laplace transforms), <https://doi.org/10.48550/arXiv.2208.02088>.
