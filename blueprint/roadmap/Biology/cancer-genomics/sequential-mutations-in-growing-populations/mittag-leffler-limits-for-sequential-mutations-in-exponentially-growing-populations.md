# Mittag-Leffler limits for sequential mutations in exponentially growing populations

**Model.** Cells of type $n$ (carrying $n-1$ sequential mutations) divide at rate $\alpha_n$, die at rate $\beta_n$, and produce a type-$(n+1)$ daughter at rate $\nu_n$:
$$(n)\to(n)(n)\ \text{at }\alpha_n,\qquad (n)\to\varnothing\ \text{at }\beta_n,\qquad (n)\to(n)(n+1)\ \text{at }\nu_n .$$
The process starts from one type-1 cell, with $\lambda_1=\alpha_1-\beta_1>0$, conditioned on survival. Let $\lambda_n=\alpha_n-\beta_n$ be the net growth rates (of any sign for $n\ge2$), $\delta_n=\max_{i\le n}\lambda_i$ the running-maximum fitness, and $r_n=\#\{i\le n:\lambda_i=\delta_n\}$ the number of times it is attained. Let $Z_n(t)$ be the number of type-$n$ cells.

**Theorem.**

1. For each $n$ there is a $(0,\infty)$-valued random variable $V_n$ with
$$\lim_{t\to\infty}t^{-(r_n-1)}e^{-\delta_nt}Z_n(t)=V_n\quad\text{a.s.},$$
and $V_1\sim\mathrm{Exp}(\lambda_1/\alpha_1)$.
2. If the running maximum does not increase at step $n+1$, then $V_{n+1}$ is a deterministic multiple of $V_n$: $V_{n+1}=\frac{\nu_n}{\delta_n-\lambda_{n+1}}V_n$ if $\delta_n>\lambda_{n+1}$, and $V_{n+1}=\frac{\nu_n}{r_n}V_n$ if $\delta_n=\lambda_{n+1}$.
3. In the small-mutation limit $\nu_1,\dots,\nu_n\to0$, with $V_n$ suitably rescaled, $V_n$ is Mittag-Leffler distributed with tail index $\lambda_1/\delta_n\in(0,1]$ and scale $\omega_n$:
$$\mathbb E\,e^{-\theta V_n}=\frac{1}{1+(\omega_n\theta)^{\lambda_1/\delta_n}} .$$
Here $\omega_1=\alpha_1/\lambda_1$. The recursion multiplies $\omega_n$ by $\nu_n/(\delta_n-\lambda_{n+1})$ or by $\nu_n/r_n$ when the running maximum stays or is matched. When the maximum increases, the recursion is $\omega_{n+1}=[c_n\nu_n(\log\nu_n^{-1})^{r_n-1}\omega_n]^{\lambda_{n+1}/\delta_n}$ with an explicit constant $c_n$.

## Expansion

Type-$(n+1)$ cells are seeded by a Poisson process with intensity $\nu_nZ_n(t)\approx\nu_nV_nt^{r_n-1}e^{\delta_nt}$. Each seed founds an independent birth–death clone. If the new type is no fitter than the current maximum, the immigrants dominate and their clones only add a deterministic factor, which gives perfect correlation of $V_{n+1}$ with $V_n$. If it is fitter, the earliest seeds dominate. The sum over a Poisson number of exponentially growing clones started at random early times gives a stable-type law, and the Mittag-Leffler distribution with index $\lambda_1/\delta_n$ appears. For index below $1$ it has infinite mean, which explains the huge variability between replicate populations (jackpots, as in Luria–Delbrück). The same scaling gives the distribution of the arrival time $\tau_n$ of the first type-$n$ cell. This applies to driver-mutation accumulation in tumours and to neoantigen accumulation with fitness costs.

## Sources

- M. D. Nicholson, D. Cheek, T. Antal, "Sequential mutations in exponentially growing populations", arXiv:2208.02088 (2022): Section 2 (model), Section 3 (Mittag-Leffler law and recursion for $\omega_n$), Proposition 5.1 and Lemma 5.3 (almost sure limits), Corollary 5.4 (perfect correlation), Corollary 5.6 and Proposition 5.7 (small-mutation Laplace transforms). <https://doi.org/10.48550/arXiv.2208.02088>
