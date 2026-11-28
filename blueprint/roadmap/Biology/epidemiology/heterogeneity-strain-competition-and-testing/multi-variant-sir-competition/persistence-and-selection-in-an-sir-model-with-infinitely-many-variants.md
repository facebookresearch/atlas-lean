# Persistence and selection in an SIR model with infinitely many pathogen variants

**Model.** A host population with susceptibles $S(t)$ is infected by countably many pathogen variants $n \in \mathbb{N}$ with infected densities $I_n(t)$:

$$S'(t) = \Lambda - \theta S(t) - \sum_{k\ge0}\beta_k S(t) I_k(t), \qquad I_n'(t) = \beta_n S(t) I_n(t) - \gamma_n I_n(t),$$

with $S(0) = S_0 > 0$ and $(I_n(0)) = (I^0_n) \in \ell^1_+$. Here $\Lambda, \theta > 0$ are recruitment and natural death, and $0 < \beta_0 \le \beta_n \le \beta^\infty$, $0 < \gamma_0 \le \gamma_n \le \gamma^\infty$ are the transmission and recovery rates of variant $n$ (no mutation between variants). Define the maximal fitness and basic reproduction number

$$\alpha^* = \sup_n \frac{\beta_n}{\gamma_n}, \qquad \mathcal{R}_0 = \frac{\Lambda}{\theta}\alpha^*.$$

Assume that $\alpha^*$ is approached by initially present variants ($I^0_{n_k} > 0$ with $\beta_{n_k}/\gamma_{n_k} \to \alpha^*$) and that the sequences $(\gamma_n)$ and $(\beta_n/\gamma_n)$ have finite $\omega$-limit sets.

**Theorem.**

1. *(Well-posedness.)* The system has a unique global classical solution in $C^1([0,\infty); \mathbb{R}\times\ell^1_+)$ depending continuously on the initial data.
2. *(Extinction.)* If $\mathcal{R}_0 < 1$, or $\mathcal{R}_0 = 1$ (under the finite-$\omega$-limit assumption), then $\sum_n I_n(t) \to 0$.
3. *(Persistence.)* If $\mathcal{R}_0 > 1$, then $S(t) \to 1/\alpha^*$ and:
   - if the maximum is attained, $\beta_i/\gamma_i = \alpha^*$ for some $i$, then $I_n(t)$ converges in $\ell^1$ to $I^\infty_n = 0$ when $\beta_n/\gamma_n < \alpha^*$ and $I^\infty_n = e^{\tau\gamma_n} I^0_n$ when $\beta_n/\gamma_n = \alpha^*$, where $\tau \in \mathbb{R}$ is the unique solution of $\sum_{\{n: \beta_n/\gamma_n = \alpha^*\}} \gamma_n I^0_n e^{\tau\gamma_n} = \frac{\theta}{\alpha^*}(\mathcal{R}_0 - 1)$;
   - if no variant attains $\alpha^*$, then every $I_n(t) \to 0$ while $\liminf_t \sum_n I_n(t) > 0$: the infection persists by escaping to ever-fitter variants, and any family of variants with fitness bounded away from $\alpha^*$ dies out.
4. *(Selection of the recovery rate.)* Let $\gamma^*$ be the largest limit of $\gamma_{n_k}$ along subsequences with $\beta_{n_k}/\gamma_{n_k} \to \alpha^*$. If every variant has $\beta_n/\gamma_n < \alpha^*$ and the initial mass near fitness $\alpha^*$ puts a uniformly positive fraction on $\gamma_n \ge \gamma^* - \varepsilon$, then

    $$\lim_{t\to\infty}\sum_n I_n(t) = \frac{\theta}{\alpha^*\gamma^*}(\mathcal{R}_0 - 1),$$

    and variants with $\sup_k \gamma_{n_k} < \gamma^*$ vanish: among near-optimal variants, the fastest-recovering ones win.

## Expansion

Each $I_n$ solves a linear equation, $I_n(t) = I^0_n \exp\big(\beta_n\int_0^t S - \gamma_n t\big) = I^0_n\exp\big(\gamma_n(\alpha_n\int_0^t S - t)\big)$ with $\alpha_n = \beta_n/\gamma_n$, so variants are ranked by fitness $\alpha_n$. Persistence forces $\int_0^t S \approx t/\alpha^* + \tau$, which kills every variant with $\alpha_n < \alpha^*$ exponentially, at a rate that becomes arbitrarily slow as $\alpha_n \to \alpha^*$; when the supremum is not attained the mass drifts to infinity in $n$. At equilibrium $\sum_n\beta_n I_n = \theta(\mathcal{R}_0 - 1)$, and since $\beta_n \approx \alpha^*\gamma_n$ for surviving mass, total prevalence is set by the recovery rate the surviving mass concentrates on. A Lyapunov functional $\sum_n I^*_n g(I_n/I^*_n) + S^* g(S/S^*)$, $g(x) = x - \ln x$, yields convergence to stationary states.

## Sources

- Jean-Baptiste Burie, Arnaud Ducrot and Quentin Griette, "Asymptotic behavior of an epidemic model with infinitely many variants", Journal of Mathematical Biology 87 (2023), 40, <https://doi.org/10.1007/s00285-023-01975-9>; numbering as in arXiv:2305.05699: Section 2 (Assumptions 2.1–2.3, Definition 2.7, Assumption 2.8), Proposition 2.4, Proposition 2.5, Theorem 2.6, Proposition 2.9 and Proposition 5.9.
