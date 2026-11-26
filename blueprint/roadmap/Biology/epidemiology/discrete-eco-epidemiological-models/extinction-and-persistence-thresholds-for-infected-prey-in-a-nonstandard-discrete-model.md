# Extinction and persistence thresholds for infected prey in a nonstandard discrete model

**Model.** Discretizing a nonautonomous predator–prey model with disease in the prey by Mickens' nonstandard finite-difference method gives, for susceptible prey $S_n$, infected prey $I_n$ and predators $P_n$,
$$\begin{aligned}
S_{n+1}-S_n &= \Lambda_n - \mu_nS_{n+1} - a_n f(S_{n+1},I_n,P_n)P_n - \beta_nS_{n+1}I_n,\\
I_{n+1}-I_n &= \beta_nS_{n+1}I_n - \eta_n g(S_n,I_n,P_n)I_{n+1} - c_nI_{n+1},\\
P_{n+1}-P_n &= (r_n - b_nP_{n+1})P_n + \gamma_na_n f(S_{n+1},I_n,P_n)P_n + \theta_n\eta_n g(S_n,I_n,P_n)I_{n+1},
\end{aligned}$$
with bounded non-negative coefficient sequences, $0 < \mu_n \le c_n$, $\Lambda_n, r_n, b_n$ bounded away from $0$, and general $C^1$ predation functional responses $f$ (on susceptible prey) and $g$ (on infected prey) that are non-increasing in $I$, with $f$ non-decreasing and $g$ non-increasing in $S$.

**Thresholds.** Let $s^*_n$ solve the prey-only equation $s_{n+1} = (\Lambda_n + s_n)/(1+\mu_n)$, $y^*_n$ the predator-only logistic equation $y_{n+1} = (r_n+1)y_n/(1+b_ny_n)$, and $(x^*_n,z^*_n)$ the globally attracting solution of the disease-free predator–prey subsystem. For $\lambda \in \mathbb N$ define
$$\mathcal R^u(\lambda) = \limsup_{n\to\infty}\prod_{k=n}^{n+\lambda}\frac{1+\beta_ks^*_{k+1}}{1+c_k+\eta_k g(s^*_k,0,y^*_k)}, \qquad \mathcal R^\ell(\lambda) = \liminf_{n\to\infty}\prod_{k=n}^{n+\lambda}\frac{1+\beta_kx^*_{k+1}}{1+c_k+\eta_k g(x^*_k,0,z^*_k)},$$
which do not depend on the chosen positive solutions.

**Theorem (extinction).** If $g(S+I,0,P) \le g(S,I,P)$ and $\mathcal R^u(\lambda) < 1$ for some $\lambda$, the infected prey go extinct. If moreover $a \equiv 0$ (no predation on susceptible prey) and $g(S,I,P) = g_0(S,I)P$, every disease-free solution is globally attractive.

**Theorem (persistence).** If $\mathcal R^\ell(\lambda) > 1$ for some $\lambda$, and the auxiliary perturbed disease-free subsystems have continuous families of globally attracting solutions, the infected prey are strongly persistent: $\liminf_n I_n > 0$.

For periodic coefficients the thresholds reduce to products over one period, $\mathcal R^u_{\rm PER}<1$ giving extinction and $\mathcal R^\ell_{\rm PER}>1$ giving persistence together with a periodic orbit; in the autonomous case they reduce to single-step ratios $\mathcal R^u_A$ and $\mathcal R^\ell_A$.

## Expansion

From the $I$ equation, $I_{n+1} = I_n\,\frac{1+\beta_nS_{n+1}}{1+c_n+\eta_n g(S_n,I_n,P_n)}$, so infected prey grow multiplicatively by the factor appearing in the thresholds. Upper solutions use the largest possible prey level ($s^*$, no predation or disease) and the smallest predation pressure from predators at their disease-free logistic level, giving the extinction condition; persistence compares with the disease-free predator–prey attractor $(x^*,z^*)$ and uses continuity in the small perturbation $\varepsilon$ of the auxiliary systems to show that $I$ cannot stay near $0$.

## Sources

- Lopo F. de Jesus, César M. Silva and Helder Vilarinho, "Dynamics of a discrete eco-epidemiological model with disease in the prey", arXiv:2007.10279 (2020), Theorems 1 and 2 (extinction and strong persistence), Theorems 3 and 4 (variant model), Corollaries 1–4 (periodic and autonomous cases), <https://doi.org/10.48550/arXiv.2007.10279>.
