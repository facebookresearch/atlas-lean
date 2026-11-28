# Survivor-marginalized versus causal hazard ratio

**Setting.** Each individual $i$ has a latent frailty $U_{0i}$, a latent effect modifier $U_{1i}$ and independent uniform noise $N_{Ti}$. Under an intervention setting exposure to level $a$ (with $a = 0$ unexposed), the potential event time is

$$T_i^a = \min\Big\{t > 0 : \exp\Big(-\int_0^t \lambda_i^a(s)\,ds\Big) \le N_{Ti}\Big\}, \qquad \lambda_i^a(t) = f_0(t, U_{0i})\, f_1(t, U_{1i}, a), \quad f_1(t, U_1, 0) = 1,$$

so $f_1(t,U_{1i},a)$ is the individual's hazard ratio. In a randomized trial the assignment $A$ is independent of $(U_0, U_1, N_T)$, and causal consistency gives $T = T^A$. Define

- the **causal hazard ratio** $\mathrm{CHR}(t) = \dfrac{\mathbb E[f_0(t,U_0) f_1(t,U_1,a)]}{\mathbb E[f_0(t,U_0)]}$ (ratio of population-averaged individual hazards in the all-exposed and all-unexposed worlds);
- the **observed hazard ratio** $\mathrm{OHR}(t)$, the ratio of the hazards of $T$ given $T \ge t$ in arms $A = a$ and $A = 0$.

**Theorem.** Assume the hazard has no infinite discontinuity (for each $t$, $\mathbb E[f_0(t+h,U_0)f_1(t+h,U_1,a) \mid T^a \ge t] < \infty$ for small $h > 0$).
1. In a randomized trial $\mathrm{OHR}(t)$ equals the **survivor-marginalized causal hazard ratio**

$$\mathrm{SMCHR}(t) = \frac{\mathbb E[f_0(t,U_0) f_1(t,U_1,a) \mid T^a \ge t]}{\mathbb E[f_0(t,U_0) \mid T^0 \ge t]},$$

in which each expectation is over the survivors of its own counterfactual world; the CHR is not identifiable from the observed data without assumptions on the law of $(U_0, U_1)$.
2. (Frailty, homogeneous effect) If $f_1(t,U_1,a) = f_1(t,a)$, then $\mathrm{SMCHR}(t) = f_1(t,a)\,\dfrac{\mathbb E[f_0(t,U_0) \mid T^a \ge t]}{\mathbb E[f_0(t,U_0) \mid T^0 \ge t]}$. If moreover the frailty is multiplicative, $f_0(t, U_0) = U_0\lambda_0(t)$ with $U_0 > 0$ having Laplace transform $\mathcal L$, then $\mathbb E[U_0 \mid T^a \ge t] = -\mathcal L'(\Lambda_a(t))/\mathcal L(\Lambda_a(t))$, where $\Lambda_a(t) = \int_0^t \lambda_0 f_1(s,a)\,ds$, which is nonincreasing in $\Lambda_a(t)$. So if the exposure lowers the cumulative hazard ($\Lambda_a(t) < \Lambda_0(t)$), the frailty factor is at least $1$ and a protective effect appears weaker than it is; if it raises it, the factor is at most $1$ and a harmful effect appears weaker.
3. (Effect heterogeneity, no frailty) If $f_0(t,U_0) = \lambda_0(t)$ and the individual hazard ratios are ordered the same way at all times, $f_1(t, U_1, a) = U_1 h(t)$ with $U_1 > 0$ and $h > 0$, then $\mathrm{SMCHR}(t) = \mathbb E[f_1(t,U_1,a) \mid T^a \ge t] \le \mathbb E[f_1(t,U_1,a)] = \mathrm{CHR}(t)$, so the exposure looks more beneficial than it is, whether it helps or harms on average.

## Expansion

$T \ge t$ is a collider between $A$ and the latent variables: among survivors, assignment carries information about $(U_0, U_1)$, while among survivors of a single counterfactual world it does not, which is why the OHR in a trial reduces to the SMCHR. Both conditional expectations are weighted averages with weights $P(T^a \ge t \mid U_0, U_1)/P(T^a \ge t)$, which tilt toward individuals with low hazard as $t$ grows; the tilt is faster in the arm with the larger cumulative hazard. For gamma frailty with mean $1$ and variance $\theta$, $\mathcal L(s) = (1 + \theta s)^{-1/\theta}$, so $\mathbb E[U_0 \mid T^a \ge t] = 1/(1 + \theta\Lambda_a(t))$ and a constant individual hazard ratio $\mu$ yields $\mathrm{SMCHR}(t) = \mu(1 + \theta\Lambda_0(t))/(1 + \theta\mu\Lambda_0(t))$, which drifts from $\mu$ toward $1$; with a non-susceptible frailty point mass (compound Poisson) the observed log hazard ratio can even change sign. A larger frailty variance gives a larger gap. Frailty and a time-varying causal effect cannot be distinguished from one-arm marginal data, so time-varying observed hazard ratios are not evidence of a time-varying biological effect.

## Sources

- R. A. J. Post, E. R. van den Heuvel, H. Putter, "The built-in selection bias of hazard ratios formalized using structural causal models", Lifetime Data Analysis 30 (2024) 404–438, SCM (2), Definition 1, Theorems 1–2, Condition 1, Corollaries 1–2, Lemma 1 and Section 4, <https://doi.org/10.1007/s10985-024-09617-y>, PMCID PMC11300553.
