# Reproduction number and disease-free stability of the fractional-order SEIQRP model

**Model.** Let $D^\alpha$ be the Caputo derivative of order $\alpha \in (0,1]$. The SEIQRP model has susceptible $S$, exposed $E$ (infectious during incubation), symptomatic infectious $I$, quarantined $Q$, recovered $R$ and protected (insusceptible) $P$ classes:

$$D^\alpha S = \Lambda - \beta_1 f_1(S)g_1(I) - \beta_2 f_2(S)g_2(E) - (\mu+\rho)S,$$

$$D^\alpha E = \beta_1 f_1(S)g_1(I) + \beta_2 f_2(S)g_2(E) - (\epsilon+\mu)E,$$

$$D^\alpha I = \epsilon E - (\delta+\mu)I,\qquad D^\alpha Q = \delta I - (\lambda+\kappa+\mu)Q,\qquad D^\alpha R = \lambda Q - \mu R,\qquad D^\alpha P = \rho S - \mu P .$$

The incidence functions satisfy $f_i(0) = g_i(0) = 0$; they are positive and strictly increasing for positive arguments; and $g_1'(I) \le g_1(I)/I$ and $g_2'(E)\le g_2(E)/E$ (concave-type incidence). The disease-free equilibrium is $M_0 = (S_0, 0, 0, 0, 0, \rho S_0/\mu)$ with $S_0 = \Lambda/(\mu+\rho)$.

**Basic reproduction number.**

$$\mathcal{R}_0 = \frac{\epsilon\beta_1}{(\mu+\epsilon)(\mu+\delta)}f_1(S_0)g_1'(0) + \frac{\beta_2}{\mu+\epsilon}f_2(S_0)g_2'(0).$$

The first term counts infections caused after symptom onset, and the second counts infections caused during incubation.

**Theorem.**

1. Solutions with nonnegative data stay nonnegative, and the set where the total population is at most $\Lambda/\mu$ is positively invariant.
2. The disease-free equilibrium $M_0$ always exists. If $\mathcal{R}_0 > 1$, there is in addition a unique endemic equilibrium $M_* = (S_*, E_*, I_*, Q_*, R_*, P_*)$ with $S_* = (\Lambda - (\mu+\epsilon)E_*)/(\mu+\rho)$, $I_* = \epsilon E_*/(\mu+\delta)$, $Q_* = \delta I_*/(\mu+\lambda+\kappa)$, $R_* = \lambda Q_*/\mu$ and $P_* = \rho S_*/\mu$.
3. $M_0$ is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$, for every order $\alpha \in (0,1]$.

## Expansion

At $M_0$ the characteristic polynomial factors as $(s+\mu)^2(s+\mu+\rho)(s+\mu+\lambda+\kappa)H_1(s)$. The quadratic $H_1$ has positive discriminant $(\delta - \epsilon + \beta_2 f_2(S_0)g_2'(0))^2 + 4\epsilon\beta_1 f_1(S_0)g_1'(0)$, so both of its roots are real. Their product is $(\mu+\delta)(\mu+\epsilon)(1-\mathcal{R}_0)$. Hence when $\mathcal{R}_0<1$ all six eigenvalues are negative reals, and when $\mathcal{R}_0>1$ one eigenvalue is positive. Matignon's criterion, that $D^\alpha x = Ax$ is asymptotically stable if and only if every eigenvalue satisfies $|\arg s| > \alpha\pi/2$, then gives stability or instability independently of $\alpha$, since negative reals have argument $\pi$ and a positive root has argument $0$. Endemic equilibria correspond to positive zeros of a scalar function $\varphi(E)$ with $\varphi(0)=0$ and $\varphi'(0) = (\mu+\epsilon)(\mathcal{R}_0-1)$. The monotonicity and concavity hypotheses on the incidence functions give existence and uniqueness of that zero when $\mathcal{R}_0>1$. Local stability of $M_*$ needs additional Routh–Hurwitz-type conditions, which depend on $\alpha$.

## Sources

- C. Xu, Y. Yu, Y. Chen and Z. Lu, "Forecast analysis of the epidemics trend of COVID-19 in the United States by a generalized fractional-order SEIR model", arXiv:2004.12541 (2020), Section 2.2 (model and hypotheses), Lemma 1 and Theorems 1–4, <https://doi.org/10.48550/arXiv.2004.12541>.
