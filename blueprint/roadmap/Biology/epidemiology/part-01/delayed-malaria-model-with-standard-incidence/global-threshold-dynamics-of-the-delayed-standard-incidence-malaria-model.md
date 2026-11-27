# Global threshold dynamics of the delayed malaria model with standard incidence

**Setting.** Consider the delayed host–vector malaria model

$$\dot S_h(t) = \beta_h - C_{vh}\frac{I_v(t)}{N_v(t)}S_h(t) - \mu_h S_h(t), \qquad \dot I_h(t) = C_{vh}\frac{I_v(t-\tau)}{N_v(t-\tau)}S_h(t-\tau) - \mu_h I_h(t),$$

$$\dot S_v(t) = \beta_v - C_{hv}I_h(t)S_v(t) - \mu_v S_v(t), \qquad \dot I_v(t) = C_{hv}I_h(t)S_v(t) - \mu_v I_v(t),$$

with $N_v = S_v + I_v$, incubation delay $\tau \ge 0$, phase space $C_+ = \{\varphi \in C([-\tau,0], [0,\infty)^4) : \varphi_3 + \varphi_4 > 0\}$, and basic reproduction number

$$R_0 = \sqrt{\frac{C_{vh}C_{hv}\beta_h}{\mu_h^2\mu_v}}.$$

Let $E^0 = (\beta_h/\mu_h, 0, \beta_v/\mu_v, 0)$ be the disease-free equilibrium, $E^*$ the endemic equilibrium (which exists exactly when $R_0 > 1$), and $D = \{\varphi \in C_+ : \varphi_2(0) > 0\}$.

**Theorem (disease-free equilibrium).** For every $\tau \ge 0$, $E^0$ is globally asymptotically stable in $C_+$ if $R_0 < 1$, and globally attractive in $C_+$ if $R_0 = 1$.

**Theorem (endemic equilibrium).** If $R_0 > 1$, then $E^*$ is globally asymptotically stable in $D$ for every $\tau \ge 0$.

Hence $R_0$ is a sharp threshold that the incubation delay does not affect.

## Depends on

- [Local stability and weak persistence of the delayed malaria model with standard incidence](local-stability-and-weak-persistence-of-the-delayed-standard-incidence-malaria-model.md)

## Expansion

Because $N_v(t) \to S_v^0 = \beta_v/\mu_v$, the system is asymptotically autonomous with limiting system

$$\dot S_h = \beta_h - \frac{C_{vh}I_v S_h}{S_v^0} - \mu_h S_h, \qquad \dot I_h = \frac{C_{vh}I_v(t-\tau)S_h(t-\tau)}{S_v^0} - \mu_h I_h,$$

with the same mosquito equations. For this mass-action delay system one builds Lyapunov functionals: for $E^0$, a combination of Volterra terms in $S_h$ and $S_v$, linear terms in $I_h$ and $I_v$, and the delay integral $\int_{-\tau}^0 \frac{\mu_v C_{vh}}{\beta_v}\psi_4(\theta)\psi_1(\theta)\,d\theta$; for $E^*$, the Volterra-type functional $V_2(\psi(0))$ plus $\mu_h I_h^* \int_{-\tau}^0 g\big(\psi_4(\theta)\psi_1(\theta)/(I_v^* S_h^*)\big)\,d\theta$ with $g(x) = x - 1 - \ln x$. LaSalle's invariance principle gives global attractivity for the limiting system. The theory of asymptotically autonomous semiflows transfers it to the original system: the $\omega$-limit set of every orbit is compact and invariant for the limiting system, so it reduces to the equilibrium. Combined with local asymptotic stability, this gives global asymptotic stability.

## Sources

- S. Guo, M. He and J.-A. Cui, "Global stability of a time-delayed malaria model with standard incidence rate", arXiv:2210.17251 (2022), Section 5: limiting system, Theorem 5.1 (global stability of the disease-free equilibrium) and Theorem 5.2 (global stability of the endemic equilibrium). <https://doi.org/10.48550/arXiv.2210.17251>. Published version: Acta Mathematicae Applicatae Sinica, English Series 39(2) (2023), 211–221, <https://doi.org/10.1007/s10255-023-1042-y>; locators above refer to the arXiv version.
