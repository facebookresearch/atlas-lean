# Effective reproduction number of the two-sex HPV model

**Model.** In a normalized heterosexual population, females are susceptible $S_f$, infected unaware $U_f$, infected aware $I_f$ or vaccinated $V_f$, and males are susceptible $S_m$, infected $I_m$ or vaccinated $V_m$, with $S_f + U_f + I_f + V_f = 1$ and $S_m + I_m + V_m = 1$:

$$\dot S_f = (1 - w_1)\mu_f - \beta_m S_f I_m - (u_1 + \mu_f)S_f + \gamma_f(U_f + I_f) + \theta V_f, \qquad \dot V_f = w_1\mu_f + u_1 S_f - \epsilon\beta_m V_f I_m - (\mu_f + \theta)V_f,$$

$$\dot U_f = (S_f + \epsilon V_f)(1-p)\beta_m I_m - (\gamma_f + \alpha + \mu_f)U_f, \qquad \dot I_f = (S_f + \epsilon V_f)p\beta_m I_m + \alpha U_f - (\gamma_f + \mu_f)I_f,$$

$$\dot S_m = (1 - w_2)\mu_m - (\beta_f U_f + \tilde\beta_f I_f)S_m - (u_2 + \mu_m)S_m + \gamma_m I_m + \theta V_m, \qquad \dot I_m = (\beta_f U_f + \tilde\beta_f I_f)(S_m + \epsilon V_m) - (\gamma_m + \mu_m)I_m,$$

and $\dot V_m = w_2\mu_m + u_2 S_m - \epsilon(\beta_f U_f + \tilde\beta_f I_f)V_m - (\mu_m + \theta)V_m$. Here $w_1, w_2$ are the vaccinated fractions of recruits, $u_1, u_2$ adult vaccination rates, $\alpha$ the screening rate, $p$ the symptomatic fraction, $\epsilon \in [0,1]$ the residual susceptibility of vaccinated individuals, $\theta$ the waning rate, and $\beta_f, \tilde\beta_f$ the transmission rates of unaware and aware infected females.

**Proposition.** For the control vector $c = (w_1, w_2, u_1, u_2, \alpha)$ the model has a unique disease-free equilibrium with

$$S^0_f = \frac{(1 - w_1)\mu_f + \theta}{u_1 + \mu_f + \theta}, \quad V^0_f = 1 - S^0_f, \qquad S^0_m = \frac{(1 - w_2)\mu_m + \theta}{u_2 + \mu_m + \theta}, \quad V^0_m = 1 - S^0_m .$$

Let $\hat S_k = S^0_k + \epsilon V^0_k$ ($k = f,m$). The effective reproduction number is the geometric mean of the cross-sex transmission numbers,

$$\mathcal{R}_e(c) = \sqrt{T_{m\to f}(c)\,T_{f\to m}(c)}, \qquad T_{m\to f} = \frac{\beta_m\hat S_f}{\gamma_m + \mu_m},$$

$$T_{f\to m} = \hat S_m\left[(1 - p)\Big(\frac{\beta_f}{\gamma_f + \alpha + \mu_f} + \frac{\alpha\,\tilde\beta_f}{(\gamma_f + \alpha + \mu_f)(\gamma_f + \mu_f)}\Big) + \frac{p\,\tilde\beta_f}{\gamma_f + \mu_f}\right],$$

and the disease-free equilibrium is locally asymptotically stable if $\mathcal{R}_e(c) < 1$ and unstable if $\mathcal{R}_e(c) > 1$.

## Expansion

The disease-free values solve the linear balance between recruitment, vaccination and waning in each sex. In the infected subsystem $(U_f, I_f, I_m)$ new infections only cross sexes, so the next-generation matrix has the bipartite form $\begin{pmatrix}0 & T_{m\to f}\\ T_{f\to m} & 0\end{pmatrix}$ (after aggregating the two female infected states), whose spectral radius is $\sqrt{T_{m\to f}T_{f\to m}}$. An infected male transmits at rate $\beta_m\hat S_f$ for a mean time $1/(\gamma_m + \mu_m)$. A newly infected female is unaware with probability $1 - p$, transmitting at rate $\beta_f\hat S_m$ for mean time $1/(\gamma_f + \alpha + \mu_f)$, and is then screened into the aware class with probability $\alpha/(\gamma_f + \alpha + \mu_f)$; aware infection lasts $1/(\gamma_f + \mu_f)$ at rate $\tilde\beta_f\hat S_m$. Local stability then follows from the van den Driessche–Watmough threshold theorem. Vaccination lowers $\hat S_f, \hat S_m$; screening lowers $T_{f\to m}$ exactly when aware women transmit less ($\tilde\beta_f < \beta_f$).

## Sources

- Fernando Saldaña, José Ariel Camacho-Gutiérrez, Ignacio Barradas, Andrei Korobeinikov, "When optimal is not the best: cost effectiveness analysis for HPV epidemic models", arXiv (2020). Section 2 (normalized model, disease-free equilibrium, effective reproduction number as a geometric mean of transfer terms, Corollary 2.1). <https://doi.org/10.48550/arXiv.2011.06594>
