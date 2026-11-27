# Reproduction number and equilibria of the LLIN malaria model

**Model.** Humans are susceptible $S_h$, infectious $I_h$ or immune $R_h$ (with $N_h = S_h + I_h + R_h$). Female mosquitoes alternate between a questing state (seeking a blood meal) and a resting state: susceptible questing mosquitoes $S_q$, infected mosquitoes in latency stages $E_r^1, E_q^1, \dots, E_q^6, E_r^7$ (seven resting and six questing stages), and infectious mosquitoes $I_r$ (resting) and $I_q$ (questing). Let $w \in [0,1]$ be the proportion of people who own a long-lasting insecticidal net (LLIN) and use it correctly. LLIN use reduces the biting rate, the vector recruitment and the loss of immunity, and raises the death rate of questing mosquitoes:

$$a(w) = a_{\max} - w\Delta_a, \quad \Lambda_v(w) = \Lambda_v^{\max} - w\Delta_{\Lambda_v}, \quad \gamma_h(w) = \gamma_h^{\min} + w\Delta_{\gamma_h}, \quad \mu_v(w) = \mu_v + w\Delta_{\mu_v}.$$

With forces of infection $\alpha_h = a(w)\,mI_q/N_h$ and $\alpha_v = a(w)(cI_h + \tilde c R_h)/N_h$, the dynamics are

$$S_h' = \Lambda_h + \gamma_h R_h - (\alpha_h + \mu_h)S_h, \quad I_h' = \alpha_h S_h - (\delta_h + \mu_h + \mu_d)I_h, \quad R_h' = \delta_h I_h - (\gamma_h + \mu_h)R_h,$$

$$S_q' = \Lambda_v - (\alpha_v + \mu_v + w\Delta_{\mu_v})S_q, \quad (E_r^1)' = \alpha_v S_q - (\chi + \mu_v)E_r^1,$$

$$(E_q^i)' = \chi E_r^i - (\beta + \mu_v + w\Delta_{\mu_v})E_q^i \ (1 \le i \le 6), \quad (E_r^i)' = \beta E_q^{i-1} - (\chi + \mu_v)E_r^i \ (2 \le i \le 7),$$

$$I_r' = \beta I_q - (\chi + \mu_v)I_r, \quad I_q' = \chi(E_r^7 + I_r) - (\beta + \mu_v + w\Delta_{\mu_v})I_q,$$

where $\chi$ and $\beta$ are the resting-to-questing and questing-to-resting rates. Put $f_r = \chi/(\chi + \mu_v)$ and $f_q = \beta/(\beta + \mu_v + w\Delta_{\mu_v})$.

**Well-posedness.** The non-negative cone of $\mathbb{R}^{19}$ is positively invariant, and $\Omega = \{0 \le N_h \le \Lambda_h/\mu_h,\ 0 \le N_v \le \Lambda_v(w)/\mu_v\}$ is compact, forward invariant and absorbing.

**Disease-free equilibrium and threshold.** The disease-free equilibrium has $S_h^* = N_h^* = \Lambda_h/\mu_h$, $S_v^* = \Lambda_v(w)/(\mu_v + w\Delta_{\mu_v})$ and all infected classes zero. The basic reproduction number is

$$\mathcal{R}_0 = \frac{S_v^* a m (f_r f_q)^7}{\beta(1 - f_q f_r)} \cdot \frac{a\,[c(\gamma_h + \mu_h) + \tilde c\,\delta_h]}{N_h^*(\delta_h + \mu_h + \mu_d)(\gamma_h + \mu_h)}.$$

**Theorem (global stability of the DFE).** With $\zeta = \mu_h/(\mu_h + \mu_d)$, the disease-free equilibrium is globally asymptotically stable in $\Omega$ when $\mathcal{R}_0 < \zeta$.

**Theorem (endemic equilibria).** There are numbers $\mathcal{R}_-, \mathcal{R}_c, \mathcal{R}_+$ such that the model has a unique endemic equilibrium if $\mathcal{R}_0 > 1$; a unique endemic equilibrium if $\mathcal{R}_0 = 1$ and $\mathcal{R}_c < 1$; two endemic equilibria if $\mathcal{R}_c < \mathcal{R}_0 < \min(1, \mathcal{R}_-)$ or $\max(\mathcal{R}_c, \mathcal{R}_+) < \mathcal{R}_0 < 1$; and none otherwise. Two endemic equilibria below $\mathcal{R}_0 = 1$ signal a backward bifurcation, so pushing $\mathcal{R}_0$ just below one need not eliminate malaria.

## Expansion

The system has the form $\mathbf{x}_S' = A_S(\mathbf{x})\mathbf{x}_S + A_{S,I}(\mathbf{x})\mathbf{x}_I + \mathbf{b}_S$, $\mathbf{x}_I' = A_I(\mathbf{x})\mathbf{x}_I$ with $A_I$ a Metzler matrix. The threshold is the condition that $A_I$ at the disease-free equilibrium is Metzler-stable; it is checked by repeated Schur-complement reductions, each eliminating a stable diagonal block. The factor $(f_r f_q)^7$ is the probability of surviving the seven resting–questing cycles of the latent period; $1/(\beta(1 - f_q f_r))$ accounts for the repeated questing bouts of an infectious mosquito; and the second factor is the number of mosquito infections produced by one human infection, counting the residual infectivity $\tilde c$ of immune humans. Global stability for $\mathcal{R}_0 < \zeta$ follows from a Kamgang–Sallet-type result for such Metzler systems; the factor $\zeta$ accounts for the variation of $N_h$ caused by disease-induced deaths.

## Sources

- S. Y. Tchoumi, Y. T. Kouakep, D. J. Fotsa Mbogne and J. C. Kamgang, "Optimal control of a malaria model with long-lasting insecticide-treated nets", arXiv:2006.12536 (2020), Section 2: model, Propositions 2.1–2.2 (invariance and absorbing set), Theorem 2.1 (disease-free equilibrium), Theorem 2.2 (basic reproduction number), Theorem 2.3 (global stability of the DFE) and Theorem 2.4 (endemic equilibria). <https://doi.org/10.48550/arXiv.2006.12536>. Published version: Mathematical Modelling and Control 1(4) (2021), 188–207, <https://doi.org/10.3934/mmc.2021018>; locators above refer to the arXiv version.
