# Threshold dynamics of the hybrid Mittag-Leffler–Caputo–Fabrizio fractional SVIR model

**Fractional operator.** For $0 < \nu < 1$, $0 < \alpha \le 1$ and $u \in H^1$, the hybrid Mittag-Leffler–Caputo–Fabrizio (MLCF) derivative is
$$ {}^{\mathrm{MLCF}}D_t^{\nu,\alpha}u(t) = \frac{M(\nu)\,E_\alpha\!\big(\tfrac{\nu}{1-\nu}t^\alpha\big)^{-1}}{1-\nu}\int_0^t E_\alpha\!\Big(\frac{\nu}{1-\nu}\kappa^\alpha\Big)u'(\kappa)\,d\kappa, \qquad E_\alpha(z) = \sum_{k\ge 0}\frac{z^k}{\Gamma(\alpha k + 1)}, $$
with normalization $M(0) = M(1) = 1$. For $\alpha = 1$ the kernel is exponential (Caputo–Fabrizio type). The kernel is nonsingular and combines short- and long-term memory.

**Model.** Susceptible $S$, vaccinated $V$, infected $I$ and recovered $R$ individuals, with $N = S + V + I + R$, evolve as
$$
\begin{aligned}
D S &= \Delta - \beta\frac{SI}{N} + \mu R - (k + \delta)S, & D V &= kS - (1-\tau)\beta\frac{VI}{N} - \delta V,\\
D I &= \beta\frac{SI}{N} + (1-\tau)\beta\frac{VI}{N} - (\alpha_r + \delta + \delta_0)I, & D R &= \alpha_r I - (\delta + \mu)R,
\end{aligned}
$$
where $D = {}^{\mathrm{MLCF}}D_t^{\nu,\alpha}$. The parameters are recruitment $\Delta$, vaccination rate $k$, contact rate $\beta$, vaccine efficacy $\tau$, waning immunity $\mu$, natural death rate $\delta$, disease death rate $\delta_0$ and recovery rate $\alpha_r$.

**Theorem.**
1. Solutions with nonnegative data stay nonnegative and bounded in an invariant region $\Omega$. The proof uses the integrated form of the MLCF operator and a generalized fractional Gronwall inequality.
2. The disease-free equilibrium is $E_0 = (S_0,V_0,0,0)$ with $S_0 = \Delta/(k+\delta)$, $V_0 = kS_0/\delta$ and $N_0 = \Delta/\delta$. The basic reproduction number is
$$ \mathcal{R}_0 = \frac{\beta}{\alpha_r + \delta + \delta_0}\cdot\frac{S_0 + (1-\tau)V_0}{N_0} = \frac{\beta\,\big(\delta + (1-\tau)k\big)}{(\alpha_r + \delta + \delta_0)(k + \delta)} . $$
3. $E_0$ is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$; it is globally asymptotically stable in $\Omega$ if $\mathcal{R}_0 \le 1$.
4. If $\mathcal{R}_0 > 1$, the endemic equilibrium $E^*$ exists and is locally asymptotically stable, and it is globally asymptotically stable in the interior of $\Omega$.
5. A $\theta$-weighted nonstandard finite-difference discretization of the MLCF derivative preserves positivity and boundedness. It is unconditionally stable in the fully implicit case, consistent, and first-order convergent.

The memory parameters $(\nu,\alpha)$ change transient dynamics (timing and height of the epidemic peak) but not the equilibria or the threshold $\mathcal{R}_0 = 1$.

## Expansion

$\mathcal{R}_0$ is the next-generation value: new infections arise from both susceptibles and imperfectly protected vaccinees, in proportions $S_0/N_0$ and $(1-\tau)V_0/N_0$, and infection lasts $1/(\alpha_r + \delta + \delta_0)$ on average. Global stability uses logarithmic (Volterra-type) Lyapunov functionals such as $\sum c_i\,(x_i - x_i^* - x_i^*\ln(x_i/x_i^*))$. A chain-rule inequality bounds the MLCF derivative of a convex function by the convex function's derivative times the MLCF derivative of its argument, and a fractional LaSalle invariance principle identifies the limit set. The nonstandard scheme keeps positivity by using nonlocal approximations of the nonlinear terms and denominator functions in place of the step size.

## Sources

- Seham M. Al-Mekhlafi, Ahmed Boudaoui and Matthias Ehrhardt, "Structure-Preserving Schemes for a Fractional SVIR Epidemic Model with a Hybrid Mittag-Leffler-Caputo-Fabrizio Operator", arXiv:2606.19045 (2026), Section 2 (Definition 2.3, model), Section 3 (Lemmas 3.1–3.2, Theorems 3.3–3.6, Lemmas 3.7–3.8, Theorems 3.9–3.10), Sections 4–5 (NSFD scheme, Theorem 5.1), <https://doi.org/10.48550/arXiv.2606.19045>.
