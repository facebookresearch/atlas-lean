# Upper and lower reproduction numbers of the non-autonomous diffusive SIS model

**Model.** On a bounded smooth domain $\Omega\subset\mathbb{R}^N$ with Neumann boundary conditions, consider the standard-incidence SIS system

$$\omega\partial_t S - d_S\Delta S = -\frac{\beta(x,t)SI}{S+I} + \gamma(x,t)I, \qquad \omega\partial_t I - d_I\Delta I = \frac{\beta(x,t)SI}{S+I} - \gamma(x,t)I,$$

with $S_0 \ge 0$, $I_0 \ge 0$, $I_0 \not\equiv 0$, and transmission and recovery rates bounded between positive constants, $0<\beta_*<\beta<\beta^*$ and $0<\gamma_*<\gamma<\gamma^*$, but not necessarily periodic in time. The total population $\int_\Omega (S+I)\,dx = N_{\mathrm{total}}$ is conserved.

**Critical numbers.** Let $H(\cdot\,;\omega,d_I,c)$ be the normalized principal Floquet bundle of $\omega\partial_t - d_I\Delta + c$ (see the Depends-on article). By monotonicity in the potential there are unique $\underline{\mathcal{R}}_0$, $\overline{\mathcal{R}}_0 > 0$ with

$$\limsup_{T\to\infty}\frac{1}{T}\int_0^T H\big(s;\gamma - \beta/\underline{\mathcal{R}}_0\big)\,ds = 0, \qquad \liminf_{T\to\infty}\frac{1}{T}\int_0^T H\big(s;\gamma - \beta/\overline{\mathcal{R}}_0\big)\,ds = 0.$$

When they coincide (e.g. periodic $\beta,\gamma$) the common value is the basic reproduction number $\mathcal{R}_0$.

**Theorem.**
1. $1 - \underline{\mathcal{R}}_0$ has the sign of $\limsup_{T}\frac{1}{T}\int_0^T H(s;\gamma-\beta)\,ds$, and $1-\overline{\mathcal{R}}_0$ has the sign of the corresponding $\liminf$. If $\beta,\gamma$ are uniformly Hölder in time,

$$\liminf_{T\to\infty}\frac{\int_0^T\!\int_\Omega \beta}{\int_0^T\!\int_\Omega\gamma} \le \underline{\mathcal{R}}_0 \le \sup_{x(\cdot)\in C(\mathbb{R};\overline{\Omega})}\liminf_{T\to\infty}\frac{\int_0^T \beta(x(s),s)\,ds}{\int_0^T\gamma(x(s),s)\,ds},$$

and the same with $\limsup$ for $\overline{\mathcal{R}}_0$.
2. (Extinction) If $\overline{\mathcal{R}}_0 < 1$, then $(S,I)(\cdot,t) \to (N_{\mathrm{total}}/|\Omega|, 0)$ in $C(\overline{\Omega})$.
3. (Persistence in mean) If $d_S = d_I$ and $\underline{\mathcal{R}}_0 > 1$, then $\liminf_{T\to\infty}\frac{1}{T}\int_0^T\int_\Omega I(x,s)\,dx\,ds > 0$.
4. (Fast infected diffusion) As $d_I \to \infty$ with $\omega/d_I \to \vartheta\in[0,\infty]$ (under smoothness assumptions), $\underline{\mathcal{R}}_0$ and $\overline{\mathcal{R}}_0$ converge to the $\liminf$ and $\limsup$ of the space-time ratio $\int_0^T\!\int_\Omega\beta \big/ \int_0^T\!\int_\Omega\gamma$.

## Depends on

- [Bounds and monotonicity of the principal Floquet exponent](../../population-dynamics/principal-floquet-bundle-of-nonautonomous-parabolic-operators/bounds-and-monotonicity-of-the-principal-floquet-exponent.md)

## Expansion

Linearizing at the disease-free state $(N_{\mathrm{total}}/|\Omega|,0)$ gives $\omega\partial_t I - d_I\Delta I + (\gamma-\beta)I = 0$, whose growth is governed by the Floquet exponents of the potential $\gamma - \beta$. Scaling $\beta$ by $1/r$ and solving for the zero of the exponent defines threshold numbers, exactly as $\mathcal{R}_0$ is defined through the principal eigenvalue in the autonomous case. The gap $\overline{\mathcal{R}}_0 - \underline{\mathcal{R}}_0$ measures how far the non-periodic environment is from having a single time average; between the two numbers the dynamics are not determined by this linear criterion. The ratio bounds follow from the bounds on the Floquet exponent by the minimum and the spatial mean of the potential.

## Sources

- Yun Li, Yuan Lou and Zhi-Cheng Wang, "Qualitative Properties of the Principal Floquet Bundle and Their Applications", arXiv:2609.26385 (2026), Chapter 9, Theorems 9.2, 9.3 and 9.4(i), <https://doi.org/10.48550/arXiv.2609.26385>.
