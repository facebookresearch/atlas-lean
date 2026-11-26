# Stability switches in the brood-maturation delay honey bee model

**Model.** An alternative stage-structured honey bee model lets adults mature from the surviving brood stock of $\tau$ days earlier rather than from the brood cohort laid then:
$$B'=\frac{rH^2}{K+H^2}-d_bB-e^{-d_b\tau}B(t-\tau),\qquad H'=e^{-d_b\tau}B(t-\tau)-d_hH ,$$
with egg-laying rate $r$, half-saturation $K>0$ and mortalities $d_b,d_h>0$. Interior equilibria satisfy $B^\ast=d_he^{d_b\tau}H^\ast$ and $\dfrac{rH}{K+H^2}=d_h(1+d_be^{d_b\tau})$.

**Theorem (extinction equilibrium).** $E_e=(0,0)$ always exists.
1. If $d_b\ge\frac{\sqrt2}{2}$, $E_e$ is asymptotically stable for all $\tau\ge 0$.
2. If $0<d_b<\frac{\sqrt2}{2}$, $E_e$ is asymptotically stable for $\tau\in(0,\tau_0)$ and for $\tau\ge\tau_1$, and unstable for $\tau\in(\tau_0,\tau_1)$, where $\tau_k=(\theta+k\pi)/w$ with $\theta=\pi-\arctan(w/d_b)$ and $w=(e^{-2d_b\tau}-d_b^2)^{1/2}$.

**Theorem (interior equilibria).** Let $r>2d_h\sqrt K(1+d_b)$ and $\tau^\ast=\frac{1}{d_b}\ln\!\Big(\frac{1}{d_b}\Big(\frac{r}{2d_h\sqrt K}-1\Big)\Big)$. For $\tau\in[0,\tau^\ast)$ there are two interior equilibria $E_1,E_2$ with $H_1^\ast<H_2^\ast$; $E_1$ is always unstable, and with $r_c=\dfrac{2d_h\sqrt K(1+d_b)^2}{\sqrt{(1+d_b)^2-4d_b^2}}$:
1. if $d_b\ge 1$, or $0<d_b<1$ with $d_b^2+d_h^2\ge 1$ and $r\le r_c$, then $E_2$ is locally asymptotically stable for all $\tau\in[0,\tau^\ast)$;
2. if $0<d_b<1$, $d_b^2+d_h^2\ge 1$ and $r>r_c$, the stability of $E_2$ switches exactly once, from stable to unstable, as $\tau$ increases;
3. if $d_b^2+d_h^2<1$ and $r\le r_c$, the stability of $E_2$ changes at most finitely many times and is eventually lost;
4. if $d_b^2+d_h^2<1$ and $r>r_c$, $E_2$ switches from stable to unstable at least once.

Because $E_e$ can lose stability to oscillations around zero, this formulation admits solutions that leave the nonnegative cone, unlike the cohort-based brood–adult model, whose solutions stay nonnegative and whose interior stability does not depend on the delay.

## Expansion

The maturation term $e^{-d_b\tau}B(t-\tau)$ removes from the brood class a delayed copy of the current brood stock, so the linearization at zero contains the delayed self-feedback $-e^{-d_b\tau}e^{-\lambda\tau}$ in the brood equation; its characteristic equation $\lambda+d_b+e^{-d_b\tau}e^{-\lambda\tau}=0$ has imaginary roots $\pm iw$ exactly when $e^{-2d_b\tau}>d_b^2$, which yields the stability window $(\tau_0,\tau_1)$. At $E_2$ the characteristic equation is $\lambda^2+(d_b+d_h)\lambda+d_hd_b+\big(\lambda+d_h-\frac{2rKH^\ast}{(K+H^{\ast2})^2}\big)e^{-(\lambda+d_b)\tau}=0$, whose delay-dependent coefficients produce the stability switches classified above. The comparison shows that how maturation is modeled, by cohort or by stock, changes qualitative colony dynamics.

## Depends on

- [Extinction and bistability in the delayed brood–adult honey bee model](extinction-and-bistability-in-the-delayed-brood-adult-honey-bee-model.md)

## Sources

- Jun Chen, Komi Messan, Marisabel Rodriguez Messan and Gloria DeGrandi-Hoffman, "How to model honeybee population dynamics: stage structure and seasonality", arXiv:2003.09796 (2020), Theorems 3.5 and 3.6, <https://doi.org/10.48550/arXiv.2003.09796>.
