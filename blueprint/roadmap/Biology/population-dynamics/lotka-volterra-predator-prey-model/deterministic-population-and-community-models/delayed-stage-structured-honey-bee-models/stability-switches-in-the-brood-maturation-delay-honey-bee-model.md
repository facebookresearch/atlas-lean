# Stability switches in the brood-maturation delay honey bee model

**Model.** An alternative stage-structured honey bee model lets adults mature from the surviving brood stock of $\tau$ days earlier rather than from the brood cohort laid then:

$$B'=\frac{rH^2}{K+H^2}-d_bB-e^{-d_b\tau}B(t-\tau),\qquad H'=e^{-d_b\tau}B(t-\tau)-d_hH ,$$

with egg-laying rate $r$, half-saturation $K>0$ and mortalities $d_b,d_h>0$. Interior equilibria satisfy $B^\ast=d_he^{d_b\tau}H^\ast$ and $\dfrac{rH}{K+H^2}=d_h(1+d_be^{d_b\tau})$.

**Theorem (extinction equilibrium).** $E_e=(0,0)$ always exists, and its brood-equation characteristic equation $\lambda+d_b+e^{-d_b\tau}e^{-\lambda\tau}=0$ has, for $\tau>0$, the roots $\lambda = W_k(-\tau)/\tau - d_b$, so for $\tau>0$ $E_e$ is asymptotically stable if and only if $\operatorname{Re} W_0(-\tau) < d_b\tau$; at $\tau=0$ the only root is $\lambda=-1-d_b$, so $E_e$ is asymptotically stable. Consequently:
1. Let $d^* := \max_{\tau>0} \operatorname{Re} W_0(-\tau)/\tau \approx 0.1704$, attained at $\tau^\dagger \approx 4.363$. $E_e$ is asymptotically stable for all $\tau\ge 0$ if and only if $d_b > d^*$. If $d_b = d^*$, $E_e$ is asymptotically stable for every $\tau\ge0$ with $\tau\ne\tau^\dagger$, and at $\tau=\tau^\dagger$ it has a root with zero real part.
2. If $0 < d_b < d^*$, $E_e$ is unstable strictly between the two solutions $\tau_0 < \tau_1$ of $\tau w(\tau) = \theta(\tau)$, where $w(\tau) = (e^{-2d_b\tau}-d_b^2)^{1/2}$ and $\theta(\tau) = \pi - \arctan(w(\tau)/d_b)$, and asymptotically stable for $\tau \in [0, \tau_0)$ and $\tau > \tau_1$ (the source's Theorem 3.5 states the looser threshold $d_b = \sqrt{2}/2$ and $\tau_1 = (\theta+\pi)/w$).

**Theorem (interior equilibria).** Let $r>2d_h\sqrt K(1+d_b)$ and $\tau^\ast=\frac{1}{d_b}\ln\!\Big(\frac{1}{d_b}\Big(\frac{r}{2d_h\sqrt K}-1\Big)\Big)$. For $\tau\in[0,\tau^\ast)$ there are two interior equilibria $E_1,E_2$ with $H_1^\ast<H_2^\ast$; $E_1$ is always unstable. Let $r_c=\dfrac{2d_h\sqrt K(1+d_b)^2}{\sqrt{(1+d_b)^2-4d_b^2}}$. If $d_b\ge 1$, or $0<d_b<1$ with $d_b^2+d_h^2\ge 1$ and $r\le r_c$, then $E_2$ is locally asymptotically stable for all $\tau\in[0,\tau^\ast)$.

Because $E_e$ can lose stability to oscillations around zero, this formulation admits solutions that leave the nonnegative cone, unlike the cohort-based brood–adult model, whose solutions stay nonnegative and whose interior stability does not depend on the delay.

## Expansion

The maturation term $e^{-d_b\tau}B(t-\tau)$ removes from the brood class a delayed copy of the current brood stock, so the linearization at zero contains the delayed self-feedback $-e^{-d_b\tau}e^{-\lambda\tau}$ in the brood equation; its characteristic equation $\lambda+d_b+e^{-d_b\tau}e^{-\lambda\tau}=0$ can have imaginary roots $\pm iw$ only when $e^{-2d_b\tau}>d_b^2$, at the $\tau$ solving $\tau w(\tau)=\theta(\tau)+2k\pi$ for some integer $k\ge0$; the $k=0$ solutions $\tau_0<\tau_1$ bound the window where $E_e$ is unstable. Substituting $\mu=\lambda+d_b$ turns it into $\mu+e^{-\mu\tau}=0$, whose roots are $\mu=W_k(-\tau)/\tau$; the function $\tau\mapsto\operatorname{Re}W_0(-\tau)/\tau$ is unimodal, which gives the threshold $d^*$. For fixed $\tau$ this is the equation $\lambda+a+be^{-\lambda\tau}=0$ with $a=d_b$, $b=e^{-d_b\tau}$, whose stability region Hayes determined. At $E_2$ the characteristic equation is $\lambda^2+(d_b+d_h)\lambda+d_hd_b+\big(\lambda+d_h-\frac{2rKH^\ast}{(K+H^{\ast2})^2}\big)e^{-(\lambda+d_b)\tau}=0$. The source's Theorem 3.6 also claims stability switches of $E_2$ in the remaining parameter regimes, but those claims fail numerically (for example, with $K=1$, $d_b=0.3$, $d_h=0.5$, $r=30$, $E_2$ is stable on all of $[0,\tau^\ast)$) and are not stated here. The comparison shows that how maturation is modeled, by cohort or by stock, changes qualitative colony dynamics.

## Depends on

- [Extinction and bistability in the delayed brood–adult honey bee model](extinction-and-bistability-in-the-delayed-brood-adult-honey-bee-model.md)

## Sources

- Jun Chen, Komi Messan, Marisabel Rodriguez Messan, Gloria DeGrandi-Hoffman, Dingyong Bai and Yun Kang, "How to model honeybee population dynamics: stage structure and seasonality", arXiv:2003.09796 (2020), Theorems 3.5 and 3.6 (Theorem 3.6, Case 1 only), <https://doi.org/10.48550/arXiv.2003.09796>.
- N. D. Hayes, "Roots of the transcendental equation associated with a certain difference-differential equation", J. London Math. Soc. 25 (1950), 226–232, <https://doi.org/10.1112/jlms/s1-25.3.226>.
