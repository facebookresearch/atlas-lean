# Wave speed of the one-equation thrombin model by the narrow reaction zone method

**One-equation model.** When the activated factors V, VIII, IX, X, XI equilibrate quickly with thrombin, the coagulation cascade reduces to a scalar equation for the dimensionless thrombin concentration $u$. In the propagation phase, where activation of prothrombin by the prothrombinase complex dominates, it takes the form

$$
\partial_t u = D\,\Delta u + b\,u^n (1 - u) - \sigma u ,
$$

with $n = 3$, $\sigma = 1$ in the dimensionless thrombin model ($b = M_1 M_2 M_3$ a product of dimensionless rate groups, $D$ the rescaled diffusivity), and $n \ge 2$, $b, \sigma, D > 0$ in general. Let $w_* \in (0,1)$ be the largest root of $b w^{n-1}(1-w) = \sigma$, the stable positive equilibrium, so that the equation is bistable between $0$ and $w_*$. A travelling wave $u = w(x - ct)$ solves

$$
D w'' + c w' + b w^n (1 - w) - \sigma w = 0, \qquad w(-\infty) = w_*, \quad w(+\infty) = 0 .
$$

**Estimate (narrow reaction zone).** Concentrating the reaction $F(w) = w^n(1-w)$ at a single point of the moving frame, solving the linear equations $Dw'' + cw' - \sigma w = 0$ ahead and $Dw'' + cw' = 0$ behind the front, and imposing the jump condition $(w'(+0))^2 - (w'(-0))^2 = \tfrac{2}{D}\int_0^{w_*} b F(w)\,\mathrm{d}w$ gives for the approximate speed $\hat c$

$$
\hat c^2 + \hat c\sqrt{\hat c^2 + 4D\sigma} + 2D\sigma = A, \qquad A = 4bD\Big(\frac{w_*^{n-1}}{n+1} - \frac{w_*^{n}}{n+2}\Big),
$$

and hence

$$
\hat c_1 = \frac{A - 2D\sigma}{\sqrt{2A}} .
$$

Numerically $\hat c_1$ underestimates the true speed and the approximation improves as $n$ grows; it is accurate for $n \ge 3$. The resulting formula reproduces the dependence of the thrombin wave speed on $D$ and on the rate constants of the full cascade and agrees in order of magnitude with clot-growth experiments.

## Expansion

The method comes from Zeldovich's combustion theory: when the reaction term is strongly nonlinear ($u^n$ with $n$ large), it is negligible except near the front, where it balances diffusion. Multiplying $D w'' + bF(w) = 0$ by $w'$ and integrating across the thin zone gives the jump in $(w')^2$. Behind the front $w \equiv w_*$, so $w'(-0) = 0$; ahead of it $w = w_* e^{\lambda x}$ with $\lambda = (-c - \sqrt{c^2 + 4D\sigma})/(2D)$, so $w'(+0) = \lambda w_*$. Substituting yields the quadratic-type speed relation above. A complementary piecewise-linear approximation replaces the nonlinearity by $f'(0)w$ below a switching level $w_0$ and $f'(w_*)(w - w_*)$ above it, with $w_0$ chosen to preserve $\int_0^{w_*} f$, and gives an alternative explicit speed estimate.

## Sources

- Tatiana Galochkina, Anass Bouchnita, Polina Kurbatova and Vitaly Volpert, "Reaction-diffusion waves of blood coagulation", arXiv (2016), Section 5 (reduction to a single equation, dimensionless model, narrow reaction zone and piecewise linear speed estimates) and Appendix B, <https://doi.org/10.48550/arXiv.1604.07635>.
- Ya. B. Zeldovich and D. A. Frank-Kamenetskii, "A theory of thermal propagation of flame", Acta Physicochimica URSS 9 (1938).
