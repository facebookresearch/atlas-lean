# Volterra-type Lyapunov inequalities for Caputo derivatives

**Lemma.** Let $0 < \vartheta < 1$ and let $\varphi : [0, \infty) \to (0, \infty)$ be continuous and differentiable. Then for every $\varphi^* > 0$ and every $t \ge 0$,

$$ {}^{C}_{0}D^{\vartheta}_t\left[ \varphi(t) - \varphi^* - \varphi^* \ln\frac{\varphi(t)}{\varphi^*} \right] \le \left(1 - \frac{\varphi^*}{\varphi(t)}\right) {}^{C}_{0}D^{\vartheta}_t \varphi(t),$$

and, for real-valued differentiable $\varphi$,

$$ \tfrac12\, {}^{C}_{0}D^{\vartheta}_t \varphi^2(t) \le \varphi(t)\, {}^{C}_{0}D^{\vartheta}_t \varphi(t).$$

For $\vartheta = 1$ both become the chain-rule equalities.

**Use in fractional epidemic models.** For a Caputo compartmental model ${}^{C}_{0}D^{\vartheta}_t x = f(x)$ with positive endemic equilibrium $x^*$, take the Volterra function $V(x) = \sum_i c_i\big(x_i - x_i^* - x_i^* \ln(x_i/x_i^*)\big)$ with $c_i > 0$. By the lemma,

$${}^{C}_{0}D^{\vartheta}_t V(x(t)) \le \sum_i c_i \Big(1 - \frac{x_i^*}{x_i}\Big) f_i(x),$$

which is exactly the expression $\dot V$ of the integer-order model. Any bound $\sum_i c_i(1 - x_i^*/x_i) f_i(x) \le 0$ proved for $\vartheta = 1$ therefore gives ${}^{C}_{0}D^{\vartheta}_t V \le 0$, and the fractional LaSalle invariance principle yields global asymptotic stability of $x^*$ in the positive orthant. Likewise $V = \tfrac12\sum_i x_i^2$-type functions handle the disease-free equilibrium.

## Depends on

- [Caputo fractional derivative](caputo-fractional-derivative.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

Write $g(u) = u - \varphi^* - \varphi^*\ln(u/\varphi^*)$, which is convex on $(0,\infty)$ with $g'(u) = 1 - \varphi^*/u$. Integrating by parts in the Caputo integral, the difference $g'(\varphi(t))\,{}^{C}D^{\vartheta}\varphi(t) - {}^{C}D^{\vartheta}g(\varphi(t))$ equals a non-negative integral of the convexity gap $g(\varphi(\tau)) - g(\varphi(t)) - g'(\varphi(t))(\varphi(\tau) - \varphi(t)) \ge 0$ against the decreasing kernel $(t-\tau)^{-\vartheta-1}$, plus a non-negative boundary term. The same argument with the convex function $u^2/2$ gives the quadratic inequality. These inequalities make the classical Volterra–Lyapunov method for SIR, SEIR and multi-compartment models carry over to Caputo models unchanged.

## Sources

- P. A. Naik, M. Yavuz, S. Qureshi, J. Zu, S. Townley, "Modeling and analysis of COVID-19 epidemics with treatment in fractional derivatives using real data from Pakistan", European Physical Journal Plus 135 (2020) 795, Section 3 (Lemma 3, Eqs. 27–28, and the global stability analysis that uses them), <https://doi.org/10.1140/epjp/s13360-020-00819-5> (PMC7594999).
- C. Vargas-De-León, "Volterra-type Lyapunov functions for fractional-order epidemic systems", Communications in Nonlinear Science and Numerical Simulation 24 (2015) 75–85, <https://doi.org/10.1016/j.cnsns.2014.12.013>.
