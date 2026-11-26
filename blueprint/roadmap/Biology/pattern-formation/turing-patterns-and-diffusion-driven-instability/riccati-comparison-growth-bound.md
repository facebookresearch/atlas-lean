# Riccati comparison bound for growth of a second-order non-autonomous linear ODE

This page covers the comparison principle (Theorem 3.1, Corollaries 3.1-3.2 and Theorem 3.2) that Van Gorder, Klika and Krause (2021) use to replace eigenvalue criteria for linear stability on time-dependent domains.

Let $I \subseteq [0, \infty)$ be an interval, $F, G \in C(I)$, and consider
$$\ddot Y + F(t)\, \dot Y + G(t)\, Y = 0 . \qquad (18)$$

**Theorem (growth; Theorem 3.1).** Let $\Phi \in C^2$ with $\Phi(t) > 0$ on $I$. If
$$G(t) \le -\frac{\ddot \Phi}{\Phi} - \frac{\dot \Phi}{\Phi} F(t) \quad \text{for all } t \in I,$$
then (18) has a solution with $|Y(t)| \ge \Phi(t)$ for all $t \in I$ (namely the one with $Y(t_0) = \Phi(t_0)$, $\dot Y(t_0) = \dot\Phi(t_0)$).

**Corollary (exponential and algebraic growth; Corollaries 3.1-3.2).** For a positive $C^2$ scale function $\mu$, taking $\Phi = \mu(t) e^{\delta t}$ or $\Phi = \mu(t) t^{\delta}$ with $\delta > 0$ and letting $\delta \to 0^+$ gives in both cases the same weakest sufficient condition for growth of $Y/\mu$ on $I$:
$$G(t) < -\frac{\ddot \mu}{\mu} - \frac{\dot \mu}{\mu} F(t), \qquad t \in I. \qquad (26)$$

**Theorem (decay complement; Theorem 3.2).** If instead $G(t) > -\ddot\mu/\mu - (\dot\mu/\mu) F(t)$ on $I$, then every solution satisfies $|Y(t)| \le K \mu(t) e^{\delta t}$ and $|Y(t)| \le K \mu(t)(1+t)^{\delta}$ on $I$ for every $\delta > 0$, with $K = O(|Y(t_0)|)$.

Eigenvalues of a time-dependent coefficient matrix predict neither stability nor instability of a non-autonomous system, which is why a criterion of this differential-inequality form is used. When $F, G, \mu$ are constant, (26) reduces to $G < 0$, the condition for a real positive root of $s^2 + Fs + G$.

## Expansion

If equality holds, $\Phi$ itself solves (18). Otherwise write $G = -\ddot\Phi/\Phi - F\dot\Phi/\Phi - H$ with $H \ge 0$ and substitute $Y(t) = Y(t_0)\exp\int_{t_0}^t Z$, which turns (18) into the Riccati equation $\dot Z = -Z^2 - FZ + \ddot\Phi/\Phi + F\dot\Phi/\Phi + H$. The function $Z_1 = \dot\Phi/\Phi$ solves the same equation with $H = 0$ and the same initial value, so the comparison theorem for scalar ODEs gives $Z \ge Z_1$ on $I$; integrating and exponentiating gives $Y \ge \Phi$. The decay statement reverses the inequality and treats the second fundamental solution separately, since it starts at $Y(t_0) = 0$ and cannot be written in exponential form.

## Sources

- R. A. Van Gorder, V. Klika and A. L. Krause, Turing conditions for pattern forming systems on evolving manifolds, *J. Math. Biol.* (2021), Section 3.1, <https://doi.org/10.1007/s00285-021-01552-y>; preprint <https://arxiv.org/abs/1904.09683> (theorem and equation numbers follow the preprint).
