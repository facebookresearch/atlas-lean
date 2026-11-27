# Finite-time prey extinction and refuge rescue under a generalized Holling response

**Model.** Let $x_1$ be prey and $x_2$ predator densities, with positive constants $a_1, b_1$ (prey growth and self-limitation), $a_2$ (predator death), $w_0, w_1$ (predation and conversion), $d$ (half-saturation), a feeding exponent $0 < m_1 \le 1$ and a mutual-interference exponent $0 < m_2 \le 1$:

$$\dot x_1 = a_1 x_1 - b_1 x_1^2 - w_0 \Bigl(\frac{x_1}{x_1 + d}\Bigr)^{m_1} x_2^{m_2}, \qquad \dot x_2 = -a_2 x_2 + w_1 \Bigl(\frac{x_1}{x_1 + d}\Bigr)^{m_1} x_2^{m_2}.$$

Solutions with positive initial data stay nonnegative and are bounded, and the system is dissipative (Lemmas 2.1-2.3; in particular $\limsup_{t\to\infty} x_1(t) \le a_1/b_1$). The nonnegative equilibria are $E_0 = (0,0)$, $E_1 = (a_1/b_1, 0)$ and interior points $E_2 = (x_1^*, x_2^*)$ with $x_2^* = \frac{w_1}{w_0 a_2}(a_1 x_1^* - b_1 x_1^{*2})$, of which there may be one or several.

**Theorem 4.1 (finite-time prey extinction).** Let $0 < m_1 < 1$. There are positive initial data for which $x_1$ reaches $0$ at a finite time. Specifically, if $x_1(0)$ is small enough that

$$\bigl(x_1(0)\bigr)^{1-m_1}\bigl(x_1(0) + d\bigr)^{m_1} \le \frac{w_0}{a_1}$$

and $x_2(0)$ is large enough, then $x_1(t) \to 0$ as $t \to T^{**} < \infty$. (At $m_1 = 1$ the prey equation reads $\dot x_1 = x_1[a_1 - b_1x_1 - w_0x_2^{m_2}/(x_1+d)]$, whose bracket is bounded below along bounded solutions, so $x_1$ stays positive and the theorem fails. The condition is the comparison inequality $a_1 u_0 (1 + d u_0)^{m_1} \le w_0 u_0^2$ for $u_0 = 1/x_1(0)$; the final display of the proof in the source writes $a_0$ for $a_1$.)

**Theorem 5.1 (a refuge prevents finite-time extinction).** Replace $x_1$ by $r x_1$ inside the functional response of both equations, where $r \in [0,1]$ is the fraction of prey exposed to predators ($r = 1$ recovers the model, $r = 0$ is complete protection). For any initial condition with $0 < x_1(0) < a_1/b_1$ and $x_2(0) > 0$ whose prey component goes extinct in finite time when $r = 1$, there is a threshold $r^* > 0$, depending on $x_1(0)$, the parameters and an upper bound $K_2$ for the predator, such that for every refuge level $r < r^*$ the prey does not go extinct in finite time.

## Expansion

With $u = 1/x_1$ the prey equation becomes

$$\dot u = -a_1 u + b_1 + w_0 \frac{u^2}{(1 + d u)^{m_1}} x_2^{m_2},$$

so finite-time extinction of $x_1$ is finite-time blow-up of $u$. Since $\dot x_2 \ge -a_2 x_2$, the predator stays above $x_2(0) e^{-a_2 t}$, and if $x_2(0)$ is large this keeps $x_2^{m_2} \ge 1$ on the relevant time interval. The comparison equation $\dot{\tilde u} = -a_1 \tilde u + w_0 \tilde u^2 (1 + d\tilde u)^{-m_1}$ has superlinear growth of order $\tilde u^{2 - m_1}$, with $2 - m_1 > 1$, so it blows up in finite time once the quadratic term dominates at the initial value; the displayed condition on $x_1(0)$ expresses that domination. With a refuge the extra term is bounded by $w_0 r^{m_1} d^{-m_1} u^{2-m_1} K_2^{m_2}$, and shrinking $r$ makes the linear decay $-a_1 u$ dominate along the trajectory, so $u$ stays bounded. Finite-time extinction is possible only because the vector field is not Lipschitz at $x_1 = 0$ when $m_1 < 1$: the classical uniqueness argument that keeps the prey-free axis from being reached in finite time does not apply.

## Sources

- K. Antwi-Fordjour, R. D. Parshad, M. A. Beauregard, "Dynamics of a predator-prey model with generalized Holling type functional response and mutual interference" (2020), Section 2 (model and Lemmas 2.1-2.3), Section 3 (equilibria), Section 4 (Theorem 4.1) and Section 5 (Theorem 5.1), <https://doi.org/10.48550/arXiv.2003.02712>.
