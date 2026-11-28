# Rate-control and effort-control optimality systems for age-structured harvesting

**Setting (rate control).** A population with age density $x(t,a)$, $a \in (0,A)$, $A < \infty$, nonnegative initial profile $x_0 \in L^1(0,A)$ and bounded mortality $\mu(t,a) \ge 0$ is harvested at an age-specific rate $u(t,a) \in [0,u_{\max}]$ and replenished at age zero by a boundary inflow $p(t) \in [0,p_{\max}]$:

$$\partial_t x + \partial_a x = -\mu(t,a)\,x - u(t,a), \qquad x(t,0) = p(t), \qquad x(0,a) = x_0(a),$$

subject to the pure state constraint $x \ge 0$. With discount rate $r > 0$, unit harvest value $c(t,a) \ge 0$ and inflow cost $k(t) \ge 0$ (both bounded), maximise

$$J(u,p) = \int_0^\infty e^{-rt}\Big(\int_0^A c(t,a)\,u(t,a)\,da - k(t)\,p(t)\Big)\,dt .$$

**Theorem (existence).** If the control-to-state map is affine and weak-$\ast$-to-$L^1_{\mathrm{loc}}$ sequentially continuous and the admissible set is nonempty (it always contains $u \equiv 0$), an optimal pair $(u^\ast,p^\ast)$ exists.

**Theorem (conditional maximum principle).** Assume (the source's (R1)–(R7)): (R1) $c, \mu \in L^\infty((0,\infty)\times(0,A))$, $k \in L^\infty(0,\infty)$, $r > 0$, $x_0 \in L^1(0,A)$ with $x_0 \ge 0$, and the box constraints on $(u,p)$; (R2) for every admissible $(u,p)$ the state equation has a unique mild solution $x = S(u,p) \in L^1_{\mathrm{loc}}([0,\infty);L^1(0,A))$; (R3) $S$ is Gâteaux differentiable along admissible directions, with derivative $\delta x$ the unique mild solution of the linearised system; (R4) $\int_0^\infty e^{-rt}\big(\int_0^A|cu|\,da + |kp|\big)dt < \infty$ for every admissible $(u,p)$; (R5) $e^{-rt}\lambda \in W^{1,1}_{\mathrm{loc}}((0,\infty)\times(0,A))$ and $\eta \in L^1_{\mathrm{loc}}((0,\infty)\times(0,A))$, $\eta \ge 0$; (R6) the products $e^{-rt}\lambda\,\delta x$, $e^{-rt}\lambda\,\partial_t\delta x$, $e^{-rt}\lambda\,\partial_a\delta x$ are integrable on finite cylinders, the integration-by-parts identities hold, and the boundary pairing at infinity vanishes; (R7) the state constraint $x \ge 0$ is qualified, so that a multiplier $\eta \ge 0$ with $\eta\,x^\ast = 0$ a.e. exists. Then an optimal $(u^\ast,p^\ast,x^\ast)$ admits a current-value adjoint $\lambda$ and multiplier $\eta \ge 0$ with

$$\partial_t \lambda + \partial_a \lambda = (r+\mu)\lambda - \eta, \qquad \lambda(t,A) = 0,$$

a discounted transversality condition $\lim_{T\to\infty}\int_0^A e^{-rT}\lambda(T,a)\,\delta x(T,a)\,da = 0$, complementary slackness $\eta\,x^\ast = 0$, and bang-bang/singular switching laws: $u^\ast$ is governed by the sign of $c - \lambda$ (zero where negative, $u_{\max}$ where positive) and $p^\ast$ by the sign of $\lambda(t,0) - k(t)$. Given $\eta$, $\lambda$ is unique, obtained by integrating backward along characteristics from $a = A$; in the autonomous stationary case

$$\lambda(a) = \int_a^A \exp\Big(-\int_a^s (r+\mu(\xi))\,d\xi\Big)\,\eta(s)\,ds .$$

**Effort control (contrast).** If instead harvest is proportional to stock, $-w(t,a)\,x$, and mortality depends on total stock $E(t) = \int_0^A x\,da$, the formal adjoint gains a nonlocal term:

$$\partial_t\lambda + \partial_a\lambda = \big(r + \mu(E,a) + w\big)\lambda - c\,w + \int_0^A \mu_E(E,s)\,x(t,s)\,\lambda(t,s)\,ds,$$

and the switching function for $w$ is $e^{-rt}x\,(c - \lambda)$.

## Expansion

Because the rate-control objective is linear in the controls and the state map is affine, existence follows from weak-$\ast$ compactness of the bounded control set and closedness of the convex admissible set. The adjoint is derived by perturbing the Lagrangian and integrating by parts along the characteristic lines $t - a = \text{const}$; the positive discount rate closes the transversality estimate whenever the linearised state grows at an exponential rate below $r$. The structural point is that in rate control the adjoint is local in age and is driven only by the state-constraint multiplier, so the shadow value of a fish of age $a$ is its discounted future harvest value; in effort control, density-dependent mortality couples all ages through $E(t)$, and every backward step must evaluate an integral over the whole age profile. In the stationary case the state is explicit: $x(a) = p\,e^{-\int_0^a\mu} - \int_0^a e^{-\int_s^a \mu}\,u(s)\,ds$ (rate) versus $x(a) = p\,e^{-\int_0^a(\mu(E,\xi)+w(\xi))\,d\xi}$ (effort).

## Sources

- Jiguang Yu, Louis Shuo Wang, Ye Liang, "Age‐Structured Harvesting Models: A Structural Comparison of Rate‐Control and Effort‐Control Optimality Systems", International Journal of Mathematics and Mathematical Sciences 2026 (2026), 6212516, <https://doi.org/10.1155/ijmm/6212516>. Published version of arXiv:2603.09767, cited next; locators there refer to the arXiv version.
- Jiguang Yu, Louis Shuo Wang, Ye Liang, "Age-Structured Harvesting Models: A Structural Comparison of Rate-Control and Effort-Control Optimality Systems", arXiv:2603.09767 (2026), Problem 4.1, Theorem 4.3, Lemma 4.6, Theorem 4.8, Proposition 5.1 and Propositions 6.3–6.5, <https://doi.org/10.48550/arXiv.2603.09767>.
