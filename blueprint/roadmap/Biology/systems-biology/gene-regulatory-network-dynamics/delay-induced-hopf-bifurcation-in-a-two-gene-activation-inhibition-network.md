# Delay-induced Hopf bifurcation in a two-gene activation–inhibition network

**Model.** Gene $a$ is activated by protein $P_b$ and gene $b$ is repressed by protein $P_a$. With
Hill functions $h^{+}(p; \theta, n) = p^n/(\theta^n + p^n)$ and $h^{-}(p; \theta, n) = \theta^n/(\theta^n + p^n)$,
mRNA concentrations $r_a, r_b$, protein concentrations $p_a, p_b$, and transcriptional and
translational delays $\tau_{ra}, \tau_{rb}, \tau_{pa}, \tau_{pb} \ge 0$, the delayed complete model is

$$\dot r_a = m_a h^{+}\bigl(p_b(t - \tau_{ra}); \theta_b, n_b\bigr) - \gamma_a r_a, \qquad
\dot r_b = m_b h^{-}\bigl(p_a(t - \tau_{rb}); \theta_a, n_a\bigr) - \gamma_b r_b,$$

$$\dot p_a = k_a r_a(t - \tau_{pa}) - \delta_a p_a, \qquad \dot p_b = k_b r_b(t - \tau_{pb}) - \delta_b p_b ,$$

and its quasi-steady-state reduction (fast mRNA) is
$\dot p_a = k_a' h^{+}(p_b(t - \tau_{ra} - \tau_{pa})) - \delta_a p_a$,
$\dot p_b = k_b' h^{-}(p_a(t - \tau_{rb} - \tau_{pb})) - \delta_b p_b$ with $k_i' = m_i k_i/\gamma_i$.
Solutions with nonnegative initial histories (and $r_a(0), r_b(0) > 0$) remain positive.

**Combined delay.** Shifting time in $p_b$ shows that only the total delay
$\tau = \tau_{ra} + \tau_{pa} + \tau_{rb} + \tau_{pb}$ matters. Linearizing the reduced model at a
positive steady state $(\bar p_a, \bar p_b)$ gives the characteristic equation

$$(\lambda + \delta_a)(\lambda + \delta_b) + D\, e^{-\lambda\tau} = 0, \qquad
D = n_a n_b \delta_a \delta_b \frac{\bar p_a^{\,n_a}}{\theta_a^{n_a} + \bar p_a^{\,n_a}} \cdot
\frac{\theta_b^{n_b}}{\theta_b^{n_b} + \bar p_b^{\,n_b}} > 0 .$$

**Theorem.** If $\delta_a \delta_b \ge D$, the steady state is stable for every delay $\tau \ge 0$. If
$\delta_a \delta_b < D$, let

$$\omega_0^2 = \tfrac{1}{2}\Bigl(-(\delta_a^2 + \delta_b^2) + \sqrt{(\delta_a^2 - \delta_b^2)^2 + 4D^2}\Bigr)$$

and let $\tau_0$ be the smallest $\tau > 0$ with $D\cos(\omega_0\tau) = \omega_0^2 - \delta_a\delta_b$ and
$D\sin(\omega_0\tau) = (\delta_a + \delta_b)\omega_0$. Then the steady state is stable for
$0 \le \tau < \tau_0$, unstable for $\tau > \tau_0$, and undergoes a Hopf bifurcation at $\tau = \tau_0$.

**Full model.** For the complete model the characteristic equation is
$\lambda^4 + A\lambda^3 + B\lambda^2 + C\lambda + D_0 + D' e^{-\lambda\tau} = 0$, again depending only on
the total delay. If the delay-free steady state is stable (Routh–Hurwitz:
$ABC - A^2(D_0 + D') - C^2 > 0$) and the transversality condition $g'(\omega_0^2) > 0$ holds for the
associated quartic $g$, the steady state is stable for $\tau < \tau_0$ and loses stability through a
Hopf bifurcation at $\tau_0$.

## Expansion

At $\tau = 0$ the reduced characteristic polynomial $\lambda^2 + (\delta_a + \delta_b)\lambda +
\delta_a\delta_b + D$ has roots with negative real parts, so the undelayed two-gene loop cannot
oscillate, and $\lambda = 0$ is never a root; stability can only be lost by a pair $\lambda = \pm i\omega$.
Substituting $\lambda = i\omega$ and eliminating $\tau$ gives $h(\omega^2) = \omega^4 + (\delta_a^2 +
\delta_b^2)\omega^2 + \delta_a^2\delta_b^2 - D^2 = 0$, which has a positive root exactly when
$\delta_a\delta_b < D$. Along that root $\operatorname{sgn}\, \mathrm{Re}\, d\lambda/d\tau =
\operatorname{sgn}\, h'(\omega_0^2) > 0$, so every crossing is from left to right and stability, once
lost at $\tau_0$, is never regained. Fast protein degradation (large $\delta_a\delta_b$) or weak
feedback gain (small $D$) therefore makes the network robust to arbitrary delays, while slow
turnover with strong regulation turns transcription and translation delays into sustained
oscillations.

## Sources

- K. Parmar, K. B. Blyuss, Y. N. Kyrychko, S. J. Hogan, "Time-Delayed Models of Gene Regulatory
  Networks", Computational and Mathematical Methods in Medicine 2015 (2015) 347273, Eqs. (5)-(6),
  (18)-(30), (31)-(42), Theorem 1, Lemma 2 and Theorem 3, <https://doi.org/10.1155/2015/347273>
  (PMC4632181).
