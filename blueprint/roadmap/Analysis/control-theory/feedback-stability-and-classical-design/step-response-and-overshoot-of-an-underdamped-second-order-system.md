# Step response and overshoot of an underdamped second-order system

Let $\omega > 0$ and $0 < \zeta < 1$, and put $\omega_d = \omega\sqrt{1 - \zeta^2}$ and $\varphi = \arccos \zeta$. The unique solution on $[0, \infty)$ of

$$\ddot x + 2\zeta\omega\, \dot x + \omega^2 x = \omega^2, \qquad x(0) = \dot x(0) = 0,$$

is

$$x(t) = 1 - e^{-\zeta\omega t}\Big(\cos \omega_d t + \frac{\zeta}{\sqrt{1 - \zeta^2}} \sin \omega_d t\Big) = 1 - \frac{e^{-\zeta\omega t}}{\sqrt{1 - \zeta^2}}\, \sin(\omega_d t + \varphi).$$

Its derivative is $\dot x(t) = \dfrac{\omega}{\sqrt{1 - \zeta^2}}\, e^{-\zeta\omega t} \sin \omega_d t$, and $x(t) \to 1$ as $t \to \infty$. The maximum of $x$ on $[0, \infty)$ is attained at the first positive critical point $t^* = \pi/\omega_d$, and the overshoot is

$$\max_{t \ge 0} x(t) - 1 = x(t^*) - 1 = e^{-\pi\zeta/\sqrt{1 - \zeta^2}} .$$

**Proof.**

- **Solution.** With $a = \zeta\omega$ and $b = \omega_d$, so $a^2 + b^2 = \omega^2$, differentiating gives the stated $\dot x$. A second differentiation shows that $x$ satisfies the equation, and $x(0) = \dot x(0) = 0$. The difference of two solutions solves the homogeneous first-order system for $(x, \dot x)$ with zero initial value; extended by $0$ to $t < 0$ it is still a solution on $\mathbb{R}$, so it vanishes, which gives uniqueness.
- **Critical points.** $\dot x(t) = 0$ for $t > 0$ exactly at $t_k = k\pi/\omega_d$, $k \ge 1$, where $x(t_k) = 1 - (-1)^k e^{-k\pi\zeta/\sqrt{1 - \zeta^2}}$.
- **Maximum.** The values at odd $k$ exceed $1$ and decrease in $k$. The values at even $k$, at $t = 0$ and as $t \to \infty$ are at most $1$. Hence the maximum on $[0, \infty)$ is at $k = 1$.

## Proof depends on

- [Global existence and uniqueness for homogeneous linear ODEs](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/exists-unique-has-deriv-at-eq-continuous.md): uniqueness for the equivalent first-order system $\frac{d}{dt}(x, \dot x) = (\dot x, -\omega^2 x - 2\zeta\omega \dot x) + (0, \omega^2)$, applied to the difference of two solutions

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 7.3: the second-order system (7.22)–(7.23) (p. 7-18), its step response (7.24) for $\zeta < 1$ and the form (7.25) with $\varphi = \arccos \zeta$ (pp. 7-19–7-20), and the maximum overshoot $M_p = e^{-\pi\zeta/\sqrt{1-\zeta^2}}$ (p. 7-20 and Table 7.1).
