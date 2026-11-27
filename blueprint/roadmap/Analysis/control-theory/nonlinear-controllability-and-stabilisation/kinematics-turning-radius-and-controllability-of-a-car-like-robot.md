# Kinematics, turning radius and controllability of a car-like robot

A car-like robot has configuration $q = (\varphi, x, y, \psi)$: heading $\varphi$, position $(x, y)$ of the midpoint of the rear axle, and steering angle $\psi$ of a virtual front wheel, with wheelbase $\ell > 0$ and steering limit $0 < \psi_{\max} < \pi/2$. With forward speed $v$ and steering rate $w$ as controls, its kinematics are

$$\dot q = v\, g_1(q) + w\, g_2(q), \qquad g_1(q) = \Big(\frac{\tan\psi}{\ell}, \cos\varphi, \sin\varphi, 0\Big), \quad g_2(q) = (0, 0, 0, 1).$$

1. **Turning radius.** If the steering angle is used directly as a control, the planar motion is that of a unicycle with forward speed $v$ and turning rate $\omega = v\tan\psi/\ell$. The constraint $|\psi| \le \psi_{\max}$ is then equivalent to $|\omega| \le |v|\tan\psi_{\max}/\ell$, so the reference point moves on curves of curvature at most $1/r_{\min}$, with minimum turning radius $r_{\min} = \ell/\tan\psi_{\max}$. A circular arc of radius $r$ is executable exactly when $r \ge r_{\min}$.
2. **Bracket rank.** With $[g_i, g_j] = \frac{\partial g_j}{\partial q}g_i - \frac{\partial g_i}{\partial q}g_j$, let $g_3 = [g_1, g_2] = -\big(\frac{\sec^2\psi}{\ell}, 0, 0, 0\big)$ and $g_4 = [g_1, g_3] = \frac{\sec^2\psi}{\ell}(0, -\sin\varphi, \cos\varphi, 0)$. Then $\det[g_1\ g_2\ g_3\ g_4] = \pm\sec^4\psi/\ell^2 \ne 0$ wherever $|\psi| < \pi/2$.
3. **Controllability within the steering limit.** For any two configurations in $\Omega = \mathbb{R} \times \mathbb{R}^2 \times (-\psi_{\max}, \psi_{\max})$ and any $T > 0$, there is a bounded measurable control $(v, w)$ on $[0, T]$ whose trajectory joins them and stays in $\Omega$. No bound on $|v|$ or $|w|$ is asserted, and backward motion ($v < 0$) is allowed.

**Proof.** Part 1: the first three components of the kinematics with $\psi$ given are $\dot\varphi = v\tan\psi/\ell$, $\dot x = v\cos\varphi$, $\dot y = v\sin\varphi$, and the speed of the reference point is $|v|$, so the curvature is $|\dot\varphi|/|v| = |\tan\psi|/\ell \le \tan\psi_{\max}/\ell$, since $\tan$ is increasing on $(-\pi/2, \pi/2)$; conversely every curvature up to that bound is attained by a constant $\psi$. Part 2: $g_2$ is constant and $g_1$ depends on $\psi$ only through its first entry, which gives $g_3 = -\partial g_1/\partial\psi$; the first entry of $g_3$ depends only on $\psi$, and $g_1$ has no $\psi$-component, so $g_4 = -\frac{\partial g_1}{\partial q}g_3$, which is the stated vector. Expanding the determinant along the $\psi$-row, where only $g_2$ is nonzero, leaves a $3 \times 3$ determinant equal to $\pm\big(\frac{\sec^2\psi}{\ell}\big)^2$. Part 3 is the Rashevskii–Chow theorem on the connected open set $\Omega$, where both fields are smooth.

## Proof depends on

- [Rashevskii–Chow theorem](rashevskii-chow.md): controllability of a smooth driftless system satisfying the Lie algebra rank condition on a connected open set

## Background

- [The unicycle satisfies the Lie algebra rank condition and is controllable](the-unicycle-satisfies-the-lie-algebra-rank-condition-and-is-controllable.md): the three-dimensional model obtained when the steering angle is a control

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Section 13.3.1.3, the car-like robot: Ackermann steering and the minimum turning radius $r_{\min}$ (Figure 13.10), the kinematics (13.16) with steering limit $|\psi| \le \psi_{\max}$ (p. 525), the conversion (13.17) between $(v, \psi)$ and $(v, \omega)$ and the simplified model (13.18) (pp. 525–526); and Theorem 13.7 on the Lie algebra rank condition (p. 535). The bracket computation and the turning-radius formula are derived on the page.
