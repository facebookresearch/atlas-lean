# The unicycle satisfies the Lie algebra rank condition and is controllable

The kinematic unicycle (a differential-drive robot) has configuration $q = (x, y, \varphi) \in \mathbb{R}^3$, forward speed $v$ and turning rate $\omega$, and moves by

$$\dot q = v\, g_1(q) + \omega\, g_2(q), \qquad g_1(q) = (\cos\varphi, \sin\varphi, 0), \quad g_2(q) = (0, 0, 1).$$

1. **Bracket.** With $[g_i, g_j] = \frac{\partial g_j}{\partial q} g_i - \frac{\partial g_i}{\partial q} g_j$, one has $[g_1, g_2](q) = (\sin\varphi, -\cos\varphi, 0)$, and $\det\big[g_1(q)\ \ g_2(q)\ \ [g_1, g_2](q)\big] = 1$ for every $q$. So the Lie algebra rank condition holds at every point of $\mathbb{R}^3$.
2. **Controllability.** For all $q_0, q_1 \in \mathbb{R}^3$ and every $T > 0$ there are a bounded measurable control $(v, \omega) : [0, T] \to \mathbb{R}^2$ and a trajectory from $q_0$ at time $0$ to $q_1$ at time $T$.
3. **The rolling constraint is not integrable.** Every trajectory satisfies the no-slip constraint $\dot x \sin\varphi - \dot y \cos\varphi = 0$, yet there is no differentiable function $F$ on an open set $U \subseteq \mathbb{R}^3$ with nowhere-vanishing gradient that is constant along all trajectories in $U$. The constraint restricts velocities but not reachable configurations.

**Proof.** In part 1, $\partial g_2/\partial q = 0$ and $\frac{\partial g_1}{\partial q} g_2 = (-\sin\varphi, \cos\varphi, 0)$, so $[g_1, g_2] = -(-\sin\varphi, \cos\varphi, 0)$; the determinant of the matrix with columns $(\cos\varphi, \sin\varphi, 0)$, $(0, 0, 1)$, $(\sin\varphi, -\cos\varphi, 0)$ is $\cos^2\varphi + \sin^2\varphi = 1$. Part 2 is the Rashevskii–Chow theorem on $\Omega = \mathbb{R}^3$, the vector fields being smooth. For part 3, the constraint holds because $\dot x = v\cos\varphi$ and $\dot y = v\sin\varphi$. If $F$ were constant along all trajectories in $U$, its derivative along $g_1$, $g_2$ and hence $[g_1, g_2]$ would vanish, since $F$ is constant along the flows of $g_1$ and $g_2$ and the bracket is a limit of compositions of these flows; by part 1 the gradient of $F$ would vanish, a contradiction. Equivalently, by part 2 the configurations reachable from a point fill a neighborhood, which no level set of $F$ does.

## Proof depends on

- [Rashevskii–Chow theorem](rashevskii-chow.md): controllability of a smooth driftless system satisfying the Lie algebra rank condition on a connected open set

## Background

- [The nonholonomic integrator satisfies the Lie algebra rank condition](accessibility-space-nonholonomic-fields.md): the same rank argument for the nonholonomic integrator

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Chapter 13: the unicycle and diff-drive kinematics and the no-slip constraint (Section 13.3), the Lie bracket of vector fields (13.28) (p. 532) and Theorem 13.7 (p. 535), the Lie algebra rank condition gives small-time local controllability when the controls positively span. The bracket and determinant computation and the non-integrability argument are on the page.
