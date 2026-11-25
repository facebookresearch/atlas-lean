# Cubic time scaling of a straight-line joint path

Let $\theta_{\mathrm{start}}, \theta_{\mathrm{end}} \in \mathbb{R}^n$, $\Delta = \theta_{\mathrm{end}} - \theta_{\mathrm{start}}$ and $T > 0$, and consider the straight-line path $\theta(s) = \theta_{\mathrm{start}} + s\Delta$, $s \in [0, 1]$, with a time scaling $s : [0, T] \to [0, 1]$.

1. **Unique cubic.** The only cubic polynomial with $s(0) = 0$, $\dot s(0) = 0$, $s(T) = 1$ and $\dot s(T) = 0$ is $s(t) = 3t^2/T^2 - 2t^3/T^3$; it is nondecreasing on $[0, T]$.
2. **Extremes.** For this time scaling, $\dot\theta_i(t) = (6t/T^2 - 6t^2/T^3)\Delta_i$ has maximal absolute value $\frac{3}{2T}|\Delta_i|$, attained at $t = T/2$, and $\ddot\theta_i(t) = (6/T^2 - 12t/T^3)\Delta_i$ has maximal absolute value $\frac{6}{T^2}|\Delta_i|$, attained at $t = 0$ and $t = T$.
3. **Feasible durations.** Given joint limits $v_i > 0$ and $a_i > 0$, the motion satisfies $|\dot\theta_i(t)| \le v_i$ and $|\ddot\theta_i(t)| \le a_i$ for all $t \in [0, T]$ and all $i$ if and only if

    $$T \ge \max_i \max\Big(\frac{3|\Delta_i|}{2v_i},\ \sqrt{\frac{6|\Delta_i|}{a_i}}\Big).$$

The cubic has nonzero acceleration at both endpoints, so the commanded acceleration jumps there (infinite jerk); this is a property of the cubic, not a violation of the limits above.

**Proof.** Writing $s(t) = a_0 + a_1 t + a_2 t^2 + a_3 t^3$, the endpoint conditions give $a_0 = a_1 = 0$ and the linear system $a_2 T^2 + a_3 T^3 = 1$, $2a_2 T + 3a_3 T^2 = 0$, whose unique solution is $a_2 = 3/T^2$, $a_3 = -2/T^3$. Then $\dot s(t) = 6t(T - t)/T^3 \ge 0$ on $[0, T]$. Part 2: $\dot s$ is a concave quadratic with maximum $3/(2T)$ at $T/2$, and $\ddot s$ is affine with values $\pm 6/T^2$ at the endpoints, and $\dot\theta = \dot s\,\Delta$, $\ddot\theta = \ddot s\,\Delta$. Part 3 follows from part 2 by solving $\frac{3}{2T}|\Delta_i| \le v_i$ and $\frac{6}{T^2}|\Delta_i| \le a_i$ for $T$.

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Section 9.2.2.1, third-order polynomial time scaling (pp. 329–330): the cubic (9.9) with coefficients $a_2 = 3/T^2$, $a_3 = -2/T^3$, the joint trajectory (9.11)–(9.13), the maximal velocity $\frac{3}{2T}(\theta_{\mathrm{end}} - \theta_{\mathrm{start}})$ at $T/2$, the maximal accelerations $\pm\frac{6}{T^2}(\theta_{\mathrm{end}} - \theta_{\mathrm{start}})$ at the endpoints, and the remark that velocity and acceleration limits determine the minimal feasible $T$. The explicit minimal-duration formula is derived on the page.
