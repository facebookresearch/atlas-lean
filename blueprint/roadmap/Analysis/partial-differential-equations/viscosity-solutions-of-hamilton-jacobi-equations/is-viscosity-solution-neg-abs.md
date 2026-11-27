# $-|x|$ is a viscosity solution of $(u')^2 - 1 = 0$ on $\mathbb{R}$

The function $u(x) = -|x|$ is a viscosity solution of $(u')^2 - 1 = 0$ on all of $\mathbb{R}$, kink
included. Away from $0$ it is a classical solution. At $0$, every $C^1$ function touching $u$ from
above satisfies $\varphi(t) - \varphi(0) \ge -|t|$ near $0$, so its slope lies in $[-1, 1]$ and
$\varphi'(0)^2 - 1 \le 0$; and no $C^1$ function touches $u$ from below at $0$, so the supersolution
condition is empty there.

By contrast [$|x|$ is not a viscosity supersolution](not-is-viscosity-supersolution-abs.md). Since
$|x| = -(-|x|)$, a viscosity solution of $F = 0$ need not give one of $-F = 0$ after a change of
sign: the theory is one-sided, which is what makes it select the physically relevant solution.

## Sources

- M. G. Crandall, H. Ishii and P.-L. Lions, "User's guide to viscosity solutions of second order partial differential equations", Bull. Amer. Math. Soc. 27 (1992), 1–67, arXiv:math/9207212, Remark 2.5.
