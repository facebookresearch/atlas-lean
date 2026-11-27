# Routh–Hurwitz criterion for cubic polynomials

Let $a_0, a_1, a_2 \in \mathbb{R}$ and $p(s) = s^3 + a_2 s^2 + a_1 s + a_0$. Then every complex root of $p$ has negative real part if and only if

$$a_2 > 0, \qquad a_0 > 0, \qquad a_2 a_1 > a_0 .$$

These conditions imply $a_1 > 0$, since $a_2 a_1 > a_0 > 0$ with $a_2 > 0$. All three inequalities are strict and none can be dropped:

- $s^3 + s^2 + s + 1 = (s + 1)(s^2 + 1)$ has $a_2 a_1 = a_0$ and roots $\pm i$ on the imaginary axis;
- $s^3 + s^2 + 2s$ has $a_0 = 0$ and the root $0$;
- $s^3 - s^2 - 2s + 1$ has $a_2 = -1 < 0$, while $a_0 = 1 > 0$ and $a_2 a_1 = 2 > a_0$; its roots sum to $1$, so one of them has positive real part.

**Proof.** A real cubic has a real root $-r$, so $p(s) = (s + r)(s^2 + bs + c)$ with real $r, b, c$, and then $a_2 = r + b$, $a_1 = rb + c$, $a_0 = rc$. The roots of $p$ are $-r$ and the roots of $s^2 + bs + c$. Both roots of the quadratic have negative real part exactly when $b > 0$ and $c > 0$: their sum is $-b$ and their product is $c$; if they are not real, they are conjugate with real part $-b/2$ and $c = |\lambda|^2 > 0$, and if they are real, both are negative exactly when their sum is negative and their product positive. So $p$ is Hurwitz if and only if $r, b, c > 0$. Moreover

$$a_2 a_1 - a_0 = (r + b)(rb + c) - rc = b\,(r^2 + rb + c).$$

- If $r, b, c > 0$, then $a_2, a_0 > 0$ and $a_2 a_1 - a_0 > 0$.
- Conversely, suppose $a_2 > 0$, $a_0 > 0$ and $a_2 a_1 > a_0$. Then $a_1 > 0$, so $p(\sigma) \ge \sigma^3 + a_0 > 0$ for every $\sigma \ge 0$; hence the real root $-r$ is negative, that is, $r > 0$. Then $c = a_0 / r > 0$, so $r^2 + rb + c = r(r + b) + c = r a_2 + c > 0$, and $b\,(r^2 + rb + c) > 0$ gives $b > 0$.

## Background

- [Routh–Hurwitz criterion for $2 \times 2$ matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/exists-eigenvalue-re-pos-iff.md): the non-strict form, applied to the companion matrix of $s^2 + bs + c$: no root has positive real part exactly when $b \ge 0$ and $c \ge 0$

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 2.2, "Stability: The Routh–Hurwitz Criterion" (p. 2-10), condition (2.18) for third-order equations, stated there without proof.
