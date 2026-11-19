# Traveling wave solves the Fisher–KPP equation

Let $D, r, c \in \mathbb{R}$ with $D \ne 0$, and let $(U, U')$ be a [traveling-wave profile](is-wave-profile.md) of speed $c$. For all real $x$ and $t$ there
is a number $U''$ such that $y \mapsto U'(y - ct)$ has derivative $U''$ at $y = x$ and

$$-c\,U'(x - ct) = D\,U'' + r\,U(x - ct)\bigl(1 - U(x - ct)\bigr).$$

Together with the [time](has-deriv-at-wave-t.md) and [space](has-deriv-at-wave-x.md) derivatives, the
wave $u(x, t) = U(x - ct)$ solves $\partial_t u = D \partial_x^2 u + r u(1 - u)$.
