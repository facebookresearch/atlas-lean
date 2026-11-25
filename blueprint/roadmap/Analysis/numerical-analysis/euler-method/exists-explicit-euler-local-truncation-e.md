# Uniform quadratic bound on the explicit Euler local error

Let $E$ be a real normed
space, let $t_0 < T$ be real numbers, let $f : \mathbb{R} \times E \to E$ be $C^2$, and let
$x : \mathbb{R} \to E$ be differentiable at every $t \in [t_0, T]$ with $x'(t) = f(t, x(t))$.
Then there is a constant $C \ge 0$ such that
$\|x(t + h) - (x(t) + h f(t, x(t)))\| \le C h^2$ for every $h \in (0, T - t_0]$ and every
$t \in [t_0, T]$ with $t + h \le T$.
