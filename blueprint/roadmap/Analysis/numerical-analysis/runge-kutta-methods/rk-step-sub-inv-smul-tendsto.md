# Consistency of explicit Runge–Kutta methods

Let $E$ be a real normed vector space,
let $f(t, y)$ be a vector field $\mathbb{R} \times E \to E$, let $t \in \mathbb{R}$ and
$y \in E$, and for an explicit Runge–Kutta method with weights $b$ let $y_1(h)$ be the
result of one step of size $h$ from the state $y$ at time $t$. If $\sum_i b_i = 1$ and $f$
is continuous at $(t, y)$ as a function of both variables, then
$h^{-1} (y_1(h) - y) \to f(t, y)$ as $h \to 0$ with $h \neq 0$.
