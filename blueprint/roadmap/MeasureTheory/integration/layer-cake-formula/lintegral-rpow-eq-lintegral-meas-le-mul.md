# Layer-cake formula for powers

Let $\mu$ be a measure on a set $\alpha$ with a σ-algebra, let $f \colon \alpha \to \mathbb{R}$ be almost everywhere
measurable with $f \ge 0$ almost everywhere, and let $p > 0$. Then

$$\int f^p \, d\mu = p \int_{(0, \infty)} \mu(\{x : t \le f(x)\}) \, t^{p-1} \, dt$$

in $[0, \infty]$, with Lebesgue measure on $(0, \infty)$. Both sides are integrals of functions with values in
$[0, \infty]$: on the left, $f(x)^p$ is replaced by $0$ where it is negative, which can happen only where $f < 0$.
