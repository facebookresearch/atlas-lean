# Dissipation identity

Let $a \le b$, $D \in \mathbb{R}$, $\Psi$ of class $C^2$, $I \subseteq \mathbb{R}$ open, and $p$ of class $C^2$ in $(t, x)$ with
$p(t, x) > 0$ for all $t \in I$ and $x \in \mathbb{R}$, a [no-flux solution](is-no-flux-solution-on.md) of the
gradient-drift Fokker–Planck equation on $[a, b]$ for $t \in I$. Then for every $t \in I$ the [free
energy](free-energy.md) is differentiable at $t$, with

$$F'(t) = -\int_a^b p(t, x) \bigl( \Psi'(x) + D\, \partial_x \log p(t, x) \bigr)^2 dx .$$

Only the values of $p$ on $[a, b]$ enter $F$; positivity is asked of the whole function $p(t, \cdot)$ so
that $\log p(t, \cdot)$ is $C^2$.
