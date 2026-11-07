# ML estimate for contour integrals

Let $f : \mathbb{C} \to \mathbb{C}$ and let
$\gamma : [0, 1] \to \mathbb{C}$ be a path from $a$ to $b$ which is continuously differentiable
on $[0, 1]$, with derivative $\gamma'$ (one-sided at the endpoints). Let $M$ and $L$ be real
numbers with $|f(\gamma(t))| \le M$ and $|\gamma'(t)| \le L$ for every $t \in [0, 1]$. If
$t \mapsto f(\gamma(t))\,\gamma'(t)$ is integrable on $[0, 1]$, then
$\left|\int_\gamma f(z)\,dz\right| \le ML$, where
$\int_\gamma f(z)\,dz = \int_0^1 f(\gamma(t))\,\gamma'(t)\,dt$.

The parameter interval has length one, so $L$ bounds the length of $\gamma$.

## Sources

- Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable", entry "contour integrals of continuous functions in ℂ"; L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §1.1 to §1.3 (line integrals).
