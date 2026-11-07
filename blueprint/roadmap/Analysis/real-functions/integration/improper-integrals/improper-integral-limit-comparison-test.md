# Limit comparison test for improper integrals

Let $a, L \in \mathbb{R}$
with $L \ne 0$, and let $f, g : \mathbb{R} \to \mathbb{R}$ be interval integrable on $[a, b]$ for
every $b \ge a$, with $f(x) > 0$ and $g(x) > 0$ for all $x \ge a$. If $f(x) / g(x) \to L$ as
$x \to \infty$, then $\int_a^b f(x)\,dx$ converges to a real limit as $b \to \infty$ if and
only if $\int_a^b g(x)\,dx$ converges to a real limit as $b \to \infty$.

## Sources

- - Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration", entry "comparison test for improper integrals" (currently missing). - T. Apostol, *Mathematical Analysis*, 2nd ed., §10.23 (limit comparison test).
