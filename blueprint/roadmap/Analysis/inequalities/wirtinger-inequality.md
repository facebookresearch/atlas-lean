# Wirtinger's inequality

Let $f, f' : \mathbb{R} \to \mathbb{R}$ be functions such that
for every $x \in [0, \pi]$ the function $f$ has derivative $f'(x)$ at $x$ within $[0, \pi]$, $f'$
is continuous on $[0, \pi]$, and $f(0) = f(\pi) = 0$. Then
$\int_0^\pi f(x)^2 \, dx \le \int_0^\pi f'(x)^2 \, dx$.

Proof: A Picone-type comparison. For `0 < c < 1` the weight `h x = -c * tan (c * (x - π / 2))` is
smooth on `[0, π]` with `h' + h ^ 2 = -c ^ 2`, so integrating
`f' ^ 2 = (f' - h * f) ^ 2 + (h * f ^ 2)' + c ^ 2 * f ^ 2` gives `c ^ 2 * ∫ f ^ 2 ≤ ∫ f' ^ 2`;
then let `c` tend to one.

## Sources

- G. H. Hardy, J. E. Littlewood, and G. Pólya, *Inequalities*, second edition, Cambridge University Press, 1952, §7.7 (the endpoint-zero form on `[0, L]`).
