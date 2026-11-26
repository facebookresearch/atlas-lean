# No-flux solution of the gradient-drift Fokker–Planck equation

Let $\Psi : \mathbb{R} \to \mathbb{R}$, $D, a, b \in \mathbb{R}$, $I \subseteq \mathbb{R}$ a set of times, and $p : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, and
write $G(t, x) = p(t, x)\, \Psi'(x) + D\, \partial_x p(t, x)$ for the [negative flux](neg-flux.md). Then $p$
is a no-flux solution of the gradient-drift Fokker–Planck equation on $[a, b]$ for $t \in I$ if

1. $\partial_t p(t, x) = \partial_x G(t, x)$ for all $t \in I$ and $x \in [a, b]$;
2. $G(t, a) = 0$ for all $t \in I$;
3. $G(t, b) = 0$ for all $t \in I$.

The equation is $\partial_t p = \partial_x (p \Psi' + D \partial_x p)$, with zero flux at both ends.
