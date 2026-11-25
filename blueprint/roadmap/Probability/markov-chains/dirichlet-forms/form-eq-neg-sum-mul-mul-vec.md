# The form of a reversible generator is $-\langle f, Qg \rangle_m$

Let $S$ be a finite set, $m : S \to \mathbb{R}$ and $Q$ a real $S \times S$ matrix in detailed
balance with $m$: $m(x) Q(x, y) = m(y) Q(y, x)$ for all $x, y$. Then the [form](form.md) of
$(m, Q)$ satisfies, for all $f, g : S \to \mathbb{R}$,

$$\mathcal E(f, g) = -\sum_{x} m(x)\, f(x)\, (Qg)(x), \qquad (Qg)(x) = \sum_y Q(x, y)\, g(y) .$$

Fukushima, Oshima and Takeda write this as $\mathcal E(f, g) = -(Qf, g)_{L^2(m)}$, which is the
same by symmetry.

## Sources

- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and extended ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, Example 1.2.5.
