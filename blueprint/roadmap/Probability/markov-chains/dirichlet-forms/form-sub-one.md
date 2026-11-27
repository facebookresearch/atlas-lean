# The Dirichlet form of a Markov kernel

Let $S$ be a finite set, $m : S \to \mathbb{R}$, and $P$ a real $S \times S$ matrix whose rows sum
to $1$. Then the [form](form.md) of the generator $P - I$ is, for all $f, g : S \to \mathbb{R}$,

$$\mathcal E_{m, P - I}(f, g) = \frac{1}{2} \sum_{x, y} m(x) P(x, y) \bigl(f(x) - f(y)\bigr)\bigl(g(x) - g(y)\bigr);$$

in particular $\mathcal E_{m, P - I}(f, f) = \frac{1}{2} \sum_{x, y} m(x) P(x, y) (f(x) - f(y))^2$.
This is equation (1.2.27) of Fukushima, Oshima and Takeda with $q_{ij} = P(i, j)$ for $i \ne j$
and $k = 0$, and the Dirichlet form of equation (1.4) of Diaconis and Saloff-Coste.

## Sources

- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and extended ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, equation (1.2.27).
- P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*, Annals of Applied Probability 6 (1996), 695–750, equation (1.4).
