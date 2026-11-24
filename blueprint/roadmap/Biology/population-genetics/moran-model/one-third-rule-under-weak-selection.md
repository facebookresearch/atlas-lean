# The one-third rule for weak selection in the Moran process

In a population of $N \ge 2$ playing a $2 \times 2$ game with payoffs $a, b$ (an $A$-player against $A$, $B$) and $c, d$ (a $B$-player
against $A$, $B$), with no self-interaction, let $i$ be the number of $A$-players and
$f_i = \frac{a(i - 1) + b(N - i)}{N - 1}$, $g_i = \frac{c i + d(N - i - 1)}{N - 1}$ the expected payoffs, and fitnesses
$1 - w + w f_i$ and $1 - w + w g_i$ with selection intensity $w \ge 0$ small enough that all fitnesses are positive. Let $\rho_A(w)$ be the
[fixation probability](frequency-dependent-moran-fixation-product-formu.md) of a single $A$-player. Then $\rho_A(0) = 1/N$ and

$$\frac{d\rho_A}{dw}\Big|_{w=0} = -\frac{1}{N^2} \sum_{i=1}^{N-1} (N - i)(g_i - f_i) = \frac{a(N - 2) + b(2N - 1) - c(N + 1) - d(2N - 4)}{6N} .$$

In the coordination case $a > c$, $d > b$, with interior equilibrium $x^* = (d - b)/(a - b - c + d)$, the numerator equals
$N(a + 2b - c - 2d) - (2a + b + c - 4d)$, and $a + 2b - c - 2d$ has the sign of $\frac13 - x^*$. Hence, if $x^* < \frac13$, then for all
sufficiently large $N$ weak selection favors the fixation of $A$, $\rho_A(w) > 1/N$ for all sufficiently small $w > 0$; if
$x^* > \frac13$, it opposes it for large $N$. If $x^* = \frac13$, the sign of the derivative at each $N$ is that of
$-(2a + b + c - 4d)$; for example $(a, b, c, d) = (2, 3, 0, 4)$ has $x^* = \frac13$ and derivative $3/(2N)$.

## Depends on

- [Fixation probability in a frequency-dependent Moran process](frequency-dependent-moran-fixation-product-formu.md)

## Sources

- M. A. Nowak, A. Sasaki, C. Taylor and D. Fudenberg, "Emergence of cooperation and evolutionary stability in finite populations", Nature 428 (2004), 646–650, <https://doi.org/10.1038/nature02414>. The derivative is computed from the fixation formula, with $\gamma_i(0) = 1$ and $\gamma_i'(0) = g_i - f_i$, and the closed form checked exactly in rational arithmetic on random games.
