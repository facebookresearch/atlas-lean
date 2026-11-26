# Fixation probabilities under frequency-dependent selection

For a diffusion approximation on $[0, 1]$ with infinitesimal mean $M(p) = E(\Delta p)$ and infinitesimal second moment $V(p) = E[(\Delta p)^2]$, the fixation probability $U(p)$ solves the backward equation $M(p)U'(p) + \frac12V(p)U''(p) = 0$ with $U(0) = 0$ and $U(1) = 1$, and

$$U(p) = \frac{\int_0^pG(x)\,dx}{\int_0^1G(x)\,dx}, \qquad G(x) = \exp\Bigl(-2\int_c^x\frac{M(y)}{V(y)}\,dy\Bigr)$$

(Kimura 1962, equations (3)–(4); Ewens 2004, Chapter 4). Kimura's derivation uses $M$ and $V$ only as functions of the current frequency, so it applies when fitnesses depend on $p$. Comparison with neutrality follows from the shape of $G$ (derivation): if $M \ge 0$ on $(0, 1)$ then $G$ is nonincreasing, $p \mapsto \int_0^pG$ is concave and lies above its chord, and $U(p) \ge p$; if $M \le 0$ then $U(p) \le p$. When $M$ changes sign, the sign of $U(p) - p$ can depend on $p$. Example (derivation): for $V(p) = p(1 - p)$ and $M(p) = \alpha p(1 - p)(1 - 2p)$ with $\alpha > 0$, a type favoured when rare and disfavoured when common, $G(x) = \exp(-2\alpha x(1 - x))$ is symmetric about $1/2$ and decreasing on $[0, 1/2]$, so the average of $G$ over $[0, p]$ exceeds its average over $[0, 1]$ for $0 < p < 1/2$; hence $U(p) > p$ for $0 < p < 1/2$, $U(1/2) = 1/2$ and, by the symmetry $U(1 - p) = 1 - U(p)$, $U(p) < p$ for $1/2 < p < 1$.

## Depends on

- [Dirichlet ratio $S(p)/S(1)$ of the scale function](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/fixation-prob.md)
- [The scale-function ratio solves the Dirichlet problem](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/fixation-prob-solves.md)

## Expansion

1. The backward equation for the fixation probability with a frequency-dependent infinitesimal mean, and its solution by the scale function when $G$ is integrable.
2. The comparisons $U(p) \ge p$ for $M \ge 0$ and $U(p) \le p$ for $M \le 0$, by concavity or convexity of the scale function.
3. The symmetric example with $M(p) = \alpha p(1 - p)(1 - 2p)$ and the sign change of $U(p) - p$ at $p = 1/2$.
4. Infinitesimal means arising from frequency-dependent fitnesses in pairwise games, as a separate statement with its own source.

## Sources

- M. Kimura, On the probability of fixation of mutant genes in a population, Genetics 47 (1962), 713–719, equations (3)–(4). <https://doi.org/10.1093/genetics/47.6.713>
- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004), Chapter 4.
