# Mutation and substitution loads as path functionals

Consider a biallelic locus whose allele frequency $X$ follows a regular diffusion on $[0, 1]$ with accessible endpoints, absorption time $\tau$, fixation probability $u$ and Green's function $G$, so that $E_p\int_0^\tau g(X_t)\,dt = \int_0^1G(p, \xi)g(\xi)\,d\xi$ for continuous $g$ (Etheridge, lecture notes, Theorem 4.4). A load is the integral of a fitness deficit along the path. For a deleterious mutant with genotype fitnesses $1$, $1 - hs$, $1 - s$ for zero, one and two copies under Hardy–Weinberg proportions, the reduction of mean fitness at frequency $x$ is $d(x) = 2hsx(1 - x) + sx^2$; for an advantageous allele with fitnesses $1$, $1 + hs$, $1 + s$, the deficit relative to the fittest genotype, the reference of the substitutional load (Wikipedia, *Genetic load*, section on substitutional load), is $d(x) = s - 2hsx(1 - x) - sx^2$.

The following definitions and identities are derived. The total deficit of one origin at $p = 1/M$, with $M$ gene copies, is $E_p\int_0^\tau d(X_t)\,dt = \int_0^1G(p, \xi)d(\xi)\,d\xi$. Since the conditional probability of eventual fixation given the path up to $t < \tau$ is $u(X_t)$, the part carried by origins that fix is

$$E_p\Bigl[\int_0^\tau d(X_t)\,dt;\ X_\tau = 1\Bigr] = \int_0^1G(p, \xi)\,d(\xi)\,u(\xi)\,d\xi,$$

and its quotient by $u(p)$, the integral of $d$ against the fixation-conditioned sojourn density, is the deficit per substitution; the difference between the total and the fixation-weighted part is the contribution of origins that are lost. If origins arise as a stationary stream at rate $\lambda$ per unit time, each starting at $1/M$ and evolving independently, the expected deficit accumulated per unit time is $\lambda$ times the total deficit of one origin, by linearity of expectation over the origins.

## Depends on

- [Dirichlet Green's function of a one-dimensional diffusion](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Sojourn density conditioned on fixation](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/conditional-green.md)

## Expansion

1. The deficit functions for deleterious and advantageous alleles with dominance $h$.
2. The total deficit of one origin as a Green potential, and its finiteness for bounded $d$.
3. The fixation-weighted deficit, the deficit per substitution, and the lost-origin remainder.
4. The deficit per unit time of a stationary stream of origins.
5. Source-specific load formulas, such as those of Kimura and Maruyama (1969) for the substitutional load in a finite population, as separate statements.

## Sources

- A. Etheridge, *Diffusion process models in mathematical genetics*, lecture notes, University of Oxford, Section 4 (Theorem 4.4).
- Wikipedia, Genetic load, section on substitutional load. <https://en.wikipedia.org/wiki/Genetic_load>
