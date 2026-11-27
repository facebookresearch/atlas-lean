# A retrospective sampling model for allele age

Watterson (1977) treats the age of an allele in two-allele models through time reversal, as a retrospective question. In a neutral two-allele model an allele $a$ arose once as a mutation in a population otherwise fixed for $A$, there is no further mutation, and the current frequency of $a$ is $x$; so $0$ and $1$ are absorbing. The age of $a$ is then the time for the reversed process to go from $x$ down to $0$, conditioned on not reaching $1$. A birth–death process with a stationary distribution is reversible by detailed balance (Kelly 1979, Chapter 1), and for the diffusion the reversal is taken with respect to the speed measure. Conditioning a diffusion with generator $\frac12\sigma^2(x)f'' + \mu(x)f'$ to leave $[0, 1]$ at $0$ gives, by Bayes' rule and the Markov property (Ewens 1973), the transition density $p^*(t, x, y) = p(t, x, y)(S(1) - S(y))/(S(1) - S(x))$, where $S$ is the scale function, and a diffusion with the same infinitesimal variance and drift

$$\mu^*(x) = \mu(x) - \sigma^2(x)\,\frac{S'(x)}{S(1) - S(x)}.$$

The expected age follows by applying the Green's-function formula for occupation integrals to the conditioned reversed diffusion. Maruyama and Kimura (1975, abstract) compute, for a diffusion model, any moment of the sum of a function of gene frequency along sample paths between two specified frequencies, and use it for the mean age of a mutant at frequency $x$, including or excluding the possibility that it was at frequency $1$ in the past. The interpretation of these ages through time reversal of the diffusion is a separate statement, the [process interpretation of allele age via time reversal](process-interpretation-of-allele-age-via-time-re.md).

## Depends on

- [Maruyama–Kimura conditional sojourn density](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/age-density.md)
- [Mean age of an allele at a given frequency](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age.md)
- [Dirichlet Green's function of a one-dimensional diffusion](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Scale function of a one-dimensional diffusion](../selection-duality-and-general-one-dimensional-di/scale-function.md)

## Expansion

1. A birth–death chain with a stationary distribution and its reversibility by detailed balance.
2. The diffusion conditioned to leave $[0, 1]$ at $0$: its transition density and the drift $\mu^*$, derived from the exit probability $(S(1) - S(y))/(S(1) - S(x))$.
3. The expected age as the Green's-function integral for the conditioned process.
4. The mean age including, and the mean age excluding, earlier periods at frequency $1$, as two statements.

## Sources

- G. A. Watterson, Reversibility and the age of an allele II. Two-allele models, with selection and mutation, Theor. Popul. Biol. 12 (1977), 179–196. <https://doi.org/10.1016/0040-5809(77)90041-7>
- W. J. Ewens, Conditional diffusion processes in population genetics, Theor. Popul. Biol. 4 (1973), 21–30.
- F. P. Kelly, *Reversibility and Stochastic Networks*, Wiley, 1979, Chapter 1.
- T. Maruyama and M. Kimura, Moments for sum of an arbitrary function of gene frequency along a stochastic path of gene frequency change, Proc. Natl. Acad. Sci. USA 72 (1975), 1602–1604, abstract. <https://doi.org/10.1073/pnas.72.4.1602>
