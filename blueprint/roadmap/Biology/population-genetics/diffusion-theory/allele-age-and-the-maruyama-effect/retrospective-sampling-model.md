# A retrospective sampling model for allele age

Etheridge's lecture notes (Example 5.5) pose the age of an allele as a retrospective question. In a neutral two-allele model an allele $a$ arose once as a mutation in a population otherwise fixed for $A$, there is no further mutation, and the current frequency of $a$ is $x$; so $0$ and $1$ are absorbing. To obtain a reversible chain, the approximating Moran model is modified: whenever the frequency of $a$ hits $0$ it is returned to $1/N$ at rate $\epsilon$, and the state $N$ is likewise given a transition at rate $\epsilon$. The age of $a$ is then the time for the reversed process to go from $x$ down to $0$, conditioned on not reaching $1$, in the limit $\epsilon \to 0$. A birth–death process with a stationary distribution is reversible by detailed balance (Lemma 5.4), and for the diffusion the reversal is taken with respect to the speed measure. Conditioning a diffusion with generator $\frac12\sigma^2(x)f'' + \mu(x)f'$ to leave $[0, 1]$ at $0$ gives, by Bayes' rule and the Markov property, the transition density $p^*(t, x, y) = p(t, x, y)(S(1) - S(y))/(S(1) - S(x))$, where $S$ is the scale function, and a diffusion with the same infinitesimal variance and drift

$$\mu^*(x) = \mu(x) - \sigma^2(x)\,\frac{S'(x)}{S(1) - S(x)}.$$

The expected age follows by applying the Green's-function formula for occupation integrals (Theorem 4.4) to the conditioned reversed diffusion. Maruyama and Kimura (1975, abstract) compute, for a diffusion model, any moment of the sum of a function of gene frequency along sample paths between two specified frequencies, and use it for the mean age of a mutant at frequency $x$, including or excluding the possibility that it was at frequency $1$ in the past. The interpretation of these ages through time reversal of the diffusion is a separate statement.

## Depends on

- [Maruyama–Kimura conditional sojourn density](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/age-density.md)
- [Mean age of an allele at a given frequency](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age.md)
- [Dirichlet Green's function of a one-dimensional diffusion](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)

## Expansion

1. The modified Moran chain with return rate $\epsilon$ at both absorbing states, its stationary distribution and its reversibility by detailed balance.
2. The diffusion conditioned to leave $[0, 1]$ at $0$: its transition density and the drift $\mu^*$, derived from the exit probability $(S(1) - S(y))/(S(1) - S(x))$.
3. The limit $\epsilon \to 0$ and the expected age as the Green's-function integral for the conditioned process.
4. The mean age including, and the mean age excluding, earlier periods at frequency $1$, as two statements.

## Sources

- A. Etheridge, Diffusion process models in mathematical genetics, lecture notes, University of Oxford, Lemma 5.4, Example 5.5 and Theorem 4.4.
- T. Maruyama and M. Kimura, Moments for sum of an arbitrary function of gene frequency along a stochastic path of gene frequency change, Proc. Natl. Acad. Sci. USA 72 (1975), 1602–1604, abstract. <https://doi.org/10.1073/pnas.72.4.1602>
