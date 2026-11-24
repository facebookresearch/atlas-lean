# Accuracy of the diffusion approximation for finite-population fixation

The fixation probability of an allele in the finite Wright–Fisher chain is the solution of a linear system, and the diffusion formula is an approximation to it. Felsenstein (Section VII.8, Table 7.5) compares the exact fixation probabilities $U(p)$ of the Wright–Fisher model with $N = 10$ diploids and multiplicative selection with the diffusion approximation $(1 - e^{-4Nsp})/(1 - e^{-4Ns})$. For $s = 0.01$ the two agree to within $2.4 \times 10^{-4}$ at the tabulated frequencies $p = 0.05$ to $0.7$, for example $0.54959$ exact against $0.54983$ at $p = 0.5$; for $s = 0.1$ the approximation is too large, by $0.00592$ at $p = 0.05$ ($0.17873$ against $0.18465$) and by $0.00973$ at $p = 0.5$ ($0.87107$ against $0.88080$). Felsenstein attributes the good performance at such a small $N$ to a general property of the approximation, even when the frequency changes by a few large jumps. For the neutral model with mutation, Ethier and Norman bound the difference between the expectations of a smooth function of the frequency under the chain and under the diffusion by a combination of the maximum mutation rate and the reciprocal of the population size.

## Depends on

- [Error of the diffusion approximation to the Wright–Fisher model](../../../../Biology/population-genetics/diffusion-theory/diffusion-limit-of-the-wright-fisher-model/error-of-the-diffusion-approximation.md)
- [Fixation probability with selection in the finite Wright–Fisher model](../../../../Biology/population-genetics/wright-fisher-markov-chain/fixation-probability-with-selection-in-the-finite-chain.md)
- [Wright–Fisher diffusion limit, generator form](../../../../Biology/population-genetics/diffusion-theory/diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md)

## Expansion

1. The finite chain with multiplicative selection and its fixation probabilities as the solution of the linear system with boundary values $0$ and $1$.
2. The tabulated comparison at $N = 10$ for $s = 0.01$ and $s = 0.1$, recomputed from the linear system.
3. Convergence of the chain's fixation probabilities to the diffusion formula as $N \to \infty$ with $4Ns$ and $p$ fixed, with a rate.
4. The neutral error bound for smooth test functions and its consequence for fixation, as a separate statement.

## Sources

- J. Felsenstein, Theoretical Evolutionary Genetics, course text, University of Washington, Section VII.8, subsection Numerical examples and Table 7.5.
- S. N. Ethier and M. F. Norman, Error estimate for the diffusion approximation of the Wright–Fisher model, Proc. Natl. Acad. Sci. USA 74 (1977), 5096–5098, abstract. <https://doi.org/10.1073/pnas.74.11.5096>
