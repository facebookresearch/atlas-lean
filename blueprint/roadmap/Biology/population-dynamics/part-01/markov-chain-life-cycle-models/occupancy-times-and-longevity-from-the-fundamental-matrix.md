# Occupancy times and longevity from the fundamental matrix

**Setting.** A life cycle with $s$ living stages (for example pre-breeder, successful breeder, failed breeder, non-breeder) and an absorbing state, death, is an absorbing Markov chain. Let $U$ be the $s \times s$ transient matrix, $U_{ij}$ the probability that a living individual in stage $j$ is alive and in stage $i$ one time step later, with spectral radius $< 1$. Let $\mathbf 1$ be the vector of ones and $\circ$ the elementwise product.

**Proposition.**

1. The *fundamental matrix* $N = (I - U)^{-1}$ exists, and $N_{ij}$ is the expected number of time steps spent in stage $i$ by an individual starting in stage $j$.
2. The variances of these occupancy times are the entries of

$$V = \bigl(2 N_{\mathrm{dg}} - I\bigr) N - N \circ N,$$

where $N_{\mathrm{dg}}$ is the diagonal matrix with the diagonal of $N$.
3. The longevity $\eta$ (time to absorption) of an individual starting in each stage has mean vector and variance vector

$$\bar\eta^{\mathsf T} = \mathbf 1^{\mathsf T} N, \qquad V(\eta^{\mathsf T}) = \mathbf 1^{\mathsf T} N (2N - I) - \bar\eta^{\mathsf T} \circ \bar\eta^{\mathsf T}.$$

## Proof depends on

- [Neumann series](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/inv-one-sub-nonneg.md)

## Expansion

$N = \sum_{t \ge 0} U^t$ counts expected visits. Second moments follow from the renewal argument that the number of visits to $i$, given at least one, is geometric with mean $N_{ii}$, giving $\mathbb E[\text{visits}^2] = (2N_{\mathrm{dg}} - I)N$. For longevity, $\eta$ satisfies $\mathbb E[\eta^2] = \mathbf 1^{\mathsf T} N (2N - I)$ by first-step analysis; subtracting the squared mean gives the variance. Even individuals with identical vital rates differ in outcome through these variances (individual stochasticity).

## Sources

- S. Jenouvrier, L. M. Aubry, C. Barbraud, H. Weimerskirch and H. Caswell, "Interacting effects of unobserved heterogeneity and individual stochasticity in the life history of the southern fulmar", *Journal of Animal Ecology* (2018), Section on Markov chain demographic outcomes, Eqs. (4)–(7). <https://doi.org/10.1111/1365-2656.12752> (PMC5765524)
