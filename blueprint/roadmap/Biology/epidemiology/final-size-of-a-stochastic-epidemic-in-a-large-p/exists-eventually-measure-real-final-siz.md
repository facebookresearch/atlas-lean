# R₀ > 1, few immune, θ > 0: a δ₀ > 0 has P(F < δ₀N) ≤ q + θ eventually as N → ∞

For each $k \in \mathbb{N}$ let the offspring numbers $\xi^{(k)}_{n,i}$ and the contact targets
$U^{(k)}_j$ form a [final-size epidemic model](is-final-size-epidemic.md) on a probability space
$(\Omega_k, P_k)$, in a population of size $N_k$ with a set $S_0^{(k)}$ of $\#S_0^{(k)}$ initially
susceptible individuals, all with the same offspring law $\nu$, a probability measure on
$\mathbb{N}$ with $\int x^2 \, d\nu(x) < \infty$ and real mean $R_0 = \int x \, d\nu(x) > 1$. Assume
$N_k \to \infty$ and $(N_k - \#S_0^{(k)})/N_k \to 0$ as $k \to \infty$ (few immune: the individuals
that are not initially susceptible form a vanishing fraction). Let $F_k$ be the
[final size](final-size.md) of model $k$ and $q$ the
[extinction probability](../../../Probability/branching-processes/galton-watson-process/extinction-prob.md)
of the Galton–Watson process with offspring law $\nu$. For every real $\theta > 0$ there is
$\delta_0 > 0$ such that, for all sufficiently large $k$,
$P_k\bigl(F_k < \delta_0 N_k\bigr) \le q + \theta$.
