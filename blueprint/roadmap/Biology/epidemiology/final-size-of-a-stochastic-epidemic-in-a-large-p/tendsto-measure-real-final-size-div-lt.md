# With R₀ > 1, 0 < δ < τ and few immune, P(F/N < δ) tends to q

For each $k \in \mathbb{N}$ let the offspring numbers $\xi^{(k)}_{n,i}$ and the contact targets
$U^{(k)}_j$ form a [final-size epidemic model](is-final-size-epidemic.md) on a probability space
$(\Omega_k, P_k)$, in a population of size $N_k$ with a set $S_0^{(k)}$ of $\#S_0^{(k)}$ initially
susceptible individuals, all with the same offspring law $\nu$, a probability measure on
$\mathbb{N}$ with $\int x^2 \, d\nu(x) < \infty$ and real mean $R_0 = \int x \, d\nu(x) > 1$. Assume
$N_k \to \infty$ and $(N_k - \#S_0^{(k)})/N_k \to 0$ as $k \to \infty$ (few immune: the individuals
that are not initially susceptible form a vanishing fraction). Let $F_k$ be the
[final size](final-size.md) of model $k$, a function of the outcome (as $N_k \ge 1$ under the model,
$F_k/N_k$ is the fraction of the population ultimately infected), $q$ the
[extinction probability](../../../Probability/branching-processes/galton-watson-process/extinction-prob.md)
of the Galton–Watson process with offspring law $\nu$, and $\tau = \tau(R_0) \in (0, 1)$ the
[positive root](final-size-root.md) of the final-size equation $1 - \tau = e^{-R_0 \tau}$. For every
real $\delta$ with $0 < \delta < \tau$,
$P_k\Bigl(\frac{F_k}{N_k} < \delta\Bigr) \longrightarrow q \quad (k \to \infty)$.
