# Mutation Wright–Fisher transition kernel and canonical path measure

Let $\theta_1, \theta_2 \ge 0$, $\theta = \theta_1 + \theta_2$, and let $(P^\theta_t)_{t \ge 0}$ be the [Feller semigroup of the two-allele Wright–Fisher diffusion with mutation](../wright-fisher-semigroup-and-moment-duality/mutation-wf-feller-semigroup-via-polynomial-dual.md) on $C([0, 1])$, without selection. Then:

1. **Kernels.** For each $t \ge 0$ and $x \in [0, 1]$ there is a unique Borel probability measure $K^\theta_t(x, \cdot)$ on $[0, 1]$ with $P^\theta_t f(x) = \int f(y)\, K^\theta_t(x, dy)$ for all $f \in C([0, 1])$, by the Riesz representation of the positive, unit-preserving functional $f \mapsto P^\theta_t f(x)$. These kernels are measurable in $x$, satisfy $K^\theta_0(x, \cdot) = \delta_x$ and the Chapman–Kolmogorov equations $K^\theta_{s+t} = K^\theta_s K^\theta_t$, and have mean

    $$\int y\, K^\theta_t(x, dy) = \frac{\theta_1}{\theta} + \Bigl(x - \frac{\theta_1}{\theta}\Bigr) e^{-\theta t/2} \qquad (\theta > 0),$$

    and $\int y\, K^\theta_t(x, dy) = x$ when $\theta = 0$.
2. **Path measures.** For each $x$ there is a unique probability measure $P^\theta_x$ on $[0, 1]^{[0, \infty)}$ with the product $\sigma$-field whose finite-dimensional laws are those of the Markov chain with transitions $(K^\theta_t)$ started at $x$, by Kolmogorov's extension theorem.

## Depends on

- [Mutation WF Feller semigroup via polynomial duality and chain limits](../wright-fisher-semigroup-and-moment-duality/mutation-wf-feller-semigroup-via-polynomial-dual.md)
- [Path-space measure of a Markov semigroup](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)

## Proof depends on

- [Positive operators on $C(E)$ are given by Markov kernels](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/exists-markov-kernel-of-positive-operato.md)
- [Kolmogorov extension theorem](../../../../Probability/foundations/kolmogorov-extension-theorem/kolmogorov-extension.md)

## Expansion

A full proof page must still establish:

- the representation, measurability and Chapman–Kolmogorov statements from the Feller property;
- the mean formula, from the generator $\tfrac12 y(1-y) f'' + \tfrac12(\theta_1(1-y) - \theta_2 y) f'$ applied to $f(y) = y$;
- the consistency of the finite-dimensional laws and the extension.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 10, Sections 1–2, <https://doi.org/10.1002/9780470316658>
- S. N. Ethier, "A class of degenerate diffusion processes occurring in population genetics", *Communications on Pure and Applied Mathematics* 29(5):483–493, 1976, <https://doi.org/10.1002/cpa.3160290503>
