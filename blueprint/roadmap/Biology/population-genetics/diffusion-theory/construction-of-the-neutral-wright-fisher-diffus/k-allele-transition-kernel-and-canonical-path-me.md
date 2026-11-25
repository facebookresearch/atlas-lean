# K-allele transition kernel and canonical path measure on the simplex

Let $K \ge 2$ and let $(T_t)_{t \ge 0}$ be the [neutral $K$-allele Feller semigroup](../wright-fisher-semigroup-and-moment-duality/neutral-k-allele-semigroup-on-the-simplex-via-mu.md) on $C(\Delta_{K-1})$, without mutation or with parent-independent mutation. Then:

1. **Kernels.** For each $t \ge 0$ and $x \in \Delta_{K-1}$ there is a unique Borel probability measure $P_t(x, \cdot)$ on $\Delta_{K-1}$ with $T_t f(x) = \int f\, dP_t(x, \cdot)$ for every $f \in C(\Delta_{K-1})$, given by the Riesz representation of the positive, unit-preserving functional $f \mapsto T_t f(x)$. The map $x \mapsto P_t(x, A)$ is measurable for every Borel set $A$, $P_0(x, \cdot) = \delta_x$, and the kernels satisfy the Chapman–Kolmogorov equations $P_{s+t} = P_s P_t$.
2. **Path measures.** For each $x \in \Delta_{K-1}$, Kolmogorov's extension theorem gives a unique probability measure $P_x$ on the paths $\omega : [0, \infty) \to \Delta_{K-1}$ with the product $\sigma$-algebra, under which the coordinate process is a Markov process with transition kernels $(P_t)$ started at $x$.

## Depends on

- [Neutral K-allele semigroup on the simplex via multinomial duality](../wright-fisher-semigroup-and-moment-duality/neutral-k-allele-semigroup-on-the-simplex-via-mu.md)
- [Path-space measure of a Markov semigroup](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)

## Proof depends on

- [Positive operators on $C(E)$ are given by Markov kernels](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/exists-markov-kernel-of-positive-operato.md)
- [Kolmogorov extension theorem](../../../../Probability/foundations/kolmogorov-extension-theorem/kolmogorov-extension.md)

## Expansion

A full proof page must still establish:

- the representation, measurability and Chapman–Kolmogorov statements from the Feller property;
- the consistency of the finite-dimensional laws and the extension;
- projection consistency: for each $i$, the coordinate $X^i$ under $P_x$ is the two-allele Wright–Fisher process started at $x_i$: neutral when there is no mutation, and with the induced two-type mutation rates under parent-independent mutation.

## Sources

- S. N. Ethier, "A class of degenerate diffusion processes occurring in population genetics", *Communications on Pure and Applied Mathematics* 29(5):483–493, 1976, <https://doi.org/10.1002/cpa.3160290503>
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 10, Section 2, <https://doi.org/10.1002/9780470316658>
