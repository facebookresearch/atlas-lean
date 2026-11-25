# Uniqueness in law for the K-allele martingale problem with a general bounded mutation matrix

Let $K \ge 2$, let $Q = (q_{ij})$ be a $K \times K$ rate matrix (nonnegative off-diagonal entries, zero row sums), and let $L$ be the [$K$-allele Wright–Fisher generator](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md) on $\Delta_{K-1}$ without selection,

$$L\varphi(x) = \frac12 \sum_{i,j=1}^K x_i(\delta_{ij} - x_j)\, \partial_i \partial_j \varphi(x) + \sum_{i=1}^K \Bigl(\sum_{j=1}^K x_j q_{ji}\Bigr) \partial_i \varphi(x).$$

Since the drift is linear and the diffusion coefficients are quadratic, $L$ maps the polynomials of degree at most $n$ into themselves for every $n$. By the [conditional polynomial-semigroup identity](conditional-polynomial-semigroup-identity-for-ma.md), [semigroup-free uniqueness](semigroup-free-uniqueness-conditional-polynomial.md) and [moment determinacy](moment-determinacy-on-compact-subsets-of-r-d-sim.md) on products of simplices, any two solutions of the martingale problem for $L$ on polynomials with the same initial law have the same finite-dimensional distributions. Existence is not claimed for a general $Q$; for neutral or parent-independent mutation, [the $K$-allele realization solves the martingale problem](k-allele-realization-solves-the-k-allele-marting.md), so the problem is well posed. This is the $K$-allele uniqueness result used by the [lookdown identification](../fleming-viot-processes/lookdown-directing-process-is-the-finite-type-fl.md) and the [finite-type Fleming–Viot correspondence](../fleming-viot-processes/finite-type-fleming-viot-k-allele-wright-fisher.md). Genic selection is handled separately by an exponential tilt.

## Depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)
- [Conditional polynomial-semigroup identity for martingale-problem solutions with triangular generators](conditional-polynomial-semigroup-identity-for-ma.md)
- [Semigroup-free uniqueness: conditional polynomial identities determine finite-dimensional laws](semigroup-free-uniqueness-conditional-polynomial.md)
- [Moment determinacy on compact subsets of Euclidean space](moment-determinacy-on-compact-subsets-of-r-d-sim.md)

## Expansion

A full proof page must still check the degree-preservation property of $L$ and assemble the three lemmas. Existence for mutation matrices that are not parent-independent is a separate result.

## Sources

- S. N. Ethier, "A class of degenerate diffusion processes occurring in population genetics", *Communications on Pure and Applied Mathematics* 29(5):483–493, 1976, <https://doi.org/10.1002/cpa.3160290503> (background)
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 10, Section 2, <https://doi.org/10.1002/9780470316658> (background)
