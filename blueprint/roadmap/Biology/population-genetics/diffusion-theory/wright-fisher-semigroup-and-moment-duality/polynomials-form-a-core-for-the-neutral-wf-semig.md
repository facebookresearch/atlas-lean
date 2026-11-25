# Polynomials form a core for the neutral Wright–Fisher semigroup

Let $P_t$ be the neutral Wright–Fisher semigroup on $C[0, 1]$, without selection or mutation, with generator $A$, and let $\mathcal{L}_0 = \frac{1}{2} x(1 - x) \frac{d^2}{dx^2}$ on the polynomials. Then the closure of $(\mathcal{L}_0, \text{polynomials})$ in $C[0, 1]$ is $A$. Indeed, the polynomials are invariant under $P_t$ and lie in $D(A)$, by [the generator on polynomials](tendsto-wf-semigroup-sub-div.md), and for $\lambda > 0$, $\lambda - \mathcal{L}_0$ maps the polynomials of degree at most $n$ onto themselves, because $\mathcal{L}_0$ is triangular in the degree. So the range of $\lambda - \mathcal{L}_0$ is dense.

## Depends on

- [Generator of the Wright–Fisher diffusion on polynomials](tendsto-wf-semigroup-sub-div.md)
- [Strongly continuous contraction semigroups, generators and cores](../../../../Analysis/operator-theory/strongly-continuous-contraction-semigroups.md)

## Proof depends on

- [Range criterion for a core of a semigroup generator](../../../../Analysis/operator-theory/core-criterion-for-semigroup-generators.md)

## Expansion

1. The range condition, from triangularity.
2. $P_t$ maps polynomials to polynomials, from [the generator on polynomials](tendsto-wf-semigroup-sub-div.md).
3. The core property from the range condition and the invariance.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 1, Section 3 (cores) and Chapter 8.
- W. Feller, The parabolic differential equations and the associated semi-groups of transformations, *Ann. of Math.* 55 (1952), 468–519, <https://doi.org/10.2307/1969644> (generator domains).
