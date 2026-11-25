# The K-allele realization solves the K-allele martingale problem

Let $K \ge 2$ and let $X$ be the continuous coordinate process on $\Delta_{K-1}$ under the [canonical path measure of the neutral $K$-allele Wright–Fisher process](../construction-of-the-neutral-wright-fisher-diffus/k-allele-transition-kernel-and-canonical-path-me.md), without mutation or with parent-independent mutation, with the [continuous modification](../construction-of-the-neutral-wright-fisher-diffus/increment-bound-and-continuous-modification-on-t.md). Then for every $\varphi$ that is $C^2$ on a neighborhood of the simplex, with $L$ the [$K$-allele Wright–Fisher generator](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md),

$$\varphi(X_t) - \varphi(X_0) - \int_0^t L\varphi(X_s)\, ds$$

is a martingale with respect to the natural filtration, so $X$ solves the [$K$-allele martingale problem](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md) for $C^2$ test functions. The proof uses the [Markov property of the continuous canonical process](../strong-markov-property-of-the-wright-fisher-diff-2/markov-property-of-the-continuous-canonical-proc.md) to obtain the martingale identity for polynomials, and then [polynomial approximation of $C^2$ functions on the simplex together with their first and second derivatives](../../../../Analysis/approximation-theory/polynomial-approximation-with-derivatives-in-sev/exists-mv-polynomial-near-cont-diff-on-t-2.md) to pass to $C^2$ test functions.

## Depends on

- [K-allele transition kernel and canonical path measure on the simplex](../construction-of-the-neutral-wright-fisher-diffus/k-allele-transition-kernel-and-canonical-path-me.md)
- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)
- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)
- [Increment bound and continuous modification on the simplex](../construction-of-the-neutral-wright-fisher-diffus/increment-bound-and-continuous-modification-on-t.md)

## Proof depends on

- [Markov property of the continuous canonical process of a Chapman-Kolmogorov family](../strong-markov-property-of-the-wright-fisher-diff-2/markov-property-of-the-continuous-canonical-proc.md)
- [Neutral K-allele semigroup on the simplex via multinomial duality](../wright-fisher-semigroup-and-moment-duality/neutral-k-allele-semigroup-on-the-simplex-via-mu.md)
- [C² polynomial approximation on the simplex](../../../../Analysis/approximation-theory/polynomial-approximation-with-derivatives-in-sev/exists-mv-polynomial-near-cont-diff-on-t-2.md)

## Expansion

A full proof page must still establish:

- the martingale identity for polynomials from the Markov property and the semigroup;
- the $C^2$ extension by simultaneous approximation of values and first and second derivatives;
- that each coordinate $X^i$ solves the two-allele martingale problem, neutral without mutation and with the induced two-type mutation rates under parent-independent mutation.

## Sources

- S. N. Ethier, "A class of degenerate diffusion processes occurring in population genetics", *Communications on Pure and Applied Mathematics* 29(5):483–493, 1976, <https://doi.org/10.1002/cpa.3160290503>
