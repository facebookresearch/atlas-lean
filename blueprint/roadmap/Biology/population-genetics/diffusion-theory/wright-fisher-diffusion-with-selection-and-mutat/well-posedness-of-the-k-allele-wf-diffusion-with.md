# Well-posedness of the K-allele Wright–Fisher diffusion with diploid selection

Let $K \ge 2$, let $w_{ij}$ be symmetric per-generation genotype fitnesses, $i, j = 1, \dots, K$, and let $W_{ij} = M (w_{ij} - w_{\mathrm{ref}})$ be the diffusion-scaled fitness matrix, for any constant $w_{\mathrm{ref}}$, in time units of $M$ generations. With $a_{ij}(x) = x_i(\delta_{ij} - x_j)$ and $V(x) = \frac{1}{2} x^{\top} W x$, the selection drift is a Shahshahani gradient,

$$x_i\bigl((W x)_i - x^{\top} W x\bigr) = (a \nabla V)_i.$$

1. **Neutral or parent-independent mutation.** Tilting the $K$-allele diffusion of [the $K$-allele realization](../neutral-wright-fisher-martingale-problem/k-allele-realization-solves-the-k-allele-marting.md) by $e^{V}$, with [the tilted path measure](../construction-of-the-neutral-wright-fisher-diffus/tilted-path-measure-on-a-canonical-space-generic.md) and [the martingale problem under an exponential tilt](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md), gives a solution with selection, and the inverse tilt with [the uniqueness in law for the $K$-allele martingale problem](../neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-k-allele-martingale-pr.md) gives uniqueness.
2. **General bounded mutation matrix $Q$.** The statement is conditional: given any solution of the $K$-allele martingale problem with mutation matrix $Q$, the tilt produces a solution with selection, and uniqueness follows from [the uniqueness in law with general bounded $Q$](../neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-k-allele-martingale-pr.md). Existence for general $Q$ is a separate result.

## Depends on

- [Tilted path measure on a canonical space (generic consistent extension)](../construction-of-the-neutral-wright-fisher-diffus/tilted-path-measure-on-a-canonical-space-generic.md)
- [Martingale problem under exponential tilt (generic)](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md)
- [K-allele realization solves the K-allele martingale problem](../neutral-wright-fisher-martingale-problem/k-allele-realization-solves-the-k-allele-marting.md)
- [Uniqueness in law for the K-allele martingale problem with general bounded Q](../neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-k-allele-martingale-pr.md)

## Proof depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](k-allele-wright-fisher-generator-on-the-simplex.md)

## Expansion

1. The gradient identity for the selection drift.
2. Boundedness of $\mathcal{L} e^{V} / e^{V}$ on the simplex, and the two parts above.
3. A check against [the generator of the $K$-allele diffusion with mutation and genic selection](k-allele-wright-fisher-generator-on-the-simplex.md) when $W$ comes from genic fitnesses.

## Sources

- M. Steinrücken, Y. X. R. Wang and Y. S. Song, An explicit transition density expansion for a multi-allelic Wright–Fisher diffusion with general diploid selection, *Theor. Popul. Biol.* 83 (2013), 1–14 (general diploid selection).
- A. D. Barbour, S. N. Ethier and R. C. Griffiths, A transition function expansion for a diffusion model with selection, *Ann. Appl. Probab.* 10 (2000), 123–162, <https://ora.ox.ac.uk/objects/uuid:90fb09ec-c270-4094-8f30-f2a439b42f29> (selection by a change of measure).
