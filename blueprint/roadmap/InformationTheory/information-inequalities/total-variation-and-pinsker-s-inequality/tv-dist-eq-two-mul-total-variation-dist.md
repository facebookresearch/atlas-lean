# Total variation norm is twice the supremum over events

For probability measures $\mu$ and $\nu$ on a measurable space, the total variation norm
$\|\mu - \nu\|$ (with values in $[0, 2]$) satisfies

$$
\|\mu - \nu\| = 2 \sup_B |\mu(B) - \nu(B)| = 2\,\mathrm{TV}(\mu, \nu).
$$

This identifies two conventions for the total variation distance: the total variation norm
$\|\mu - \nu\|$ and the [supremum over events](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md), which is the convention of Polyanskiy and Wu,
$\mathrm{TV}(P, Q) = \tfrac12 \int |dP - dQ|$. On a finite set, the [total variation distance of functions](../../../Probability/markov-chains/mixing-times-of-markov-chains/tv-dist.md) $\tfrac12 \sum_y |\mu(y) - \nu(y)|$
also equals $\mathrm{TV}$, half of the total variation norm.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 7.7(a), the identity `TV(P, Q) = sup_E (P(E) - Q(E))` for `TV(P, Q) = ½ ∫ |dP - dQ|`.
