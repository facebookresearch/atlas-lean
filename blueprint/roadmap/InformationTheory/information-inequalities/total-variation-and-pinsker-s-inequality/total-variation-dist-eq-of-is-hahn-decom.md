# Total variation is attained at a Hahn set

Let $\mu$ and $\nu$ be probability measures on a measurable space and let $s$ be a Hahn set for
$(\mu, \nu)$: $s$ is measurable, $\mu(t \cap s) \le \nu(t \cap s)$ and $\nu(t \cap s^c) \le \mu(t \cap s^c)$
for every set $t$. Then

$$
\mathrm{TV}(\mu, \nu) = \sup_B |\mu(B) - \nu(B)| = \nu(s) - \mu(s).
$$

A Hahn set exists for any two finite measures, so the supremum over events is always attained.

## Background

- [Total variation distance](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md):
  the supremum definition.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 7.7(a); the maximising event is `{dν/dμ' > dμ/dμ'}` there.
