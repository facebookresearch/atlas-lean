# Two-point testing bound

Let $\mu$ and $\nu$ be probability measures on a measurable space. For every measurable event $A$
(the test that decides for $\nu$ on $A$ and for $\mu$ on $A^c$), the sum of its two error
probabilities satisfies

$$
\mu(A) + \nu(A^c) \ge 1 - \mathrm{TV}(\mu, \nu).
$$

Together with [its attainment](exists-add-compl-eq-one-sub-total-variat.md), the least total
error of a test between $\mu$ and $\nu$ is exactly $1 - \mathrm{TV}(\mu, \nu)$.

## Informally uses

- [Total variation is attained at a Hahn set](total-variation-dist-eq-of-is-hahn-decom.md):
  the bound is checked against the Hahn set.

## Background

- [Neyman–Pearson lemma](../../../Probability/hypothesis-testing/neyman-pearson-dominated-two-simple.md):
  the likelihood-ratio test minimising one error under a constraint on the other; here the two errors are added with equal weights.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 7.7(a), eq. (7.19).
