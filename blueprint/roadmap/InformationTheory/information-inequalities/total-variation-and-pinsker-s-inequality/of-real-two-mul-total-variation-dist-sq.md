# Pinsker's inequality for probability measures

Let $\mu$ and $\nu$ be probability measures on an arbitrary measurable space. Then

$$
2\,\mathrm{TV}(\mu, \nu)^2 \le D(\mu \,\|\, \nu),
$$

where $\mathrm{TV}(\mu, \nu) = \sup_B |\mu(B) - \nu(B)|$ and $D$ is the Kullback–Leibler divergence
(natural logarithm, valued in $[0, \infty]$). No positivity, finiteness or
absolute-continuity hypothesis is needed; $D(\mu \,\|\, \nu) = \infty$ when $\mu$ is not absolutely
continuous with respect to $\nu$.

The proof follows Polyanskiy and Wu: the data-processing inequality for $D$ applied to the
indicator of a Hahn set $s$ gives
$D(\mu \,\|\, \nu) \ge D(\mathrm{Ber}(\mu(s)) \,\|\, \mathrm{Ber}(\nu(s)))$, and the
[binary Pinsker inequality](../binary-pinsker-of-mem-icc.md) bounds the right side below by
$2 (\nu(s) - \mu(s))^2 = 2\,\mathrm{TV}(\mu, \nu)^2$.

## Informally uses

- [Total variation is attained at a Hahn set](total-variation-dist-eq-of-is-hahn-decom.md):
  the event on which the reduction to Bernoulli laws is made.
- [Binary Pinsker inequality on the closed interval](../binary-pinsker-of-mem-icc.md):
  the two-point case.
- [Kullback–Leibler divergence on a finite space](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md):
  evaluates the divergence between the two Bernoulli laws.

## Background

- [Csiszár–Kullback–Pinsker inequality for strictly positive distributions](../csiszar-kullback-pinsker.md):
  the earlier finite, strictly positive special case.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 7.10 (stated there as `D ≥ 2 log e · TV²`); M. S. Pinsker, Information and Information Stability of Random Variables and Processes (1964).
