# Pinsker's inequality for the total variation norm

For probability measures $\mu$ and $\nu$ on a measurable space,

$$
\frac{\|\mu - \nu\|^2}{2} \le D(\mu \,\|\, \nu),
$$

where $\|\mu - \nu\|$ is the total variation norm (with values in $[0, 2]$)
and $D$ the Kullback–Leibler divergence with the natural logarithm. This is
[Pinsker's inequality](of-real-two-mul-total-variation-dist-sq.md) rewritten with
$\|\mu - \nu\| = 2\,\mathrm{TV}(\mu, \nu)$.

## Informally uses

- [Total variation norm is twice the supremum over events](tv-dist-eq-two-mul-total-variation-dist.md):
  the change of convention.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 7.10, with `tvDist = 2 TV` (Theorem 7.7(a)).
