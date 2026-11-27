# Common part of two probability measures

For probability measures $\mu$ and $\nu$ on a measurable space there is a measure $m$ with
$m \le \mu$, $m \le \nu$ and

$$
m(\Omega) = 1 - \mathrm{TV}(\mu, \nu),
$$

namely $m = \mu|_s + \nu|_{s^c}$ for a Hahn set $s$. This is the overlap $\mu \wedge \nu$, whose
density with respect to $\mu + \nu$ is the minimum of the two densities, so
$\int \min(p, q) = 1 - \mathrm{TV}(\mu, \nu)$.

## Informally uses

- [Total variation is attained at a Hahn set](total-variation-dist-eq-of-is-hahn-decom.md):
  computes the mass of $m$.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), proof of Theorem 31.1 (the identity `∫ min(p₀, p₁) = 1 - TV`).
