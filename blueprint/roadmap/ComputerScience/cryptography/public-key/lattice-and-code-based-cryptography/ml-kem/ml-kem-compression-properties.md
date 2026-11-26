# Rounding properties of ML-KEM compression

Let $q > 0$ and $d \ge 1$. (i) If $2^d < q$ then $\mathrm{Compress}_d(\mathrm{Decompress}_d(y)) = y$ for every $y \in \mathbb{Z}_{2^d}$. (ii) For every $x \in \mathbb{Z}_q$, the centered representative of $\mathrm{Decompress}_d(\mathrm{Compress}_d(x)) - x$ has absolute value at most $\lceil q / 2^{d+1} \rfloor$. (iii) If $4B + 2 < q$ and $w \in \mathbb{Z}_q$ has centered absolute value at most $B$, then $\mathrm{Compress}_1(\mathrm{Decompress}_1(\mu) + w) = \mu$ for both bits $\mu$.

## Proof sketch

All three are statements about nearest-integer rounding of the rationals $2^d x/q$ and $q y/2^d$: rounding twice moves a point by at most half a step at each scale, and the step $q/2^d > 1$ in (i) ensures the round trip is exact.

## Depends on

- [Coefficient compression in ML-KEM](ml-kem-compression.md)

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
