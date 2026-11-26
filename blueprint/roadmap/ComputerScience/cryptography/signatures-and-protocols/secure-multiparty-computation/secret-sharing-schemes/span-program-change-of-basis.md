# Change of basis preserves monotone span programs

Let $\{M_P\}$ be a monotone span program with matrices of width $d$ over a finite field, and let $R \in \mathbb{F}^{d \times d}$ be invertible with top row $e_1$. Then the program $\{M_P R\}$ is equivalent to $\{M_P\}$: for every secret, the two linear secret-sharing schemes with uniform randomness give the same distribution of shares.

## Proof sketch

$M_P R (z, \rho)^{\mathsf T} = M_P (z, \rho')^{\mathsf T}$ with $(z, \rho') = R(z, \rho)$; since the first row of $R$ is $e_1$, the first coordinate stays $z$, and $\rho \mapsto \rho'$ is an affine bijection preserving the uniform law.

## Depends on

- [Monotone span programs and linear secret sharing](monotone-span-programs.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
