# MakeHint and UseHint

For $z, r \in \mathbb{Z}_q$, the hint bit is $h = \mathrm{MakeHint}(z, r) = [\mathrm{HighBits}(r) \ne \mathrm{HighBits}(r + z)]$, and $\mathrm{UseHint}(h, r)$ returns $\mathrm{HighBits}(r)$ if $h = 0$ and otherwise moves it by one bucket, to $r_1 \pm 1 \bmod m$ according to the sign of $\mathrm{LowBits}(r)$, with $m = (q-1)/(2\gamma_2)$. Then: (i) if $\|z\|_\infty \le \gamma_2$, $\mathrm{UseHint}(\mathrm{MakeHint}(z, r), r) = \mathrm{HighBits}(r + z)$; (ii) for every hint bit $h$, the centered residual $r - 2\gamma_2\,\mathrm{UseHint}(h, r)$ has absolute value at most $2\gamma_2 + 1$; (iii) for fixed $r$, $\mathrm{UseHint}(\cdot, r)$ is injective, and a set hint never returns the unadjusted high bits.

## Proof sketch

Since adding $z$ with $|z| \le \gamma_2$ to $r$ moves its high part by at most one bucket, in the direction given by the sign of the low part, the hint records exactly whether that move occurs.

## Depends on

- [Power2Round, Decompose, HighBits and LowBits](ml-dsa-decompositions.md)

## Proof depends on

- [Reconstruction and uniqueness of the ML-DSA decompositions](ml-dsa-decomposition-properties.md)

## Sources

- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
