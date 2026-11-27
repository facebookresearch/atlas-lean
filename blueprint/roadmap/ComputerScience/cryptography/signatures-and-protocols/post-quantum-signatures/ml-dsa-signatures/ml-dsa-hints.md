# MakeHint and UseHint

For $z, r \in \mathbb{Z}_q$, with $m = (q-1)/(2\gamma_2) \ge 2$ (that is, $q > 4\gamma_2$), the hint bit is $h = \mathrm{MakeHint}(z, r) = [\mathrm{HighBits}(r) \ne \mathrm{HighBits}(r + z)]$, and $\mathrm{UseHint}(h, r)$ returns $r_1 = \mathrm{HighBits}(r)$ if $h = 0$; if $h = 1$ it returns $(r_1 + 1) \bmod m$ when $\mathrm{LowBits}(r) > 0$ and $(r_1 - 1) \bmod m$ when $\mathrm{LowBits}(r) \le 0$, with residues taken in $[0, m)$. Then: (i) if $\|z\|_\infty \le \gamma_2$, $\mathrm{UseHint}(\mathrm{MakeHint}(z, r), r) = \mathrm{HighBits}(r + z)$; (ii) for every hint bit $h$, the centered residual $r - 2\gamma_2\,\mathrm{UseHint}(h, r)$ has absolute value at most $2\gamma_2 + 1$; (iii) for fixed $r$, $\mathrm{UseHint}(\cdot, r)$ is injective, and a set hint never returns the unadjusted high bits.

## Proof sketch

Since adding $z$ with $|z| \le \gamma_2$ to $r$ moves its high part by at most one bucket, upward only if the low part is positive and downward only if it is not, the hint records exactly whether that move occurs; since $m \ge 2$, the moved bucket differs from the original one.

## Depends on

- [Power2Round, Decompose, HighBits and LowBits](ml-dsa-decompositions.md)

## Proof depends on

- [Reconstruction and uniqueness of the ML-DSA decompositions](ml-dsa-decomposition-properties.md)

## Sources

- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
