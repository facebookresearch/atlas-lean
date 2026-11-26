# The number-theoretic transform of ML-DSA

Let $q = 8380417$ and $\zeta = 1753$. Then $\zeta$ has multiplicative order $512$ modulo $q$, so its odd powers $\zeta^{2\,\mathrm{brv}_8(i) + 1}$, $i < 256$ (with $\mathrm{brv}_8$ the bit reversal of $8$-bit indices), are the $256$ distinct roots of $X^{256} + 1$ in $\mathbb{Z}_q$, and $R_q = \mathbb{Z}_q[X]/(X^{256}+1) \cong \mathbb{Z}_q^{256}$ by evaluation at these roots. The FIPS 204 NTT computes this evaluation; twisting each coefficient by the corresponding power of $\zeta$ reduces it to an ordinary discrete Fourier transform at $\zeta^2$, and the inverse NTT applies the inverse DFT, the inverse twist and the factor $256^{-1}$. The two transforms are mutually inverse, and polynomial multiplication becomes pointwise multiplication of NTT vectors.

## Proof sketch

$\zeta^{256} = -1$ in $\mathbb{Z}_q$, so the odd powers are roots of $X^{256}+1$, and they are distinct because $\zeta$ has order $512$; the Chinese remainder theorem gives the isomorphism.

## Depends on

- [The ML-DSA signature scheme](ml-dsa-scheme.md)
- [The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/negacyclic-ring.md)

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
