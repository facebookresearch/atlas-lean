# Multilinear polynomial commitments from constrained Reed–Solomon proximity

A Merkle commitment to the Reed–Solomon encoding $f=\hat{f}|_L$ of a polynomial of degree $< 2^{m}$ is a binding commitment to the multilinear polynomial $\bar{f}$ whenever $f$ is proved close to the code. An evaluation claim $\bar{f}(z)=y$ for $z\in\mathbb{F}^{m}$ is exactly membership of $f$ in $\mathrm{CRS}[\mathbb{F},L,m,\hat{w}_z,y]$ with $\hat{w}_z(Z,X)=Z\cdot\widetilde{\mathrm{eq}}(z,X)$, so any IOPP for constrained Reed–Solomon codes with knowledge soundness, compiled with the BCS transform, yields a multilinear polynomial commitment scheme in the random oracle model; several evaluation claims are batched by taking a random linear combination of their weight polynomials.

## Proof sketch

The sum $\sum_b\bar{f}(b)\widetilde{\mathrm{eq}}(z,b)$ equals $\bar{f}(z)$ by the equality-polynomial identity. Batching: a random combination of constraints with distinct targets fails to detect a false claim with probability at most the number of claims over $|\mathbb{F}|$. Knowledge soundness of the IOPP plus Merkle extraction in the random oracle model yield extractability.

## Depends on

- [Constrained Reed–Solomon codes with sum-check constraints](constrained-rs-code.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Merkle root](../../hash-functions/merkle-trees/root.md)

## Proof depends on

- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)
- [Existential soundness of Merkle inclusion proofs](../../hash-functions/merkle-trees/verify-sound.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT (2025), IACR ePrint 2024/1586.
