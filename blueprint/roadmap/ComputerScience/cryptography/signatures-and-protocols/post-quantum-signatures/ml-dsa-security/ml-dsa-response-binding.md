# Distinct responses to the same ML-DSA challenge give a Module-SIS solution

If two distinct responses $\mathbf{z} \ne \mathbf{z}'$ (with hints $\mathbf{h}, \mathbf{h}'$) verify for the same challenge $c$ and recover the same commitment $\mathbf{w}_1$, then subtracting the two verification relations cancels the public-key term and yields a nonzero short vector in the kernel of $[\,I_k \mid \mathbf{A}\,]$ (a Module-SIS solution in Hermite normal form) with coefficient bound $2(\gamma_1 - \beta)$ on the $\mathbf{z}$ part and $4\gamma_2 + 2$ on the low part. Consequently strong unforgeability adds, to the key-only bound, at most the Module-SIS advantage of an explicit reduction for this same-challenge, same-commitment case.

## Proof sketch

Both $\mathbf{A}\mathbf{z} - c\mathbf{t}$ and $\mathbf{A}\mathbf{z}' - c\mathbf{t}$ are within the hint residual of $2\gamma_2 \mathbf{w}_1$, so $\mathbf{A}(\mathbf{z} - \mathbf{z}')$ is short; the pair (negated difference of the residuals, $\mathbf{z} - \mathbf{z}'$) is the kernel vector.

## Depends on

- [The ML-DSA signature scheme](../ml-dsa-signatures/ml-dsa-scheme.md)
- [Module-SIS and Ring-SIS](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/module-sis.md)

## Proof depends on

- [MakeHint and UseHint](../ml-dsa-signatures/ml-dsa-hints.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
