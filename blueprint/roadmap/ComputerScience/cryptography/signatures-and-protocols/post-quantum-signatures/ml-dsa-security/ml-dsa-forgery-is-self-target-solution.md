# A verifying ML-DSA forgery is a SelfTargetMSIS solution

Let $(\mathbf{z}, c)$ verify for message $\mu$ under the full public key $(\mathbf{A}, \mathbf{t})$ with a fixed hash. Then $(-\mathrm{LowBits}(\mathbf{A}\mathbf{z} - c\mathbf{t}), \mathbf{z}, c)$ is a short vector $\mathbf{y}$ with $\|\mathbf{y}\|_\infty \le \max(\gamma_1 - \beta, \gamma_2 + 1, 1)$ solving SelfTargetMSIS for the matrix $[\,I_k \mid \mathbf{A} \mid -\mathbf{t}\,]$: the hash of $\mu$ and of $[\,I \mid \mathbf{A} \mid -\mathbf{t}\,]\mathbf{y}$, rounded by HighBits, equals $c$. For compressed verification with public key $\mathbf{t}_1$ and hints, the forgery likewise yields a SelfTargetMSIS solution in which the low part is corrected by the hint residual and the rounding error $c\,\mathbf{t}_0$, with bound $2\gamma_2 + 1 + \beta$-type terms in place of $\gamma_2$.

## Proof sketch

Write $\mathbf{A}\mathbf{z} - c\mathbf{t} = \mathrm{HighBits}\cdot 2\gamma_2 + \mathrm{LowBits}$; adding the negated low part to the product gives a multiple of $2\gamma_2$ whose bucket is what the verifier hashes. In the compressed case, use the hint residual bound.

## Depends on

- [The ML-DSA signature scheme](../ml-dsa-signatures/ml-dsa-scheme.md)
- [The SelfTargetMSIS problem](../../../hash-functions/lattice-based-hashing/self-target-module-sis.md)

## Proof depends on

- [Reconstruction and uniqueness of the ML-DSA decompositions](../ml-dsa-signatures/ml-dsa-decomposition-properties.md)
- [MakeHint and UseHint](../ml-dsa-signatures/ml-dsa-hints.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
