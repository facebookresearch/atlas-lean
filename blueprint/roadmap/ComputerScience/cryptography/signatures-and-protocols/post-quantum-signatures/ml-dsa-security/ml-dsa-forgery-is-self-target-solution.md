# A verifying ML-DSA forgery is a SelfTargetMSIS solution

Let $(\mathbf{z}, c)$ verify for message $\mu$ under the full public key $(\mathbf{A}, \mathbf{t})$ with a fixed hash. Then $(-\mathrm{LowBits}(\mathbf{A}\mathbf{z} - c\mathbf{t}), \mathbf{z}, c)$ is a short vector $\mathbf{y}$ with $\|\mathbf{y}\|_\infty \le \max(\gamma_1 - \beta, \gamma_2 + 1, 1)$ solving SelfTargetMSIS for the matrix $[\,I_k \mid \mathbf{A} \mid -\mathbf{t}\,]$: the hash of $\mu$ and of $[\,I \mid \mathbf{A} \mid -\mathbf{t}\,]\mathbf{y}$, rounded by HighBits, equals $c$. For compressed verification with public key $\mathbf{t}_1$, where $\mathbf{t} = 2^d\mathbf{t}_1 + \mathbf{t}_0$ and $c$ has $\tau$ nonzero coefficients, each $\pm 1$, and with hints, the forgery yields a SelfTargetMSIS solution $\mathbf{y}$ for the same matrix $[\,I_k \mid \mathbf{A} \mid -\mathbf{t}\,]$ in which the low part is corrected by the hint residual and the rounding error $c\,\mathbf{t}_0$: with $\mathbf{w}'_1$ the hinted high part and $\mathbf{u} = \mathbf{A}\mathbf{z} - 2^d c\,\mathbf{t}_1 - 2\gamma_2\mathbf{w}'_1$, the vector $\mathbf{y} = (c\,\mathbf{t}_0 - \mathbf{u}, \mathbf{z}, c)$ maps that matrix to $2\gamma_2\mathbf{w}'_1$, with $\|\mathbf{y}\|_\infty \le \max(\gamma_1 - \beta, 2\gamma_2 + 1 + 2^{d-1}\tau)$.

## Proof sketch

Write $\mathbf{A}\mathbf{z} - c\mathbf{t} = \mathrm{HighBits}\cdot 2\gamma_2 + \mathrm{LowBits}$; adding the negated low part to the product gives a multiple of $2\gamma_2$ whose bucket is what the verifier hashes. In the compressed case, the hint residual has norm at most $2\gamma_2 + 1$ and $\|c\,\mathbf{t}_0\|_\infty \le 2^{d-1}\tau$.

## Depends on

- [The ML-DSA signature scheme](../ml-dsa-signatures/ml-dsa-scheme.md)
- [The SelfTargetMSIS problem](../../../hash-functions/lattice-based-hashing/self-target-module-sis.md)

## Proof depends on

- [Reconstruction and uniqueness of the ML-DSA decompositions](../ml-dsa-signatures/ml-dsa-decomposition-properties.md)
- [MakeHint and UseHint](../ml-dsa-signatures/ml-dsa-hints.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
