# Simulation of ML-DSA signing attempts

In the ideal-mask model of ML-DSA (mask coefficients uniform in $(-\gamma_1, \gamma_1]$ and a fresh uniform challenge), for every fixed challenge $c$ and secret with $\|c\mathbf{s}_1\|_\infty \le \beta$, exactly $(2(\gamma_1 - \beta) - 1)^{\ell n}$ of the $(2\gamma_1)^{\ell n}$ masks yield an admissible response, and the accepted response $\mathbf{z}$ is uniform on the box $\|\mathbf{z}\|_\infty < \gamma_1 - \beta$, independent of the secret. A simulator that samples $c$ and $\mathbf{z}$ uniformly, recomputes the commitment $\mathbf{w}_1$ from $\mathbf{A}\mathbf{z} - c\mathbf{t}$ and applies the low-bits check publicly reproduces the accepted transcript; every accepted simulated attempt has the requested challenge, a short response, an encodable hint and the very commitment the verifier recovers. Moreover, by the min-entropy bound for signing commitments, the chance that a fresh commitment collides with an earlier oracle query is at most the number of earlier queries times the largest probability of a rounded commitment value.

## Proof sketch

The first part is the box-shift bijection of rejection sampling. The collision bound is a union bound over the earlier queries.

## Depends on

- [The ML-DSA signature scheme](ml-dsa-scheme.md)

## Proof depends on

- [Completeness, abort probability and zero knowledge of Lyubashevsky's protocol](../../sigma-protocols-and-fiat-shamir/fiat-shamir-with-aborts/lyubashevsky-identification-properties.md)
- [Reconstruction and uniqueness of the ML-DSA decompositions](ml-dsa-decomposition-properties.md)
- [Min-entropy of ML-DSA signing commitments](../ml-dsa-security/ml-dsa-commitment-entropy.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
- Pouria Fallahpour, Serge Fehr and Yu-Hsuan Huang, "Tighter Quantum Security for Fiat-Shamir-with-Aborts and Hash-and-Sign-with-Retry Signatures", Cryptology ePrint Archive, Paper 2025/985, 2025.
