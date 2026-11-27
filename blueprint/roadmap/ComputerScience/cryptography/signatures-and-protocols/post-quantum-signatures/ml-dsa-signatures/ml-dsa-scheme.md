# The ML-DSA signature scheme

ML-DSA (CRYSTALS-Dilithium) works over $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ with $q = 8380417$ and parameters $(k, \ell, \eta, \tau, \gamma_1, \gamma_2, \beta = \tau\eta, \omega, d)$. *Key generation* expands a uniform $\mathbf{A} \in R_q^{k \times \ell}$ from a seed $\rho$ (rejection sampling in the NTT domain), samples $\mathbf{s}_1 \in S_\eta^\ell$, $\mathbf{s}_2 \in S_\eta^k$ with coefficients uniform in $[-\eta, \eta]$, computes $\mathbf{t} = \mathbf{A}\mathbf{s}_1 + \mathbf{s}_2$ and publishes $(\rho, \mathbf{t}_1)$ where $(\mathbf{t}_1, \mathbf{t}_0) = \mathrm{Power2Round}(\mathbf{t})$. *Signing* $M$ repeats: sample a mask $\mathbf{y}$ with coefficients in $(-\gamma_1, \gamma_1]$ (expanded from a private seed), set $\mathbf{w}_1 = \mathrm{HighBits}(\mathbf{A}\mathbf{y})$, compute the challenge $c = \mathrm{SampleInBall}(H(\mu \Vert \mathbf{w}_1))$ (a polynomial with exactly $\tau$ coefficients $\pm 1$), and $\mathbf{z} = \mathbf{y} + c\mathbf{s}_1$; reject and retry unless $\|\mathbf{z}\|_\infty < \gamma_1 - \beta$, $\|\mathrm{LowBits}(\mathbf{A}\mathbf{y} - c\mathbf{s}_2)\|_\infty < \gamma_2 - \beta$, $\|c\mathbf{t}_0\|_\infty < \gamma_2$ and the hint $\mathbf{h}$ for recovering $\mathbf{w}_1$ from $\mathbf{A}\mathbf{z} - c\mathbf{t}_1 2^d$ has at most $\omega$ ones. The signature is $(\tilde c, \mathbf{z}, \mathbf{h})$. *Verification* checks $\|\mathbf{z}\|_\infty < \gamma_1 - \beta$, at most $\omega$ hints, and $\tilde c = H(\mu \Vert \mathrm{UseHint}(\mathbf{h}, \mathbf{A}\mathbf{z} - c\mathbf{t}_1 2^d))$. Here $\mu = H(H(pk) \Vert M')$ binds the public key, and FIPS 204 fixes the byte encodings, the context string, the hedged or deterministic signing randomness and caps on the number of attempts.

## Depends on

- [Fiat–Shamir with aborts signatures](../../sigma-protocols-and-fiat-shamir/fiat-shamir-with-aborts/fiat-shamir-with-aborts-signatures.md)
- [Power2Round, Decompose, HighBits and LowBits](ml-dsa-decompositions.md)
- [MakeHint and UseHint](ml-dsa-hints.md)
- [Decision Module-LWE](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/decision-module-lwe.md)
- [The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/negacyclic-ring.md)
- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)

## Sources

- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
