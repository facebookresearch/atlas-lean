# Correct decryption of GSW ciphertexts with small noise

If a GSW ciphertext encrypts $\mu$ with error $\varepsilon$ satisfying $4\|\varepsilon\|_\infty < q$, decryption returns $\mu$: the selected row, recomposed and paired with the unexpanded secret $s$, equals $\mu\, 2^{w-1} + \varepsilon_j \bmod q$, and rounding it modulo $q$ to the nearer of $0$ and $2^{w-1}$ (the top bit of the value plus $2^{w-2}$) recovers $\mu$. At width $w = 1$ decryption reads the single bit of the phase.

## Proof sketch

Row $j$ of $C G^{\mathsf T} s$ corresponding to the most significant gadget entry of the first coordinate is $2^{w-1}\mu + \varepsilon_j$; apply half-modulus decoding.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)

## Proof depends on

- [Half-modulus encoding of a bit tolerates errors below $q/4$](../../lattice-and-code-based-cryptography/lattice-trapdoors/half-modulus-bit-decoding.md)
- [Noise growth of GSW encryption and NAND](gsw-noise-growth.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
