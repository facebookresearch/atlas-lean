# The Gentry–Sahai–Waters (GSW) encryption scheme

Let $q = 2^w$, $n, m \ge 1$, $N = (n + 1) w$, and let $G = I_{n+1} \otimes g^{\mathsf T}$ be the gadget matrix with bit decomposition $G^{-1}$. Key generation draws an LWE secret $t \in \mathbb{Z}_q^n$ and publishes the LWE matrix $A = [\,B t + e \mid B\,] \in \mathbb{Z}_q^{m \times (n+1)}$; the secret vector is $s = (1, -t)$, so $A s = e$. A bit $\mu$ is encrypted with a uniform binary matrix $R \in \{0,1\}^{N \times m}$ as

$$
C = G^{-1}\bigl(\mu\, G^{\mathsf T} + R A\bigr) \in \{0,1\}^{N \times N},
$$

the bit decomposition of $\mu G^{\mathsf T} + R A$. The defining *approximate eigenvector* relation is $C\, G^{\mathsf T} s = \mu\, G^{\mathsf T} s + R e$. Decryption selects the row of $C$ whose recomposition pairs with $s$ to $2^{w-1}\mu + \text{noise}$ and decodes it by half-modulus rounding to the nearer of $0$ and $2^{w-1}$. Homomorphic NAND of $C_1, C_2$ is $G^{-1}(G^{\mathsf T} - C_1 C_2 G^{\mathsf T})$, and the noiseless encryption of a constant $\mu$ is $G^{-1}(\mu\, G^{\mathsf T})$.

## Depends on

- [The binary gadget vector and gadget matrix](../../lattice-and-code-based-cryptography/lattice-trapdoors/gadget-matrix.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Homomorphic encryption: correctness and compactness](../homomorphic-encryption-correctness-and.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
