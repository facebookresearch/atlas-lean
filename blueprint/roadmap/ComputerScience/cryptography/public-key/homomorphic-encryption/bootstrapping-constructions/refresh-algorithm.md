# Gentry's refresh (recryption) algorithm

Let $\mathcal{E}$ be a homomorphic bit-encryption scheme with decryption circuit $D_\mathcal{E}$, which maps a secret key $sk$ and a ciphertext $c$ (as bit strings of fixed widths) to $\mathrm{Dec}(sk, c)$. Given an *encrypted secret key* $\overline{sk_1} = (\mathrm{Enc}(pk_2, sk_{1,i}))_i$ under a public key $pk_2$, the *refresh* of a ciphertext $c$ under $pk_1$ is

$$
\mathrm{Refresh}(pk_2, \overline{sk_1}, c) = \mathrm{Evaluate}\bigl(pk_2, D_\mathcal{E}, \overline{sk_1}, (\mathrm{Enc}(pk_2, c_j))_j\bigr),
$$

which homomorphically decrypts $c$ under the new key. The *NAND refresh* of $c, c'$ evaluates the *NAND-augmented decryption circuit* that runs two copies of $D_\mathcal{E}$ on disjoint input blocks and applies NAND to their outputs.

## Depends on

- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)
- [Homomorphic encryption: correctness and compactness](../homomorphic-encryption-correctness-and.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
- Craig Gentry, "A Fully Homomorphic Encryption Scheme", 2009.
