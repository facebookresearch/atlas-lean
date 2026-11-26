# Bootstrapping gives leveled fully homomorphic encryption

Let $\mathcal{E}$ be an IND-CPA secure bit-encryption scheme that is bootstrappable for the identity and NAND gates, whose decryption circuits are generated uniformly in polynomial time, and let $B(\lambda)$ be a polynomially bounded depth budget. The *leveled scheme* $\mathcal{E}^{(B)}$ generates $2B + 1$ base key pairs and the acyclic chain of links between them, encrypts under $pk_0$, evaluates any Boolean circuit of depth at most $B$ layer by layer (padding with identity refresh layers to exactly $2B$ transitions), and decrypts with the secret key at the end of the chain indicated by a one-bit tag. Then: (i) $\mathcal{E}^{(B)}$ correctly evaluates every circuit of depth at most $B$; (ii) it is compact: decryption, including tag selection, is computed by a polynomial-size circuit on ciphertexts whose width does not depend on $B$ or on the evaluated circuit; (iii) it is IND-CPA secure, with

$$
\mathrm{Adv}_{\mathcal{E}^{(B)}}(\mathcal{A}) \le c\,(2B + 1)(\ell_{sk} + 1)\cdot \mathrm{Adv}_{\mathcal{E}}(\mathcal{B})
$$

for an explicit strict polynomial-time reduction $\mathcal{B}$ and a small constant $c$. All schemes $\{\mathcal{E}^{(d)}\}_{d}$ run in one uniform polynomial time bound in $\lambda$ and $d$.

## Proof sketch

Correctness is the layered-evaluation lemma. Compactness holds because evaluated ciphertexts are base ciphertexts under the last key. Security: the challenge ciphertext is a base encryption under $pk_0$, which together with the zero chain is a base IND-CPA challenge, and the key-chain theorem replaces the real chain by the zero chain.

## Depends on

- [Gentry's bootstrapping theorem](../homomorphic-encryption/gentry-s-bootstrapping-theorem.md)
- [Homomorphic encryption: correctness and compactness](../homomorphic-encryption/homomorphic-encryption-correctness-and.md)
- [CPA security of public-key encryption families](../../security-games/asymptotic-security/pub-cpasecure.md)

## Proof depends on

- [Homomorphic evaluation of Boolean circuits layer by layer along a key chain](layered-circuit-evaluation.md)
- [Security of an acyclic encrypted-key chain](key-chain-security.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
- Craig Gentry, "A Fully Homomorphic Encryption Scheme", 2009.
