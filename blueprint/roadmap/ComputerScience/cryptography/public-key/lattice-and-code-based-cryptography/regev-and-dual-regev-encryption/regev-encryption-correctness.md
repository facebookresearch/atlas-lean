# Correctness of Regev bit encryption

Let $q = 2^w$. In Regev's scheme the public key is $A = [\,B t + e \mid B\,] \in \mathbb{Z}_q^{m \times (n+1)}$ with $B$ uniform, secret $t \in \mathbb{Z}_q^n$ and integer errors $e$, and a bit $\mu$ is encrypted with uniform coins $x \in \{0,1\}^m$ as $c = x^{\mathsf T} A + (\mu\, 2^{w-1}, 0, \dots, 0)$. Decryption rounds $\langle c, (1, -t) \rangle$, which equals $\mu\, 2^{w-1} + \langle x, e \rangle \bmod q$. If every error satisfies $|e_i| \le \beta$ and $4 m \beta < q$, every ciphertext decrypts correctly with probability $1$; in particular, with errors from a centered binomial distribution of parameter $\eta$, decryption never fails when $4 m \eta < q$.

## Proof sketch

The residual identity follows from $A (1, -t)^{\mathsf T} = e$. The selected noise $\langle x, e\rangle$ is a subset sum of errors, hence of absolute value at most $m\beta$, and half-modulus decoding tolerates errors below $q/4$.

## Depends on

- [Regev's public-key encryption from learning with errors](../../hardness-assumptions/regev-s-public-key-encryption-from-learning.md)

## Proof depends on

- [Half-modulus encoding of a bit tolerates errors below $q/4$](../lattice-trapdoors/half-modulus-bit-decoding.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM, 2009.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
