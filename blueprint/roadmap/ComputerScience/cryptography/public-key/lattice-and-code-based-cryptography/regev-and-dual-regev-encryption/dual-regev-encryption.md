# Dual-Regev public-key encryption

Let $q = 2^w$ and $n, m \ge 1$. In the *dual-Regev* scheme, key generation draws a uniform $A \in \mathbb{Z}_q^{m \times n}$ and a short secret $e \in \{0,1\}^m$, and publishes $(A, u)$ with syndrome $u^{\mathsf T} = e^{\mathsf T} A$; the secret key is $e$. To encrypt a bit $\mu$, draw a uniform $s \in \mathbb{Z}_q^n$ and small integer errors $x \in \mathbb{Z}^m$, $x_0 \in \mathbb{Z}$, and output

$$
(b, c_0) = \bigl(A s + x,\; \langle u, s \rangle + x_0 + \mu\, 2^{w-1}\bigr).
$$

Decryption rounds $c_0 - \langle e, b \rangle$ to the nearest multiple of $2^{w-1}$. The public key is a preimage-sampleable function: $e \mapsto e^{\mathsf T} A$ with trapdoor-based Gaussian preimage sampling gives the GPV identity-based and signature schemes.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Half-modulus encoding of a bit tolerates errors below $q/4$](../lattice-trapdoors/half-modulus-bit-decoding.md)

## Sources

- Craig Gentry, Chris Peikert and Vinod Vaikuntanathan, "Trapdoors for Hard Lattices and New Cryptographic Constructions", Proceedings of the 40th Annual ACM Symposium on Theory of Computing, 2008.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
