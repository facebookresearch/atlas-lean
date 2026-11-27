# Correctness of dual-Regev encryption

In dual-Regev encryption, for every key $(A, u = A^{\mathsf T} e)$ and every ciphertext the decryption residual is

$$
c_0 - \langle e, b \rangle \equiv \mu\, 2^{w-1} + x_0 - \langle e, x \rangle \pmod q .
$$

If $\|e\|_\infty \le \beta$ and all error coordinates satisfy $|x_i|, |x_0| \le \eta$, the noise has absolute value at most $m \beta \eta + \eta$, so decryption is always correct when $4(m\beta\eta + \eta) < q$; for binary secrets this is $4(m\eta + \eta) < q$.

## Proof sketch

Substitute $b = As + x$ and $\langle u, s\rangle = \langle e, As\rangle$; the terms in $s$ cancel. Bound the noise by the triangle inequality and apply half-modulus decoding.

## Depends on

- [Dual-Regev public-key encryption](dual-regev-encryption.md)

## Proof depends on

- [Half-modulus encoding of a bit tolerates errors below $q/4$](../lattice-trapdoors/half-modulus-bit-decoding.md)

## Sources

- Craig Gentry, Chris Peikert and Vinod Vaikuntanathan, "Trapdoors for Hard Lattices and New Cryptographic Constructions", Proceedings of the 40th Annual ACM Symposium on Theory of Computing, 2008.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
