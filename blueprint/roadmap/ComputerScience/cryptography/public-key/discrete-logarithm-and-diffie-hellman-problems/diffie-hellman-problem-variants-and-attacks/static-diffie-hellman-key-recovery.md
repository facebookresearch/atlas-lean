# Static Diffie–Hellman oracles leak the key in groups with smooth subgroups

Suppose a party with fixed secret $\alpha$ answers *static Diffie–Hellman* queries $h \mapsto h^{\alpha}$ on arbitrary elements $h$ of a larger group (for example, a decryption oracle that does not check subgroup membership). If the ambient group has a subgroup of small prime order $\ell$, querying an element of order $\ell$ reveals $\alpha \bmod \ell$ by exhaustive search; combining such residues over several small primes by the Chinese remainder theorem recovers $\alpha$ when the product of these primes exceeds the order of $g$. Hence decryption and key-agreement implementations must validate that received elements lie in the prime-order subgroup.

## Proof sketch

For $h$ of order $\ell$, $h^\alpha = h^{\alpha \bmod \ell}$ and the $\ell$ candidates can be tested in $O(\ell)$ group operations; this is the Pohlig–Hellman decomposition applied to the oracle's answers.

## Depends on

- [Cyclic and prime-order group families](cyclic-group-families.md)
- [Correctness of Diffie–Hellman key agreement](../../diffie-hellman-key-exchange/dh-agree.md)

## Proof depends on

- [Pohlig–Hellman reduction to prime-order subgroups](../generic-group-algorithms-and-bounds/pohlig-hellman-reduction.md)

## Sources

- C. H. Lim and P. J. Lee, "A Key Recovery Attack on Discrete Log-based Schemes Using a Prime Order Subgroup", Advances in Cryptology – CRYPTO '97, LNCS 1294, Springer, 1997, pp. 249–263.
