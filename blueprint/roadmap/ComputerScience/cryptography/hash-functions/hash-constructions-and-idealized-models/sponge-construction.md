# Sponge construction

Let $f$ be a permutation of $\{0,1\}^b$ and $b = r + c$ (rate $r$, capacity $c$). The *sponge* on a padded message $P_1 \| \cdots \| P_\ell$ of $r$-bit blocks starts from $S = 0^b$, *absorbs* each block by $S \leftarrow f(S \oplus (P_i \| 0^c))$, and then *squeezes* output by repeatedly emitting the first $r$ bits of $S$ and applying $f$, until the requested output length is reached. SHA-3 and SHAKE are sponges over the Keccak-$p[1600, 24]$ permutation with domain-separating padding; an extendable-output function (XOF) allows arbitrary output length.

## Depends on

- [Merkle–Damgård hash with length strengthening](../merkle-damg-rd-construction/hash.md)

## Sources

- G. Bertoni, J. Daemen, M. Peeters and G. Van Assche, "On the Indifferentiability of the Sponge Construction", Advances in Cryptology (EUROCRYPT 2008), LNCS 4965, 2008.
- National Institute of Standards and Technology, "SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions", FIPS PUB 202, 2015.
