# Stateless tree signatures from an indexed scheme and a PRF

Let $S$ be a secure indexed signature scheme of capacity $q \ge 2$ and $F$ a PRF. The *stateless tree signature* scheme fixes a $q$-ary tree of depth $\ell$ whose nodes carry key pairs of $S$ generated from PRF outputs on the node names; to sign $m$ it chooses a leaf (pseudo)randomly, signs $m$ with the leaf's key, and certifies the path to the root by signing each child's public key under its parent at the child's index. If $q^{\ell}$ is super-polynomial, the scheme is EUF-CMA secure.

## Proof sketch

Replace the PRF-derived coins by truly random coins and then by lazily generated keys (PRF security). A forgery either reuses every certified public key on its path, giving a forgery against the leaf's indexed scheme, or contains a first uncertified key, giving a forgery against its parent; the reduction plants its challenge key at a random node among the polynomially many generated ones. Leaf collisions occur with probability at most $Q^2/q^\ell$.

## Depends on

- [Indexed signature scheme](indexed-signature-scheme.md)
- [Asymptotic PRF security relative to a class of distinguishers](../../../symmetric-key/pseudorandom-functions/prfsecure.md)
- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)

## Proof depends on

- [Counters and doubling for indexed signature schemes](indexed-signature-counter-and-doubling.md)
- [Merkle signing](../../merkle-signature-scheme/sign.md)

## Sources

- O. Goldreich, "Two Remarks Concerning the Goldwasser-Micali-Rivest Signature Scheme", Advances in Cryptology (CRYPTO 1986), LNCS 263, 1987.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
