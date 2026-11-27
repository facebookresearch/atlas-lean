# Cramer–Shoup is CCA secure under DDH and collision resistance

Over a decodable prime-order group family, if DDH holds and $H'$ is collision resistant on the ciphertext-and-associated-data domain, then the Cramer–Shoup scheme is IND-CCA secure (with associated data), including against adversaries making interleaved, multiple challenge queries; the advantage is bounded by a DDH advantage, a collision-finding advantage, and $Q/q$ for $Q$ decryption queries.

## Proof sketch

Replace $w = u^\beta$ in the challenge by an independent element (DDH), so the challenge pair is off the Diffie–Hellman pairs. By universal$_2$ hashing, every decryption query with a non-DH pair and a tag different from the challenge tag is rejected except with probability $1/q$; equal tags with a different tuple give a hash collision. Then by universality the mask $v^\sigma w^\tau$ on the challenge is uniform and hides $m_b$.

## Depends on

- [Cramer–Shoup encryption scheme](cramer-shoup-scheme.md)
- [Public-key CCA experiment](../../../security-games/generic-security-games/pub-cca-game.md)
- [Advantage of a DDH distinguisher](../../elgamal-encryption/ddh-advantage.md)

## Proof depends on

- [Projective hash games against unbounded adaptive adversaries](projective-hash-security-games.md)
- [Fundamental lemma of game playing for stateful oracle handlers](../../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- R. Cramer and V. Shoup, "A Practical Public Key Cryptosystem Provably Secure against Adaptive Chosen Ciphertext Attack", Advances in Cryptology (CRYPTO 1998), LNCS 1462, 1998.
- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
