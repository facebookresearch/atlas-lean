# Diffie–Hellman key exchange is key-guessing secure iff CDH holds

For a prime-order group family, Diffie–Hellman key exchange (Alice sends $g^x$, Bob sends $g^y$, both output $g^{xy}$, with exponents drawn within statistical distance $2^{-n}$ of uniform) is key-guessing secure against eavesdroppers if and only if CDH holds. The key-guessing and CDH advantages differ by at most $2 \cdot 2^{-n}$.

## Proof sketch

The transcript is exactly a CDH instance (up to the sampling distance) and the key is its solution, so each adversary is the other.

## Depends on

- [Key-guessing security of anonymous key exchange](key-guessing-security-of-key-exchange.md)
- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)
- [Correctness of Diffie–Hellman key agreement](../dh-agree.md)

## Proof depends on

- [Sampling residues by reducing uniform bit strings](../../../security-games/probabilistic-oracle-programs/sampling-residues-from-fair-bits.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- W. Diffie and M. E. Hellman, "New Directions in Cryptography", IEEE Transactions on Information Theory 22(6), 1976.
