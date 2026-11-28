# Secure signatures imply one-way functions, and one-way functions give one-time signatures

(a) If a signature scheme is existentially unforgeable under a one-time (or many-time) chosen-message attack, then one-way functions exist: the map from key-generation coins to the public key is one-way. (b) Conversely, every one-way function on $n$-bit strings gives a one-time EUF-CMA secure signature scheme for $n$-bit messages (Lamport's scheme), so one-time signatures exist iff one-way functions exist.

## Proof sketch

(a) An inverter for coins-to-public-key yields coins consistent with the public key, from which the forger computes a secret key that signs a fresh message correctly with noticeable probability (by correctness on keys sampled from those coins). (b) Lamport's scheme reduces to inverting at a planted position.

## Depends on

- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)
- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)
- [One-way function families](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Security reduction for Lamport one-time signatures](../forge-game-le.md)

## Sources

- J. Rompel, "One-Way Functions are Necessary and Sufficient for Secure Signatures", Proceedings of the 22nd Annual ACM Symposium on Theory of Computing (STOC), 1990.
- O. Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
- L. Lamport, "Constructing Digital Signatures from a One-Way Function", Technical Report CSL-98, SRI International, 1979.
