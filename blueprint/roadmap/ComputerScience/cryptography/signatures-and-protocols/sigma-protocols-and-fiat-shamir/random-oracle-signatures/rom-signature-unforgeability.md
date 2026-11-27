# Signature schemes and (strong) unforgeability in the random oracle model

A *signature scheme in the random oracle model* has key generation, signing and verification algorithms that may query a function $H : Q \to D$, which the security experiment draws uniformly at random (and answers lazily). In the *EUF-CMA experiment* the forger receives the public key and oracle access to $H$ and to a signing oracle; it wins if it outputs a pair $(m^*, \sigma^*)$ that verifies and $m^*$ was never submitted to the signing oracle. In the *strong* (SUF-CMA) experiment it suffices that the pair $(m^*, \sigma^*)$ differs from every pair returned by the signing oracle. A forger is $(q_S, q_H)$-bounded if it makes at most $q_S$ signing and $q_H$ hash queries. The scheme is (strongly) unforgeable if every probabilistic polynomial-time forger wins with negligible probability.

## Depends on

- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)
- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Mihir Bellare and Gregory Neven, "Multi-Signatures in the Plain Public-Key Model and a General Forking Lemma", Proceedings of the 13th ACM Conference on Computer and Communications Security, 2006.
