# Unclonable encryption from BB84 states via monogamy

The scheme that encrypts $m\in\{0,1\}^{\ell}$ with key $\theta\in\{0,1\}^{n}$ as $|x\rangle_\theta$ for a fresh uniform $x\in\{0,1\}^{n}$ together with the classical value $m\oplus H(x)$ (with $H$ a random oracle, or $m\oplus x$ with $\ell=n$ for the one-time version) is unclonable in the search sense: two non-communicating parties holding a split ciphertext, both given the key, recover $m$ simultaneously with probability at most $0.854^{n}$ (information-theoretic, one-time-pad version) or negligible in the random oracle model.

## Proof sketch

Both parties recovering $m$ in the one-time-pad version means both recovering $x$ given $\theta$, which is the BB84 monogamy game. In the random oracle model, recovering $m$ requires querying $H$ at $x$; by an extraction argument (measuring a random query), both parties producing $x$ again reduces to the monogamy game.

## Depends on

- [Unclonable encryption](unclonable-encryption.md)
- [The quantum random oracle model](../security-games/quantum-random-oracle-techniques/quantum-random-oracle-model.md)

## Proof depends on

- [Monogamy-of-entanglement game for BB84 states](monogamy-bb84.md)
- [One-way to hiding lemma for reprogramming quantum random oracles](../security-games/quantum-random-oracle-techniques/one-way-to-hiding.md)

## Sources

- Anne Broadbent, Sébastien Lord, "Uncloneable Quantum Encryption via Oracles", TQC (2020).
