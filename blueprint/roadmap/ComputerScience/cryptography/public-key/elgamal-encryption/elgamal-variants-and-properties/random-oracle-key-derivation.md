# Key derivation in the random oracle model from unpredictable secrets

Let secrets $s$ be drawn from a source with side information $z$ such that every efficient adversary, given $z$, guesses $s$ with negligible probability (computational unpredictability). If $H$ is a random oracle, then $(z, H(s))$ is computationally indistinguishable from $(z, U_\ell)$ by every efficient oracle distinguisher; a distinguisher making $Q$ oracle queries yields a guesser, which simulates the oracle lazily and outputs a uniformly chosen query, with advantage at least $1/Q$ of the distinguisher's.

## Proof sketch

Real and ideal experiments are identical until the distinguisher queries the oracle at $s$; the guessing adversary outputs a random query from its lazily simulated table, which hits $s$ with probability at least $\Pr[\text{bad}]/Q$.

## Depends on

- [Secure key derivation function for a group](secure-key-derivation-function.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and P. Rogaway, "Random Oracles are Practical: A Paradigm for Designing Efficient Protocols", Proceedings of the 1st ACM Conference on Computer and Communications Security (CCS), 1993.
