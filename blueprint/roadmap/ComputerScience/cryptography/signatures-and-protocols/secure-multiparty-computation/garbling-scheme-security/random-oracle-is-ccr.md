# A random oracle is circular correlation robust

Let $H : L \times \mathcal{T} \to M$ be a random oracle and $\Delta$ uniform in a subset $D \subseteq L$ (for Free-XOR, labels with colour bit $1$). For every adversary making $q_O$ queries to the circular correlation oracle $(x, t, b) \mapsto H(x \oplus \Delta, t) \oplus b\Delta'$ without repeating a tweak with different inputs and without querying both $(x, t, 0)$ and $(x, t, 1)$, and $q_H$ direct queries to $H$, the advantage in distinguishing the oracle from a random function is at most

$$
\frac{q_O\, q_H}{|D|}.
$$

Hence garbling schemes proved secure under circular correlation robustness (Free-XOR and half gates) are secure in the random oracle model.

## Proof sketch

The two worlds agree unless some direct query hits a point $x \oplus \Delta$ already used by the correlation oracle; for each pair of queries this has probability at most $1/|D|$ over the hidden offset.

## Depends on

- [Circular correlation robust hash functions](circular-correlation-robustness.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [The difference lemma](../../../security-games/games-and-advantages/advantage-le-win-prob-of-eq-of-not-bad.md)

## Sources

- Seung Geol Choi, Jonathan Katz, Ranjit Kumaresan and Hong-Sheng Zhou, "On the Security of the ``Free-XOR'' Technique", Theory of Cryptography, 2012.
- Samee Zahur, Mike Rosulek and David Evans, "Two Halves Make a Whole: Reducing Data Transfer in Garbled Circuits Using Half Gates", Advances in Cryptology – EUROCRYPT 2015, 2015.
