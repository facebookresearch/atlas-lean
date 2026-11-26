# Appending a collision-resistant hash of keys and messages makes aggregate signatures binding

Let an aggregate signature scheme combine signatures under key vector $\vec{pk}$ on message vector $\vec m$ into one aggregate. Appending $H_d(\vec{pk}, \vec m)$ for a collision-resistant keyed hash $H$ (with the hash key as a system parameter), and checking it during verification, yields a scheme in which no efficient adversary produces one aggregate that verifies under two different (key vector, message vector) pairs, while preserving unforgeability.

## Proof sketch

An aggregate valid for two distinct pairs carries one appended digest equal to the hash of both, which is a collision.

## Depends on

- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)
- [Collision resistance and target collision resistance](../../../hash-functions/collision-resistance-and-target-collision-resistance.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
