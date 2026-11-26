# Lazy and eager sampling of a random oracle are equivalent

Let $F$ be a random function from a finite set $X$ to a finite set $Y$. Running an oracle algorithm against $F$ sampled *eagerly* (the whole table drawn uniformly before the execution) and against $F$ sampled *lazily* (each new point answered by a fresh uniform value and cached, repeated points answered from the cache) gives identical output distributions. The same holds for several independent oracles, for oracles whose tables are re-indexed by a bijection of their domains, and for games in which some table entries are later replaced by an independent table read only at points the adversary cannot query.

## Proof sketch

Induct on the execution: at each query the lazily sampled answer at a new point is uniform and independent of everything seen so far, exactly as the corresponding unread entry of an eagerly sampled table.

## Depends on

- [The random oracle model](../random-oracle-constructions/the-random-oracle-model.md)
- [Adaptive oracle algorithms](../../security-games/oracle-algorithms/oracle-comp.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
