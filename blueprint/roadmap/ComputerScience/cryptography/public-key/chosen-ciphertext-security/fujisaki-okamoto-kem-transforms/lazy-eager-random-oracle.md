# Lazy and eager sampling of a random oracle are equivalent

The equivalence of a lazily sampled random function (each new point answered by a fresh uniform value and cached) with an eagerly sampled one (the whole table drawn uniformly in advance) extends in three ways used by the Fujisaki–Okamoto proofs: to an oracle algorithm querying several independent random functions on finite sets, all sampled lazily versus all sampled eagerly; to random functions whose tables are re-indexed by a bijection of their domains; and to games in which some table entries are later replaced by an independent uniform table that is read only at points the adversary cannot query. In each case an oracle algorithm has identical output distributions in the two games.

## Proof sketch

For several oracles, apply the single-oracle equivalence to their product, a random function on the disjoint union of the domains. A bijective re-indexing of a uniform table is again uniform. Entries that the adversary cannot query are independent of its view, so replacing them by an independent uniform table leaves the joint distribution of the view unchanged.

## Depends on

- [Lazy random functions are random functions](../../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rf-map-fst.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)
- [Adaptive oracle algorithms](../../../security-games/oracle-algorithms/oracle-comp.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
