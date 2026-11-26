# Gathering an encoded query input in one round

At space exponent $\varepsilon=1$, every query with finite reports and decidable equality of output tuples can be computed in one round with zero failure probability in either raw-position input convention. One protocol family works for all positive worker counts, public shapes, schedules and valid payloads, under any fixed common seed law.

Use $C=1$ and choose worker 0 as the collector. In the distributed convention, all other workers send it their shards. It supplies its own shard locally and inverts the public slot-to-position bijection. In the input-server convention each relation server sends it the corresponding relation word. No worker receives more than the $M$ input bits. The collector reports the query answer and all other workers report the empty set.

## Sources

- Paul Beame, Paraschos Koutris and Dan Suciu, *Communication Steps for Parallel Query Processing*, PODS 2013, §2.1 (the $\varepsilon=1$ endpoint); §2.4 (input servers). [Authors' copy](https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf).
