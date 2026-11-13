# Lineages after the first coalescence events of a ranked history

The lineages after the first `t` coalescence events of the ranked history `h` (of `m`
lineages), starting from the lineages `bs`, each given as the set of sampled genes it is
ancestral to. Events follow the encoding of `RankedHistory`: the pair `{a, b}` with `a < b`
merges into position `a`, and position `b` is removed (`mergeBlocks`). With the singletons as
starting lineages this is `blocksAfter` (`mergeAlong_singletons`).
