# Generation sizes have the Galton–Watson law

Let `ξ` be an [offspring family](is-offspring-family.md) under `P` whose law `ν` is a probability
measure. Then for every `n` the [generation size](bp-size.md) `Z_n` of the branching process built
from `ξ` has law `𝓛_n`, the
[law of the `n`-th generation size](../../../Probability/branching-processes/galton-watson-process/law.md)
of the Galton–Watson process with offspring law `ν`: given `Z_n = z`, the next generation is the
total offspring of `z` fresh individuals, which is independent of `Z_n` and has law `ν^{∗z}`.
