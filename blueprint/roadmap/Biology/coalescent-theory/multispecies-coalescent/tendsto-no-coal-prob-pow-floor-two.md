# Wright–Fisher limit of the no-coalescence probability

The three-species probabilities come from the Wright–Fisher model: in a population of `M`
gene copies, the lineages of species `0` and `1` have distinct parents in each of the
`⌊t M⌋` generations of the internal branch (`t ≥ 0` coalescent units) with probability
`noCoalProb M 2 ^ ⌊t M⌋`, which tends to `tavareProb 2 2 t = e^{-t}`, the weight of the case
in which three lineages reach the root population.
