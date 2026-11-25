# In the admixture model individual frequencies are ancestral mixtures

Let `θ = (Q, F)` be
[parameters of the admixture model](../admixture-model-and-the-frappe-em-algorithm/params.md) with a
finite set `K` of ancestral populations (`Q i k > 0`, `∑ k, Q i k = 1` for every `i`, and
`0 < F k j < 1`). In the [admixture-model frequency family](ancestry-freq.md), the frequency of
individual `i` at SNP `j` is `∑ k, Q i k * F k j`, the mixture with proportions `Q i` of the
frequencies of the ancestral populations: the individual has no private drift.
