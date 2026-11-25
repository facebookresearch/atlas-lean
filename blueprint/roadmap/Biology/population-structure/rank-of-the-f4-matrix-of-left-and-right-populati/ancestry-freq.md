# Admixture-model frequencies of individuals and ancestral populations

Let `θ = (Q, F)` be
[parameters of the admixture model](../admixture-model-and-the-frappe-em-algorithm/params.md) with
individuals `I`, SNPs `J` and a finite set `K` of ancestral populations, so that `Q i k > 0`,
`∑ k, Q i k = 1` for every `i`, and `0 < F k j < 1`. The admixture-model frequency family is the
[global-ancestry family](ancestry-freq-of.md) of `Q` and `F`: individual `i` has frequency
`∑ k, Q i k * F k j` at SNP `j`, its
[reference-allele probability](../admixture-model-and-the-frappe-em-algorithm/qf.md), and ancestral
population `k` has frequency `F k j`.
