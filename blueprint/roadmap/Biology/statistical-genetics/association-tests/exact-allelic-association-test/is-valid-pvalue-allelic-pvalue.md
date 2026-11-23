# Validity of the exact allelic test

Under the stated null (`X ~ Bin(n₁, f)` and
`Y ~ Bin(n₂, f)` independent, with common allele frequency `0 < f < 1`), the allelic p-value is
valid under `μ`: `μ {allelicPValue ≤ s} ≤ s` for `s ∈ [0, 1]`, whatever the value of `f`.

This holds only under that null. It is a per-variant statement; it says nothing about the joint
law of the p-values of different variants.

## Sources

- Lehmann–Romano (2005), §4.5 and Lemma 3.3.1.
