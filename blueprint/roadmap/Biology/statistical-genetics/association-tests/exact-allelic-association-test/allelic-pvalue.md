# Allelic PValue

The **one-sided exact allelic p-value** of a case–control variant: `X ω` copies of the tested
allele among `n₁` case alleles and `Y ω` among `n₂` control alleles. It is the upper Fisher exact
p-value of `X` given the margin `X + Y`. The margin is capped at `n₁ + n₂`, which changes nothing
under the null (where `X ≤ n₁` and `Y ≤ n₂` almost surely) and makes the definition total.
