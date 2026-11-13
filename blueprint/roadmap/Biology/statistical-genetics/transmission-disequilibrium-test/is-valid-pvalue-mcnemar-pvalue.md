# Validity of the one-sided McNemar test

Let the discordant counts `X` and `Y` be
independent Poisson counts with a common rate `a > 0`. Conditionally on `X + Y = N`, the McNemar
p-value is valid: `P(mcnemarPValue N X ≤ s | X + Y = N) ≤ s` for `s ∈ [0, 1]`. The bound holds
for every common rate `a`.

The same theorem is the conditional TDT when `X` and `Y` are the transmitted and untransmitted
counts, modeled as independent Poisson counts with equal rates under the null.

## Sources

- McNemar (1947); Lehmann–Romano (2005), §4.6 and Lemma 3.3.1.
