# Normalized old-allele Green weight equals the frequency

For real numbers `0 < ε < x < 1 - ε`, the
[neutral Green's function](../sojourn-times-of-the-wright-fisher-diffusion/neutral-green.md) `G`
satisfies `G(1 - ε, x) / (G(ε, x) + G(1 - ε, x)) = x`; here `G(ε, x) = 2ε / x` and
`G(1 - ε, x) = 2ε / (1 - x)`. In Patterson's Corollary 1 (after Kimura and Ohta), `G(ε, x)` stands
for an allele that is new and `G(1 - ε, x)` for one that is old, and the normalized weight `x` is
the posterior probability that an allele at frequency `x` is old; the identity holds for every such
`ε`, not only in the limit.

## Sources

- N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*, Genetics 169
  (2005), 1093–1104.
- M. Kimura and T. Ohta, *The age of a neutral mutant persisting in a finite population*, Genetics
  75 (1973), 199–212.
