# Patterson's MRCA-age function M₂ for an old allele

For a real number `y`, let `M₂(y) = 1 - (1 - y) M₁(y) / y`, where [`M₁`](mean-mrca-new.md) is
Patterson's function for a new allele, with the convention `u / 0 = 0`; thus `M₂(0) = 1` and
`M₂(1) = 1`. The intended domain is `0 < y < 1`. There `M₂` is Patterson's Equation 17: in his
diffusion model, the expected age, in units of `2N` generations, of the most recent common ancestor
of two copies of an old (ancestral) allele now at frequency `y`.

## Sources

- N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*, Genetics 169
  (2005), 1093–1104.
