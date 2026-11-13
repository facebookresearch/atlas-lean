# The hypotheses a genome-wide BH/BY pipeline needs

**The hypotheses a genome-wide BH/BY pipeline needs** from `m` per-variant p-values `p` with
(unknown) true-null set `H0`, in dependence regime `r`. They are assumptions for the pipeline,
not proved here: `null_valid` is supplied per variant (for the allelic test by
`isValidPValue_allelicPValue`, only under its stated null); `dependence` must be justified
separately for the variants at hand.
