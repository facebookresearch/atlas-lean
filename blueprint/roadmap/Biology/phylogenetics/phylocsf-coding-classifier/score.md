# The PhyloCSF score

**The PhyloCSF score** (natural-log scale): the sum over the columns of the
log-likelihood ratio of the coding model `(tC, πC)` against the non-coding model
`(tN, πN)`. The published PhyloCSF score is reported in decibans; see `score_decibans`
for the conversion. Thresholds for this `score` are in natural-log units.
