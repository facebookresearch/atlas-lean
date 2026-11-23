# TDT with a random number of informative transmissions

Let `D ω` be the number of
informative transmissions (from heterozygous parents) and `B ω` the number that pass on the
allele of interest. If, given each value `D = d` of positive probability, `B ~ Bin(d, 1/2)` (the
null of no linkage, with the transmissions treated as independent fair coins given `d`), then
the TDT p-value evaluated at the observed total, `ω ↦ P(Bin(D ω, 1/2) ≥ B ω)`, is valid under
`μ`. This is the generic averaging lemma `isValidPValue_of_forall_cond_of_ne_zero` (over the
values of `D`) applied to the fixed-`d` guarantee `isValidPValue_tdtPValue`.
