# Transport of module presentations through selected colimits

Let `(D₁,K₁,S₁)` and `(D₂,K₂,S₂)` be ringed sites with rings/modules in universe `u`, and
additive sheafification with the locally-bijective comparison on both sites. Let `P` present a
module sheaf `M`, with generator set `I_G`, relation set `I_R`, and relation map `r :
free(I_R) → free(I_G)` equal to the relation-generating map followed by `kernel.ι
P.generators.π`. For an additive functor `F`, assume preservation of `Discrete I_G`- and
`Discrete I_R`-colimits and of `parallelPair r 0`, and give `η : unit S₂ ≅ F(unit S₁)`. Then
`P.mapOfPreserves F η hF` is a presentation of `F(M)` with the transported generator and
relation families.
