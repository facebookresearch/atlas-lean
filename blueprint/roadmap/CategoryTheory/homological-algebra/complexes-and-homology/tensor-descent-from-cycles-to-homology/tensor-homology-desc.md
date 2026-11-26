# Descent of a map on cycles to the tensor of homology

Let C be a preadditive monoidal category with bilinear tensor product. Let K₁ and K₂ have
arbitrary, independently indexed complex shapes c₁,c₂, with homology at j₁,j₂ and predecessor
indices i₁ = c₁.prev(j₁), i₂ = c₂.prev(j₂). Write Z₁,Z₂ and H₁,H₂ for their cycles and homology,
and β₁ : K₁,i₁ → Z₁, β₂ : K₂,i₂ → Z₂ for the incoming boundary maps. Assume right tensoring by
Z₂ preserves the cokernel coequalizer of β₁ and left tensoring by H₁ preserves that of β₂.
Assume also that the coproduct of K₁,i₁ ⊗ Z₂ and Z₁ ⊗ K₂,i₂ exists and right tensoring by K₂,i₂
preserves the cokernel coequalizer of β₁. If k : Z₁ ⊗ Z₂ → Z kills the map from the coproduct
whose components are β₁ ⊗ id_Z₂ and id_Z₁ ⊗ β₂, then tensorHomologyDesc k is the unique map H₁ ⊗
H₂ → Z satisfying (π₁ ⊗ π₂) ≫ tensorHomologyDesc k = k.
