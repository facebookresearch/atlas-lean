# A free chart remains free under further restriction

Let `(C₀,J₀)` be a site at universe `u` with additive sheafification and the locally-bijective
comparison on slice sites, and let `S : Sheaf J₀ RingCat.{u}`. For `A : SheafOfModules.{u} S`,
`f : V → W`, `I : Type u`, and an isomorphism `A.over W ≅ free_{S.over W} I`, further
restriction gives `A.over V ≅ free_{S.over V} I`. The isomorphism uses the over-site
comparison, restriction of the given chart, and the free-sheaf comparison.
