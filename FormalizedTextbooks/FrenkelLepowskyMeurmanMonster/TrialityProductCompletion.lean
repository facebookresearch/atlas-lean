/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Completion of triality multiplication from the two remaining octad families. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityABCOctad
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityXYZMixedCubic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityXYZProductReduction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All XYZ products follow from the explicit remaining octad×XYZ family. -/
theorem sExtra_preserves_XYZ_product_of_octad
    (hOT : ∀ (o : Fin 759) (e : Fin 64) (s : Fin 3) (k : Fin 49152),
      TrialityProductPreserved (trialityOctadBasis o e) (trialityXYZBasis s k))
    (s t : Fin 3) (k l : Fin 49152) :
    TrialityProductPreserved (trialityXYZBasis s k) (trialityXYZBasis t l) :=
  triality_XYZ_XYZ_product_of_octad_and_mixed hOT
    trialityXYZ_cubic_mixed_preserved s t k l

/-- The full product equation now requires only the two actual octad product families.
All diagonal, ABC and XYZ cubic prerequisites are proved and instantiated here. -/
theorem sExtra_preserves_product_of_octad_pairs
    (hOO : ∀ (o : Fin 759) (e : Fin 64) (p : Fin 759) (f : Fin 64),
      TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f))
    (hOT : ∀ (o : Fin 759) (e : Fin 64) (s : Fin 3) (k : Fin 49152),
      TrialityProductPreserved (trialityOctadBasis o e) (trialityXYZBasis s k)) :
    ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y) := by
  apply sExtra_preserves_product_of_source_pairs
  · intro s p t q
    exact sExtra_preserves_ABC_product p q s t
  · intro s p o e
    exact sExtra_preserves_ABC_octad_product s p o e
  · intro s p t k
    let a := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm k
    have ha : (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152) a = k := by
      dsimp only [a]
      exact (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).apply_symm_apply k
    rw [← ha]
    exact triality_ABC_XYZ_product s t p a.1 a.2
  · exact hOO
  · exact hOT
  · intro s k t l
    exact sExtra_preserves_XYZ_product_of_octad hOT s t k l

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
