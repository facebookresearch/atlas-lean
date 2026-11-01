/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete octad product preservation from its actual octad and XYZ cubic tests. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityABCOctad
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCubic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The diagonal and ABC cubic tests are already proved. The remaining
octad and XYZ cubic tests imply the actual octad basis product equation. -/
theorem sExtra_octad_product_of_cubic_tests (o p : Fin 759) (e f : Fin 64)
    (hO : ∀ (u : Fin 759) (g : Fin 64),
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityOctadBasis p f))) (sExtra (trialityOctadBasis u g)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
          (trialityOctadBasis u g))
    (hT : ∀ (s : Fin 3) (k : Fin 49152),
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityOctadBasis p f))) (sExtra (trialityXYZBasis s k)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
          (trialityXYZBasis s k)) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f) := by
  apply (trialityProductPreserved_iff_source_cubic _ _).mpr
  intro i
  rcases i with i | (⟨s,q⟩ | (⟨u,g⟩ | ⟨s,k⟩)) <;> simp only [trialitySourceBasis]
  · rw [griessCubic_triality_cycle, griessCubic_triality_cycle]
    apply griessCubic_triality_of_pair
    exact sExtra_preserves_diagonal_product _ _
  · rw [griessCubic_triality_cycle, griessCubic_triality_cycle]
    apply griessCubic_triality_of_pair
    exact sExtra_preserves_ABC_octad_product s q o e
  · exact hO u g
  · exact hT s k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
