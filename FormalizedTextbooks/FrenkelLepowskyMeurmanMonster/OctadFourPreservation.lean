/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual octad product preservation from the remaining sum-octad cubic identity. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCubicPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCubicZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductCompletion

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All cubic testers outside the sum octad are proved zero. The actual
sum-octad cubic identity therefore closes each four-point octad product. -/
theorem sExtra_four_octad_product_of_sum_cubic (o p : Fin 759) (e f : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hc : ∀ (u : Fin 759) (g : Fin 64),
      golayOctadWord u = golayOctadWord o + golayOctadWord p →
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityOctadBasis p f))) (sExtra (trialityOctadBasis u g)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
          (trialityOctadBasis u g)) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f) := by
  apply sExtra_octad_product_of_cubic_tests o p e f
  · intro u g
    by_cases hu : golayOctadWord u = golayOctadWord o + golayOctadWord p
    · exact hc u g hu
    · rw [griessForm_transformed_octad_cubic_zero o p u e f g hfour hu,
        griessForm_octad_cubic_zero o p u e f g hfour hu]
  · intro s k
    rw [griessForm_transformed_octad_octad_XYZ_zero,
      griessForm_octad_octad_XYZ_zero]

/-- The only remaining octad×octad input is the actual cubic of its sum octad. -/
theorem sExtra_octad_product_of_sum_cubics
    (hc : ∀ (o p u : Fin 759) (e f g : Fin 64),
      (golayOctadIntersection o p).card = 4 →
      golayOctadWord u = golayOctadWord o + golayOctadWord p →
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityOctadBasis p f))) (sExtra (trialityOctadBasis u g)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
          (trialityOctadBasis u g))
    (o : Fin 759) (e : Fin 64) (p : Fin 759) (f : Fin 64) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f) := by
  apply sExtra_preserves_octad_product_of_four _ o e p f
  intro v w a b hvw
  exact sExtra_four_octad_product_of_sum_cubic v w a b hvw
    (fun u g hu => hc v w u a b g hvw hu)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
