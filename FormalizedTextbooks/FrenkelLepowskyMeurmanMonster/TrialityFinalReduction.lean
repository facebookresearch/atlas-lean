/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The full actual triality product law from the two remaining octad color transitions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXYZCycleClosure

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every source product family except octad×XYZ is proved and instantiated. -/
theorem sExtra_preserves_product_of_octadXYZ
    (hOT : ∀ (o : Fin 759) (e : Fin 64) (s : Fin 3) (k : Fin 49152),
      TrialityProductPreserved (trialityOctadBasis o e) (trialityXYZBasis s k)) :
    ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y) :=
  sExtra_preserves_product_of_octad_pairs sExtra_preserves_octad_product hOT

/-- Only the two actual octad color transitions X→Y and Y→Z remain as
explicit inputs. All other source cubic tests and product families are proved. -/
theorem sExtra_preserves_product_of_two_octad_cubics
    (hX : ∀ (o : Fin 759) (e : Fin 64) (k l : Fin 49152),
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityXYZBasis 0 k))) (sExtra (trialityXYZBasis 0 l)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 0 k))
          (trialityXYZBasis 0 l))
    (hY : ∀ (o : Fin 759) (e : Fin 64) (k l : Fin 49152),
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityXYZBasis 1 k))) (sExtra (trialityXYZBasis 1 l)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 1 k))
          (trialityXYZBasis 1 l)) :
    ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y) :=
  sExtra_preserves_product_of_octadXYZ
    (sExtra_octadXYZ_product_of_two_transitions sExtra_preserves_octad_product hX hY)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
