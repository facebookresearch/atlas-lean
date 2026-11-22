/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerA2CobaseAcyclicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerHornFactorization

/-!
# Every SAME original A1 or A2 generator pushout is genuinely acyclic

The genuine original Hom-horn left class retains all scalar horn
positions and dimensions. Its existing full lifting and original word
acyclicity prove every A1 pushout weak. Together with the actual A2
interval cobase theorem, every original combined-generator pushout is
both a genuine global C0 cofibration and the SAME DK weak map.

This proves Bergner v2, Lemma Push, with the exact original generators.
Simultaneous and transfinite cell closure and the global model theorem
are separate statements.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.Bergner

/-- The SAME actual original scalar horn is in the genuine original global Hom-horn left class. -/
theorem generatingHomHorns_le_homHornLeft : generatingHomHorns.{u} ≤ homHornLeft := by
  intro C D p hp E H r hr
  exact ((generatingHomHorns_rlp_iff r).mpr hr) p hp

/-- Every actual original full-Hom horn cobase change is genuinely DK weak. -/
theorem generatingHomHorns_pushouts_le_weak : generatingHomHorns.{u}.pushouts ≤ EnrichedDwyerKan.weakEquivalences := by
  rintro C D q ⟨A, B, p, g, j, hp, sq⟩
  have hl : homHornLeft p := generatingHomHorns_le_homHornLeft p hp
  have hq : homHornLeft q := MorphismProperty.of_isPushout sq hl
  exact (HornFactorization.homHornLeft_le_cofibration_inf_weak q hq).2

end CategoryTheory.SimplicialEnrichment.Bergner

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily

/-- Every SAME actual original combined A1+A2 generator is genuinely C0 cofibrant and DK weak. -/
theorem generatingTrivialCofibrations_le_cofibration_weak :
    generatingTrivialCofibrations.{u} ≤ Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences := by
  intro C D f hf
  rcases hf with hf | hf
  · exact Bergner.HornFactorization.homHornLeft_le_cofibration_inf_weak f
      (Bergner.generatingHomHorns_le_homHornLeft f hf)
  · exact generatingIntervals_le_cofibration_weak f hf

/-- Every SAME actual original combined-generator cobase change is genuinely DK weak. -/
theorem generatingTrivialCofibrations_pushouts_le_weak :
    generatingTrivialCofibrations.{u}.pushouts ≤ EnrichedDwyerKan.weakEquivalences := by
  rintro C D f ⟨A, B, p, g, j, hp, sq⟩
  rcases hp with hp | hp
  · exact Bergner.generatingHomHorns_pushouts_le_weak f ⟨A, B, p, g, j, hp, sq⟩
  · exact generatingIntervals_pushouts_le_weak f ⟨A, B, p, g, j, hp, sq⟩

/-- The SAME whole original source arrow in any actual A1 or A2 pushout is genuinely DK weak. -/
theorem weak_of_generator_isPushout {A B C D : Carrier.{u}} (i : A ⟶ B)
    (hi : generatingTrivialCofibrations i) (g : A ⟶ C) (j : B ⟶ D) (f : C ⟶ D)
    (sq : IsPushout i g j f) : EnrichedDwyerKan.weakEquivalences f :=
  generatingTrivialCofibrations_pushouts_le_weak _ (MorphismProperty.pushouts_mk _ sq.flip hi)

/-- Every SAME actual original combined-generator pushout is both genuinely C0 cofibrant and DK weak. -/
theorem generatingTrivialCofibrations_pushouts_le_cofibration_weak :
    generatingTrivialCofibrations.{u}.pushouts ≤ Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences := by
  rintro C D f ⟨A, B, p, g, j, hp, sq⟩
  exact ⟨MorphismProperty.of_isPushout sq (generatingTrivialCofibrations_le_cofibration_weak p hp).1,
    weak_of_generator_isPushout p hp g j f sq.flip⟩

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
