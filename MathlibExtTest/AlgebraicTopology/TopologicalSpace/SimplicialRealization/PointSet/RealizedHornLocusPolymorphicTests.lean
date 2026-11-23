/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornLocusPolymorphic

@[expose] public section

/-!
# Polymorphic realized horn locus client test

Downstream clients for the range equation, the legacy lifted iso, and the raw
cross-universe homeomorphism, including a concrete universe-one client and a
wrong-source-universe guard. No retraction, Kan, or weak-equivalence claim.
-/

set_option autoImplicit false

universe u

#check @hornRange_image_eq_locus_u

#check @realizedHornIsoUliftHornLocus

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornLocusPolymorphicTests

theorem image_eq_locus_one_zero :
    (SimplexCategory.toTopHomeo (SimplexCategory.mk 1)) ''
      Set.range (SSet.toTop.{1}.map (SSet.horn.{1} 1 (⟨0, by decide⟩ : Fin (1 + 1))).ι) =
      {t : Convexity.StdSimplex ℝ (Fin (1 + 1)) |
        ∃ j, j ≠ (⟨0, by decide⟩ : Fin (1 + 1)) ∧ t.weights j = 0} :=
  hornRange_image_eq_locus_u 1 _ (by decide : 0 < 1)

noncomputable def hornIso_one_zero :
    SSet.toTop.{1}.obj (SSet.horn.{1} 1 (⟨0, by decide⟩ : Fin (1 + 1))) ≅
      TopCat.uliftFunctor.obj
        (TopCat.of {t : Convexity.StdSimplex ℝ (Fin (1 + 1)) //
          ∃ j, j ≠ (⟨0, by decide⟩ : Fin (1 + 1)) ∧ t.weights j = 0}) :=
  realizedHornIsoUliftHornLocus 1 _ (by decide : 0 < 1)

noncomputable def rawHomeomorph_client
    (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n k)) ≃ₜ
      {t : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        ∃ j, j ≠ k ∧ t.weights j = 0} :=
  realizedHornHomeomorphHornLocus n k hn

noncomputable def rawHomeomorph_one_zero_u1 :
    ↥(SSet.toTop.{1}.obj
      (SSet.horn.{1} 1 (⟨0, by decide⟩ : Fin (1 + 1)))) ≃ₜ
      {t : Convexity.StdSimplex ℝ (Fin (1 + 1)) //
        ∃ j, j ≠ (⟨0, by decide⟩ : Fin (1 + 1)) ∧ t.weights j = 0} :=
  realizedHornHomeomorphHornLocus 1 _ (by decide)

/-- error: Type mismatch -/
#guard_msgs (error, substring := true) in
#check (realizedHornHomeomorphHornLocus.{1} 1
    (⟨0, by decide⟩ : Fin (1 + 1)) (by decide) :
  ↥(SSet.toTop.{0}.obj
    (SSet.horn.{0} 1 (⟨0, by decide⟩ : Fin (1 + 1)))) ≃ₜ
    {t : Convexity.StdSimplex ℝ (Fin (1 + 1)) //
      ∃ j, j ≠ (⟨0, by decide⟩ : Fin (1 + 1)) ∧ t.weights j = 0})

#print axioms hornRange_image_eq_locus_u

#print axioms realizedHornIsoUliftHornLocus

#print axioms image_eq_locus_one_zero

#print axioms hornIso_one_zero

#print axioms realizedHornHomeomorphHornLocus

end MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornLocusPolymorphicTests
