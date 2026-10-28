/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhTetradMonomialData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhTriangleFiveAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionCode

/-! Exact original sign and permutation actions on the ten signed tetrad classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

private theorem permutation_integral (p : golayAutomorphismSubgroup) (u : leechIntegral) :
    (leechIntegralAction (golayPermutationIsometry p) u).val =
      golayIntegerPermute p.val u.val := by
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  exact golayRealPermute_embedding p.val u.val

private theorem source_sign_integral :
    leechIntegralAction (golaySignIsometry (sourceGeneratedSignCode 2))
      (leechSeventhTetradLattice ⟨15, by decide +kernel⟩ false) =
      leechSeventhTetradAtLattice ⟨15, by decide +kernel⟩ 18
        (by decide +kernel) (by decide) true := by
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  change golayRealSign (sourceGeneratedSignCode 2).val _ = _
  rw [golayRealSign_embedding]
  apply congrArg leechCoordinateEmbedding
  change golayIntegerSign (golayEncoder (golayLabelCoefficients 2))
    ((4 : ℤ) • leechSeventhTetradCoefficients 15 false) =
      (4 : ℤ) • leechSeventhTetradAtCoefficients 15 18 true
  unfold leechSeventhTetradCoefficients leechSeventhTetradAtCoefficients
    generatedSeventhFiveFrameCoordinates golayIntegerSign
  decide +kernel

/-- A literal actual Golay sign interchanges the two sign classes on the original tetrad. -/
theorem leechSeventhTetrad_source_sign :
    leechModTwoAction (golaySignIsometry (sourceGeneratedSignCode 2))
      (leechSeventhTetradClass (⟨15, by decide +kernel⟩, false)) =
      leechSeventhTetradClass (⟨15, by decide +kernel⟩, true) := by
  change leechQuotientAut (leechIntegralAction (golaySignIsometry (sourceGeneratedSignCode 2)))
    (leechReduction _) = _
  rw [leechQuotientAut_reduce, source_sign_integral]
  exact leechSeventhTetradAt_class _ _ _ _ true

/-- An actual triangle permutation carries each original sign class
to its omitted-coordinate image. -/
theorem leechSeventhTetrad_permutation (p : generatedSeventhTrianglePermutationSubgroup)
    (t : {i // i ∈ generatedSeventhFiveFrameCoordinates}) (hpt : p.val.val 15 = t.val)
    (b : Bool) :
    leechModTwoAction (golayPermutationIsometry p.val)
      (leechSeventhTetradClass (⟨15, by decide +kernel⟩, b)) =
      leechSeventhTetradClass (t, b) := by
  have hk : p.val.val 18 ∈ generatedSeventhFiveFrameCoordinates :=
    (generatedSeventh_triangle_five_mem p 18).mpr (by decide +kernel)
  have hkt : p.val.val 18 ≠ t.val := by
    intro h
    have he := p.val.val.injective (h.trans hpt.symm)
    norm_num at he
  have hsrc : leechReduction (leechSeventhTetradAtLattice ⟨15, by decide +kernel⟩ 18
      (by decide +kernel) (by decide) b) =
      leechSeventhTetradClass (⟨15, by decide +kernel⟩, b) :=
    leechSeventhTetradAt_class _ _ _ _ b
  rw [← hsrc]
  change leechQuotientAut (leechIntegralAction (golayPermutationIsometry p.val))
    (leechReduction _) = _
  rw [leechQuotientAut_reduce]
  have hv : leechIntegralAction (golayPermutationIsometry p.val)
      (leechSeventhTetradAtLattice ⟨15, by decide +kernel⟩ 18
        (by decide +kernel) (by decide) b) =
      leechSeventhTetradAtLattice t (p.val.val 18) hk hkt b := by
    apply Subtype.ext
    rw [permutation_integral]
    ext i
    simp only [leechSeventhTetradAtLattice, golayIntegerPermute, Pi.smul_apply,
      smul_eq_mul, leechSeventhTetradAtCoefficients, Pi.single_apply]
    have heq : p.val.val.symm i = 15 ↔ i = t.val := by
      rw [Equiv.symm_apply_eq, hpt]
    simp only [generatedSeventh_triangle_five_inverse_mem p i, ne_eq, heq, Equiv.symm_apply_eq]
  rw [hv]
  exact leechSeventhTetradAt_class t _ hk hkt b

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
