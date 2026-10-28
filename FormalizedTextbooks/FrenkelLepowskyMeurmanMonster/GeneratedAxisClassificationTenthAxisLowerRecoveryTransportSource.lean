/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7Conjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySmallSourceData

/-! A complete original one-Xi source word for the actual Tenth coordinate transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The complete original four-letter Golay source transporting the first tetrad. -/
def generatedTenthAxisLowerRecoveryTransportPermutationWord : Fin 4 → Fin 129 := ![0, 26, 67, 73]

/-- A genuine original Golay automorphism obtained from all four certified source letters. -/
def generatedTenthAxisLowerRecoveryTransportPermutation : golayAutomorphismSubgroup :=
  ((List.finRange 4).map fun k => golayStabilizerAutomorphism
    (generatedTenthAxisLowerRecoveryTransportPermutationWord k)).prod

/-- The exact integer sign of an actual original Golay code coordinate. -/
def generatedTenthAxisLowerRecoveryIntegerSign (c : golayCode) (i : Fin 24) : ℤ :=
  if c.val i = 0 then 1 else -1

/-- All 576 original coordinates of the single-Xi source numerator. -/
def generatedTenthAxisLowerRecoveryTransportNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j =>
    generatedTenthAxisLowerRecoveryIntegerSign (generatedTenthAxisLowerRecoveryCode 3559) i *
      co1XiNumerator (generatedTenthAxisLowerRecoveryTransportPermutation.val.symm i)
        (generatedTenthAxisLowerRecoveryTransportPermutation.val.symm j) *
      generatedTenthAxisLowerRecoveryIntegerSign (generatedTenthAxisLowerRecoveryCode 64) j

/-- The entire actual transport numerator equals the complete original one-Xi source numerator. -/
theorem generatedTenth_axis_lower_recovery_transport_numerator :
    generatedTenthAxisLowerRecoveryTransportNumerator = generatedTenthE7Numerator := by
  decide +kernel

/-- The complete genuine original source word, preserving both original sign factors. -/
def generatedTenthAxisLowerRecoveryTransportSource : leechIsomSubgroup :=
  golaySignIsometry (generatedTenthAxisLowerRecoveryCode 3559) *
    golayPermutationIsometry generatedTenthAxisLowerRecoveryTransportPermutation *
      co1XiIsometry *
        golayPermutationIsometry generatedTenthAxisLowerRecoveryTransportPermutation⁻¹ *
          golaySignIsometry (generatedTenthAxisLowerRecoveryCode 64)

private theorem sign_cast (c : golayCode) (i : Fin 24) :
    qSign (c.val i) = (generatedTenthAxisLowerRecoveryIntegerSign c i : ℝ) := by
  by_cases h : c.val i = 0 <;> simp [qSign,
    generatedTenthAxisLowerRecoveryIntegerSign, h]

/-- Every real matrix entry of the entire source word retains its true denominator two. -/
theorem generatedTenth_axis_lower_recovery_transport_source_matrix (i j : Fin 24) :
    leechIsomMatrix generatedTenthAxisLowerRecoveryTransportSource i j =
      (generatedTenthAxisLowerRecoveryTransportNumerator i j : ℝ) / 2 := by
  let p := generatedTenthAxisLowerRecoveryTransportPermutation
  let c := generatedTenthAxisLowerRecoveryCode 3559
  let d := generatedTenthAxisLowerRecoveryCode 64
  change qSign (c.val i) *
    (∑ k : Fin 24, co1XiMatrix (p.val.symm i) k *
      (qSign (d.val (p.val k)) * (Pi.single j (1 : ℝ) : Fin 24 → ℝ) (p.val k))) = _
  have hs : (∑ k : Fin 24, co1XiMatrix (p.val.symm i) k *
      (qSign (d.val (p.val k)) * (Pi.single j (1 : ℝ) : Fin 24 → ℝ) (p.val k))) =
      co1XiMatrix (p.val.symm i) (p.val.symm j) * qSign (d.val j) := by
    rw [Finset.sum_eq_single (p.val.symm j)]
    · rw [p.val.apply_symm_apply]
      simp only [Pi.single_apply, ite_true, mul_one]
    · intro k _ hk
      have hp : p.val k ≠ j := by
        intro h
        apply hk
        exact p.val.injective (h.trans (p.val.apply_symm_apply j).symm)
      simp only [Pi.single_apply, hp, ite_false, mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hs, sign_cast, sign_cast]
  have hxi : co1XiMatrix (p.val.symm i) (p.val.symm j) =
      (co1XiNumerator (p.val.symm i) (p.val.symm j) : ℝ) / 2 := by
    simp [co1XiMatrix, co1XiMatrixQ]
  rw [hxi]
  change (generatedTenthAxisLowerRecoveryIntegerSign c i : ℝ) *
    ((co1XiNumerator (p.val.symm i) (p.val.symm j) : ℝ) / 2 *
      (generatedTenthAxisLowerRecoveryIntegerSign d j : ℝ)) =
      ((generatedTenthAxisLowerRecoveryIntegerSign c i *
        co1XiNumerator (p.val.symm i) (p.val.symm j) *
          generatedTenthAxisLowerRecoveryIntegerSign d j : ℤ) : ℝ) / 2
  push_cast
  ring

/-- The certified actual Tenth coordinate isometry equals this entire original source word. -/
theorem generatedTenth_axis_lower_recovery_transport_source_actual :
    generatedTenthAxisLowerRecoveryTransportSource = generatedTenthE7Isometry := by
  have hm : leechIsomMatrix generatedTenthAxisLowerRecoveryTransportSource =
      generatedTenthE7Matrix := by
    ext i j
    rw [generatedTenth_axis_lower_recovery_transport_source_matrix,
      generatedTenth_axis_lower_recovery_transport_numerator]
    simp [generatedTenthE7Matrix, generatedTwelfthCertifiedRealMatrix, div_eq_inv_mul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [← leechIsomMatrix_mulVec generatedTenthAxisLowerRecoveryTransportSource x, hm]
  exact (generatedTenth_e7_isometry_apply x).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
