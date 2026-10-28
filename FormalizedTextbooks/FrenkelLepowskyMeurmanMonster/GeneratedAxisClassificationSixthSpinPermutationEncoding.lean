/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinEncoding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Exact inverse code labels and original Parker phases using bounded binary operations. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem mask_sum_bound {m : ℕ} (xs : List ℕ)
    (h : ∀ a ∈ xs, a < 2 ^ m) : monsterCo1GeometryBinaryMaskSum xs < 2 ^ m := by
  induction xs with
  | nil => simp [monsterCo1GeometryBinaryMaskSum]
  | cons a xs ih =>
    exact Nat.xor_lt_two_pow (h a (by simp))
      (ih (fun b hb => h b (by simp [hb])))

/-- The selected inverse source-code columns form a literal twelve-bit XOR label. -/
def generatedSixthSpinInverseMask (k : Fin 2) (n : Fin 4096) : Fin 4096 :=
  ⟨monsterCo1GeometryBinaryMaskSum (List.ofFn (fun j : Fin 12 =>
    if n.val.testBit j.val then (omegaOrbitPermCodeImages (Fin.natAdd 2 k) j).val else 0)), by
    apply mask_sum_bound (m := 12)
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    split_ifs
    · exact (omegaOrbitPermCodeImages (Fin.natAdd 2 k) j).isLt
    · norm_num⟩

private theorem inverse_code_apply (k : Fin 2) (t : SpinIndex) :
    (monsterSourcePermutationCode k).symm t =
      monsterSourcePermutationCodeMatrix (Fin.natAdd 2 k) *ᵥ t := rfl

/-- The fast inverse address is the genuine inverse source-code linear action. -/
theorem generatedSixth_spin_inverse_mask (k : Fin 2) (n : Fin 4096) :
    golayLabelCoefficients (generatedSixthSpinInverseMask k n) =
      (monsterSourcePermutationCode k).symm (golayLabelCoefficients n) := by
  rw [inverse_code_apply]
  have h := monsterCo1GeometryBinaryMaskDecode_sum (n := 12)
    (List.ofFn (fun j : Fin 12 =>
      if n.val.testBit j.val then (omegaOrbitPermCodeImages (Fin.natAdd 2 k) j).val else 0))
  rw [List.map_ofFn, List.sum_ofFn] at h
  ext i
  have hi := congrFun h i
  simp only [Finset.sum_apply, Function.comp_apply] at hi
  change golayLabelCoefficients (generatedSixthSpinInverseMask k n) i = _ at hi
  rw [hi]
  simp only [Matrix.mulVec, dotProduct, monsterSourcePermutationCodeMatrix]
  apply Finset.sum_congr rfl
  intro j _
  cases hb : n.val.testBit j.val <;>
    simp [monsterCo1GeometryBinaryMaskDecode, golayLabelCoefficients, hb]

/-- The complete original quadratic phase, computed as twelve binary dot products. -/
def generatedSixthSpinPhaseMask (k : Fin 2) (n : Fin 4096) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 12 =>
    if n.val.testBit i.val then
      monsterCo1GeometryBinaryMaskDot 12 (monsterSourcePermutationPhaseRows k i) n.val else 0))

/-- The phase mask is the actual Parker quadratic polynomial, including diagonal terms. -/
theorem generatedSixth_spin_phase_mask (k : Fin 2) (n : Fin 4096) :
    (if (generatedSixthSpinPhaseMask k n).testBit 0 then (1 : ZMod 2) else 0) =
      monsterMonomialQuadratic (monsterSourcePermutationPhaseData k)
        (golayLabelCoefficients n) := by
  unfold generatedSixthSpinPhaseMask
  rw [monsterCo1GeometryBinaryMaskSum_parity, List.map_ofFn, List.sum_ofFn]
  dsimp only [Function.comp_apply]
  unfold monsterMonomialQuadratic
  apply Finset.sum_congr rfl
  intro i _
  cases hb : n.val.testBit i.val
  · simp [hb, golayLabelCoefficients]
  · simp only [ite_true]
    rw [monsterCo1GeometryBinaryMaskDot_decode]
    apply Finset.sum_congr rfl
    intro j _
    simp [monsterCo1GeometryBinaryMaskDecode, monsterSourcePermutationPhaseData,
      golayBooleanCast, golayLabelCoefficients, hb, mul_comm]

/-- Fast executable permutation coordinates retain the actual inverse code and quadratic sign. -/
def generatedSixthIntegerPermutationFast (k : Fin 2) (v : NortonUIntegerVector)
    (n : Fin 4096) : ℤ :=
  let a := generatedSixthSpinInverseMask k n
  let z := v a
  if z = 0 then 0 else (if (generatedSixthSpinPhaseMask k a).testBit 0 then -1 else 1) * z

/-- The fast binary permutation is the original integer spin permutation. -/
theorem generatedSixth_integer_permutation_fast (k : Fin 2) (v : NortonUIntegerVector) :
    generatedSixthIntegerPermutation k v = generatedSixthIntegerPermutationFast k v := by
  funext n
  dsimp only [generatedSixthIntegerPermutation, generatedSixthIntegerPermutationFast]
  rw [← generatedSixth_spin_inverse_mask, nortonUIntegerLabel_coeff]
  by_cases hz : v (generatedSixthSpinInverseMask k n) = 0
  · simp only [hz, ite_true, mul_zero]
  · simp only [hz, ite_false]
    unfold nortonUIntegerSign
    rw [← generatedSixth_spin_phase_mask]
    cases hb : (generatedSixthSpinPhaseMask k (generatedSixthSpinInverseMask k n)).testBit 0 <;>
      norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
