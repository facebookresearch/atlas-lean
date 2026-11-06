/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianQCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneSpinBitSignsCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneConjugateGammaData

/-! Exact integer signs of the original Pauli phases and conjugated Gaussian. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
private def bin (b : Bool) : ZMod 2 := if b then 1 else 0
private theorem bin_xor (a b : Bool) : bin (Bool.xor a b) = bin a + bin b := by
  cases a <;> cases b <;> decide
private theorem bin_and (a b : Bool) : bin (a && b) = bin a * bin b := by
  cases a <;> cases b <;> decide
private theorem bin_fold (l : List Bool) (a : Bool) :
    bin (l.foldl Bool.xor a) = bin a + (l.map bin).sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, bin_xor]
    abel
private theorem parity_bin (n r : ℕ) :
    bin (monsterNortonBitParity (n &&& r)) =
      ∑ j : Fin 12, bin (n.testBit j.val) * bin (r.testBit j.val) := by
  have h : monsterNortonBitParity (n &&& r) =
      (List.ofFn (fun j : Fin 12 => (n &&& r).testBit j.val)).foldl Bool.xor false := rfl
  rw [h, bin_fold]
  simp only [bin, Bool.false_eq_true, ite_false, zero_add, List.map_ofFn,
    List.sum_ofFn, Nat.testBit_and]
  apply Finset.sum_congr rfl
  intro j _
  change bin (n.testBit j.val && r.testBit j.val) = _
  rw [bin_and]
  rfl

/-- Binary dot products of source labels are exactly their compact bit parity. -/
theorem generatedSeventhXi_bit_dot (m d : Fin 4096) :
    spinDot (golayLabelCoefficients m) (golayLabelCoefficients d) =
      golayBooleanCast (monsterNortonBitParity (m.val &&& d.val)) := by
  change (∑ j : Fin 12, bin (m.val.testBit j.val) * bin (d.val.testBit j.val)) = _
  exact (parity_bin m.val d.val).symm

/-- Integer signs preserve the actual characteristic-two addition law. -/
theorem generatedSeventhXi_integer_sign_add (c e : ZMod 2) :
    nortonUIntegerSign (c + e) = nortonUIntegerSign c * nortonUIntegerSign e := by
  revert c e
  decide +kernel

/-- Compact dot signs agree with every genuine actual binary phase. -/
theorem generatedSeventhXi_integer_dot_phase (m d : Fin 4096) :
    nortonUIntegerSign (spinDot (golayLabelCoefficients m) (golayLabelCoefficients d)) =
      if monsterNortonBitParity (m.val &&& d.val) then -1 else 1 := by
  rw [generatedSeventhXi_bit_dot]
  cases h : monsterNortonBitParity (m.val &&& d.val) <;>
    simp [golayBooleanCast, nortonUIntegerSign]

/-- The packed diagonal is the complete original Gaussian conjugated by the source word. -/
theorem generatedSeventhXiPlaneConjugateGammaBit_actual (d : Fin 4096) :
    generatedSeventhXiPlaneConjugateGamma d = generatedSeventhXiPlaneConjugateGammaBit d := by
  have hl := generatedSeventhXiPlaneBitCodeLabel_actual 1 d
  simp only [generatedSeventhXiPlaneBitCode, show (1 : Fin 2) ≠ 0 by decide,
    ite_false] at hl
  have ht : generatedSeventhXiPlaneCode.symm (golayLabelCoefficients d) =
      golayLabelCoefficients (generatedSeventhXiPlaneBitCodeLabel 1 d) := by
    rw [← hl]
    exact (nortonUIntegerLabel_inverse _).symm
  simp only [generatedSeventhXiPlaneConjugateGamma, ht,
    generatedSeventhXiPlaneBitGamma_actual, generatedSeventhXiPlaneConjugateGammaBit_lookup]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
