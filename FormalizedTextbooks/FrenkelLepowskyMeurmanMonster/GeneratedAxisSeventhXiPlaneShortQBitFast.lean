/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortQBitPackedData

/-! Exact packed mask evaluation of the whole corrected Xi automorphism and central phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- XOR of the actual packed image columns selected by a full input vector. -/
def generatedSeventhXiShortQImageFast (x : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun j : Fin 24 =>
    if x.testBit j.val then generatedSeventhXiShortQColumnPacked j else 0))

/-- The complete selected phase rows are added in characteristic two. -/
def generatedSeventhXiShortQPhaseSelected (x : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if x.testBit i.val then generatedSeventhXiShortQPhaseRowPacked i else 0))

/-- Parity of all twenty-four phase coordinates, including both original source halves. -/
def generatedSeventhXiShortQPhaseFast (x : ℕ) : Bool :=
  (List.ofFn (fun j : Fin 24 =>
    (generatedSeventhXiShortQPhaseSelected x &&& x).testBit j.val)).foldl Bool.xor false

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

/-- Packed source columns preserve every original binary image mask. -/
theorem generatedSeventhXiShortQImageFast_actual (x : ℕ) :
    generatedSeventhXiShortQImageFast x = generatedSeventhXiShortQImageMask x := by
  simp only [generatedSeventhXiShortQImageFast, generatedSeventhXiShortQImageMask,
    generatedSeventhXiShortQColumnPacked_actual]

/-- The selected rows decode to the original quadratic phase coefficient vector. -/
theorem generatedSeventhXiShortQPhaseSelected_decode (x : ℕ) (j : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedSeventhXiShortQPhaseSelected x) j =
      ∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode x i *
        generatedSeventhXiPlaneQPhaseMatrix i j := by
  rw [generatedSeventhXiShortQPhaseSelected, monsterCo1GeometryBinaryMaskDecode_sum,
    List.map_ofFn, List.sum_ofFn]
  simp only [Finset.sum_apply, Function.comp_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [generatedSeventhXiShortQPhaseRowPacked_actual]
  cases hx : x.testBit i.val <;>
    simp [monsterCo1GeometryBinaryMaskDecode, generatedSeventhXiPlaneQPhaseMatrix,
      golayBooleanCast, hx]

/-- The packed parity gives the full original central correction of every actual input. -/
theorem generatedSeventhXiShortQPhaseFast_actual (x : ℕ) :
    golayBooleanCast (generatedSeventhXiShortQPhaseFast x) =
      generatedFourthLiftQMatrixPhase generatedSeventhXiPlaneQPhaseMatrix
        (monsterCo1GeometryBinaryMaskDecode x) := by
  change bin (generatedSeventhXiShortQPhaseFast x) = _
  rw [generatedSeventhXiShortQPhaseFast, bin_fold]
  simp only [bin, Bool.false_eq_true, ite_false, zero_add, List.map_ofFn,
    List.sum_ofFn, Nat.testBit_and]
  change (∑ j : Fin 24, bin
    ((generatedSeventhXiShortQPhaseSelected x).testBit j.val && x.testBit j.val)) = _
  simp only [bin_and]
  change (∑ j : Fin 24,
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedSeventhXiShortQPhaseSelected x) j *
      monsterCo1GeometryBinaryMaskDecode x j) = _
  simp only [generatedSeventhXiShortQPhaseSelected_decode, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact (Matrix.toBilin'_apply generatedSeventhXiPlaneQPhaseMatrix _ _).symm

/-- Fast packed masks retain both the genuine image and its entire central coefficient. -/
theorem generatedSeventhXiShortQFast_image (x : ℕ) :
    generatedSeventhXiPlaneQMatrixHom (generatedSeventhXiShortQMask x) =
      ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode
          (n := 24) (generatedSeventhXiShortQImageFast x)),
        ofAdd (golayBooleanCast (generatedSeventhXiShortQPhaseFast x))⟩ := by
  apply NormalizedCocycleExtension.Extension.ext
  · change ofAdd (generatedSeventhXiPlaneQMatrix *ᵥ
        monsterCo1GeometryBinaryMaskDecode x) = _
    rw [generatedSeventhXiShortQImageFast_actual, generatedSeventhXiShortQImageMask_decode]
  · change ofAdd (0 + generatedFourthLiftQMatrixPhase generatedSeventhXiPlaneQPhaseMatrix
        (monsterCo1GeometryBinaryMaskDecode x)) = _
    rw [zero_add, generatedSeventhXiShortQPhaseFast_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
