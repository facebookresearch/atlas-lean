/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortThetaSplitData

/-! Algebraic transport for the two original six-bit code halves and their polar masks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The six original binary coefficients of a finite source label. -/
def generatedSeventhXiShortCodeSix (d : Fin 64) : Fin 6 → ZMod 2 :=
  fun i => golayBooleanCast (d.val.testBit i.val)

/-- Both original source halves, including omega, reconstruct the actual twelve coefficients. -/
theorem generatedSeventhXiShortTheta_code_split (d : Fin 4096) :
    golayLabelCoefficients d =
      Fin.append (generatedSeventhXiShortCodeSix (generatedSeventhXiShortThetaLowCode d)) 0 +
        Fin.append 0 (generatedSeventhXiShortCodeSix (generatedSeventhXiShortThetaHighCode d)) := by
  funext k
  refine Fin.addCases (m := 6) (n := 6) (fun i => ?_) (fun i => ?_) k
  · have hb : (d.val % 64).testBit i.val = d.val.testBit i.val := by
      change (d.val % 2 ^ 6).testBit i.val = _
      rw [Nat.testBit_mod_two_pow]
      simp only [i.isLt, decide_true, Bool.true_and]
    simp only [Pi.add_apply, Fin.append_left, Pi.zero_apply, add_zero,
      generatedSeventhXiShortCodeSix, generatedSeventhXiShortThetaLowCode,
      golayLabelCoefficients, Fin.val_castAdd, hb, golayBooleanCast]
  · have hb : (d.val / 64).testBit i.val = d.val.testBit (6 + i.val) := by
      simpa only [Nat.add_comm, show (2 : ℕ) ^ 6 = 64 by norm_num] using
        (Nat.testBit_div_two_pow (n := 6) d.val i.val)
    simp only [Pi.add_apply, Fin.append_right, Pi.zero_apply, zero_add,
      generatedSeventhXiShortCodeSix, generatedSeventhXiShortThetaHighCode,
      golayLabelCoefficients, Fin.val_natAdd, hb, golayBooleanCast]

private theorem code_fold (l h : Fin 64) (xs : List (Fin 6)) (a : Fin 4096) :
    golayLabelCoefficients (xs.foldl (fun c i =>
      if l.val.testBit i.val then monsterNortonBitXor c (generatedSeventhXiShortThetaCross i h)
      else c) a) = golayLabelCoefficients a +
        (xs.map (fun i => if l.val.testBit i.val then
          golayLabelCoefficients (generatedSeventhXiShortThetaCross i h) else 0)).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    cases l.val.testBit i.val <;> simp [monsterNortonBitXor_coeff, add_assoc]

/-- The six cross-polar mask selections become the exact original binary coefficient sum. -/
theorem generatedSeventhXiShortThetaCrossSum_coeff (l h : Fin 64) :
    golayLabelCoefficients (generatedSeventhXiShortThetaCrossSum l h) =
      ∑ i : Fin 6, if l.val.testBit i.val then
        golayLabelCoefficients (generatedSeventhXiShortThetaCross i h) else 0 := by
  rw [generatedSeventhXiShortThetaCrossSum, code_fold]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn]
  have h0 : golayLabelCoefficients (0 : Fin 4096) = 0 := by
    funext i
    simp [golayLabelCoefficients]
  rw [h0, zero_add]
  rfl

/-- The packed evaluator retains the original lower, upper, and cross coefficient vectors. -/
theorem generatedSeventhXiShortThetaSplit_coeff (d : Fin 4096) :
    golayLabelCoefficients (generatedSeventhXiShortThetaSplit d) =
      golayLabelCoefficients
          (generatedSeventhXiShortThetaLow (generatedSeventhXiShortThetaLowCode d)) +
        golayLabelCoefficients
          (generatedSeventhXiShortThetaHigh (generatedSeventhXiShortThetaHighCode d)) +
        ∑ i : Fin 6, if (generatedSeventhXiShortThetaLowCode d).val.testBit i.val then
          golayLabelCoefficients (generatedSeventhXiShortThetaCross i
            (generatedSeventhXiShortThetaHighCode d)) else 0 := by
  simp only [generatedSeventhXiShortThetaSplit, monsterNortonBitXor_coeff,
    generatedSeventhXiShortThetaCrossSum_coeff, add_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
