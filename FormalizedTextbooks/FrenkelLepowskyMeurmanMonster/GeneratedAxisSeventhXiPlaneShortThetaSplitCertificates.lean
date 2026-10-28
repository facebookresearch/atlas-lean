/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortThetaSplitAlgebra

/-! Ordinary-kernel certificates of the actual source theta and cross-polar mask tables. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every complete original lower-half Parker mask is retained as a single Nat equality.
/-- All lower-half table entries are exactly the original Parker theta masks. -/
theorem generatedSeventhXiShortThetaLow_mask : ∀ l : Fin 64,
    parkerThetaMask l.val = (generatedSeventhXiShortThetaLow l).val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The complete upper-half table retains its actual omega bit and source mask.
/-- All upper-half table entries are exactly the original Parker theta masks. -/
theorem generatedSeventhXiShortThetaHigh_mask : ∀ h : Fin 64,
    parkerThetaMask (64 * h.val) = (generatedSeventhXiShortThetaHigh h).val := by
  decide +kernel

/-- The original cross-polar mask of a lower source basis element with an upper word. -/
def generatedSeventhXiShortThetaCrossSource (i : Fin 6) (h : Fin 64) : ℕ :=
  (List.finRange 6).foldl (fun c j => c ^^^
    (if h.val.testBit j.val then
      parkerBasisAssociatorMasks (Fin.castAdd 6 i) (Fin.natAdd 6 j) else 0)) 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Each complete source cross-mask is checked against the original associator coefficients.
/-- All cross-polar entries retain the complete actual associator masks. -/
theorem generatedSeventhXiShortThetaCross_mask : ∀ i : Fin 6, ∀ h : Fin 64,
    generatedSeventhXiShortThetaCrossSource i h =
      (generatedSeventhXiShortThetaCross i h).val := by
  decide +kernel

set_option maxRecDepth 10000 in
-- Only original binary coefficient labels are compared here; no theta values are assumed.
/-- An original lower-half source label has exactly its six nonzero coefficient positions. -/
theorem generatedSeventhXiShortThetaLow_code : ∀ l : Fin 64,
    golayLabelCoefficients ⟨l.val, by omega⟩ =
      Fin.append (generatedSeventhXiShortCodeSix l) (0 : Fin 6 → ZMod 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
-- The original upper-half source label includes all six positions, including omega.
/-- An original upper-half source label has exactly its six nonzero coefficient positions. -/
theorem generatedSeventhXiShortThetaHigh_code : ∀ h : Fin 64,
    golayLabelCoefficients ⟨64 * h.val, by omega⟩ =
      Fin.append (0 : Fin 6 → ZMod 2) (generatedSeventhXiShortCodeSix h) := by
  decide +kernel

/-- Complete original lower-half theta coefficients equal the checked table. -/
theorem generatedSeventhXiShortThetaLow_polynomial (l : Fin 64) :
    sourceCodeThetaPolynomial (Fin.append (generatedSeventhXiShortCodeSix l) (0 : Fin 6 → ZMod 2)) =
      golayLabelCoefficients (generatedSeventhXiShortThetaLow l) := by
  rw [← generatedSeventhXiShortThetaLow_code l]
  funext k
  rw [← sourceCodeThetaPolynomial_mask]
  simp only [generatedSeventhXiShortThetaLow_mask, golayLabelCoefficients,
    golayBooleanCast]

/-- Complete original upper-half theta coefficients equal the checked table. -/
theorem generatedSeventhXiShortThetaHigh_polynomial (h : Fin 64) :
    sourceCodeThetaPolynomial (Fin.append (0 : Fin 6 → ZMod 2) (generatedSeventhXiShortCodeSix h)) =
      golayLabelCoefficients (generatedSeventhXiShortThetaHigh h) := by
  rw [← generatedSeventhXiShortThetaHigh_code h]
  funext k
  rw [← sourceCodeThetaPolynomial_mask]
  simp only [generatedSeventhXiShortThetaHigh_mask, golayLabelCoefficients,
    golayBooleanCast]

/-- Every actual cross-polar coefficient is retained in the complete binary polynomial. -/
theorem generatedSeventhXiShortThetaCross_polynomial (i : Fin 6) (h : Fin 64) (k : Fin 12) :
    golayLabelCoefficients (generatedSeventhXiShortThetaCross i h) k =
      ∑ j : Fin 6, generatedSeventhXiShortCodeSix h j *
        golayBooleanCast
          ((parkerBasisAssociatorMasks (Fin.castAdd 6 i) (Fin.natAdd 6 j)).testBit k.val) := by
  change golayBooleanCast (((generatedSeventhXiShortThetaCross i h).val).testBit k.val) = _
  rw [← generatedSeventhXiShortThetaCross_mask]
  unfold generatedSeventhXiShortThetaCrossSource
  rw [sourceMaskFold_sum]
  simp only [Nat.zero_testBit, show golayBooleanCast false = 0 from rfl, zero_add,
    List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  apply Finset.sum_congr rfl
  intro j _
  cases hb : h.val.testBit j.val <;>
    simp [generatedSeventhXiShortCodeSix, golayBooleanCast, hb]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
