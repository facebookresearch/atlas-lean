/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQStageData

/-! Genuine complete word conjugation from the checked original one-step coordinate tables. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- The initial table is the actual original coordinate generators. -/
theorem generatedAxisGlobalOddFourthQStageInitial (k : Fin 4) (i : Fin 24) :
    generatedAxisGlobalOddFourthQStageCache k 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ k : Fin 4, ∀ i j : Fin 24,
        toAdd (generatedAxisGlobalOddFourthQStageCache k 0 i).base j =
          toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h k i j
  · apply toAdd.injective
    have h : ∀ k : Fin 4, ∀ i : Fin 24,
        toAdd (generatedAxisGlobalOddFourthQStageCache k 0 i).coeff =
          toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h k i

/-- The actual final original fiber is the unchanged source-letter product. -/
theorem generatedAxisGlobalOddFourthQStageWord (k : Fin 4) :
    generatedAxisGlobalOddFourthQStageFiber k 20 =
      ((generatedAxisGlobalOddFourthComparisonLetters k).map
        generatedAxisGlobalOddSourceFiberLetter).prod := by
  fin_cases k <;> rfl

/-- Every intermediate table is genuine conjugation by its full original source prefix. -/
theorem generatedAxisGlobalOddFourthQStage_actual (k : Fin 4) (n : ℕ) (hn : n ≤ 20)
    (i : Fin 24)
    (hstep : ∀ (k : Fin 4) (n : Fin 20) (i : Fin 24),
      generatedAxisGlobalOddFourthQStageCoordinate k n i =
        generatedAxisGlobalOddFourthQStageCache k ⟨n.val + 1, by omega⟩ i) :
    spinConjugation (generatedAxisGlobalOddFourthQStageFiber k n).val.1 (qCoordinateGenerator i) =
      generatedAxisGlobalOddFourthQStageCache k ⟨n, by omega⟩ i := by
  induction n with
  | zero =>
    change spinConjugation 1 (qCoordinateGenerator i) = _
    rw [map_one]
    exact (generatedAxisGlobalOddFourthQStageInitial k i).symm
  | succ n ih =>
    have hlt : n < 20 := by omega
    let m : Fin 20 := ⟨n, hlt⟩
    have hp := ih (by omega) hstep
    have hs := hstep k m i
    rw [generatedAxisGlobalOddFourthQStageFiber, dite_eq_left hlt]
    cases h : generatedAxisGlobalOddFourthQStageLetter k m with
    | none =>
      change spinConjugation (generatedAxisGlobalOddFourthQStageFiber k n).val.1
        (qCoordinateGenerator i) = _
      rw [hp]
      simpa only [generatedAxisGlobalOddFourthQStageCoordinate, h] using hs
    | some l =>
      change spinConjugation ((generatedAxisGlobalOddSourceFiberLetter l).val.1 *
        (generatedAxisGlobalOddFourthQStageFiber k n).val.1) (qCoordinateGenerator i) = _
      rw [map_mul]
      change spinConjugation (generatedAxisGlobalOddSourceFiberLetter l).val.1
        (spinConjugation (generatedAxisGlobalOddFourthQStageFiber k n).val.1
          (qCoordinateGenerator i)) = _
      rw [hp, generatedAxisGlobalOddSourceFastLetter_actual]
      simpa only [generatedAxisGlobalOddFourthQStageCoordinate, h] using hs

/-- The complete original source word is now evaluated once from its genuine final coordinate table. -/
theorem generatedAxisGlobalOddFourthQStageWord_generator (k : Fin 4) (i : Fin 24)
    (hstep : ∀ (k : Fin 4) (n : Fin 20) (i : Fin 24),
      generatedAxisGlobalOddFourthQStageCoordinate k n i =
        generatedAxisGlobalOddFourthQStageCache k ⟨n.val + 1, by omega⟩ i) :
    generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddFourthComparisonLetters k)
      (qCoordinateGenerator i) = generatedAxisGlobalOddFourthQStageCache k 20 i := by
  have hi := generatedAxisGlobalOddFourthQStage_actual k 20 (by decide) i hstep
  rw [generatedAxisGlobalOddFourthQStageWord] at hi
  rw [← generatedAxisGlobalOddSourceFastWord_actual]
  exact hi

/-- The genuine extraspecial correction gives exactly the final cached full coordinate images. -/
theorem generatedAxisGlobalOddFourthQStageFinal (k : Fin 4) (i : Fin 24) :
    generatedAxisGlobalOddFourthComparisonQ k * generatedAxisGlobalOddFourthQStageCache k 20 i *
      (generatedAxisGlobalOddFourthComparisonQ k)⁻¹ = generatedAxisGlobalOddFourthQCache k i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ k : Fin 4, ∀ i j : Fin 24,
        toAdd (generatedAxisGlobalOddFourthComparisonQ k * generatedAxisGlobalOddFourthQStageCache k 20 i *
          (generatedAxisGlobalOddFourthComparisonQ k)⁻¹).base j =
            toAdd (generatedAxisGlobalOddFourthQCache k i).base j := by decide +kernel
    exact h k i j
  · apply toAdd.injective
    have h : ∀ k : Fin 4, ∀ i : Fin 24,
        toAdd (generatedAxisGlobalOddFourthComparisonQ k * generatedAxisGlobalOddFourthQStageCache k 20 i *
          (generatedAxisGlobalOddFourthComparisonQ k)⁻¹).coeff =
            toAdd (generatedAxisGlobalOddFourthQCache k i).coeff := by decide +kernel
    exact h k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
