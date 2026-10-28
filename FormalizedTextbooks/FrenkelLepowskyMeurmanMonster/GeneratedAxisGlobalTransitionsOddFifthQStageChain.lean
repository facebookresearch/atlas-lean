/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStageData

/-! Complete genuine original Fifth-frame conjugation from original checked primitive prefixes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Every initial full preferred-section image is the original coordinate generator. -/
theorem generatedAxisGlobalOddFifthQStageInitial (k : Fin 2) (i : Fin 24) :
    generatedAxisGlobalOddFifthQStageCache k 0 i = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ (k : Fin 2) (i j : Fin 24),
        toAdd (generatedAxisGlobalOddFifthQStageCache k 0 i).base j =
          toAdd (qCoordinateGenerator i).base j := by decide +kernel
    exact h k i j
  · apply toAdd.injective
    have h : ∀ (k : Fin 2) (i : Fin 24),
        toAdd (generatedAxisGlobalOddFifthQStageCache k 0 i).coeff =
          toAdd (qCoordinateGenerator i).coeff := by decide +kernel
    exact h k i

/-- The final original prefix and complete Q correction are exactly the original comparison fiber. -/
theorem generatedAxisGlobalOddFifthQStageWord (k : Fin 2) :
    localFiberIncl (generatedAxisGlobalOddFifthComparisonQ k) * generatedAxisGlobalOddFifthQStageFiber k 30 =
      generatedAxisGlobalOddFifthComparisonFiber k := by
  have hxi : generatedAxisGlobalOddSourceFiberLetter (0 : Fin 10) = xiSpinLocalFiber := rfl
  fin_cases k <;>
    norm_num [generatedAxisGlobalOddFifthQStageFiber, generatedAxisGlobalOddFifthQStageLetter,
      generatedAxisGlobalOddFifthComparisonFiber, generatedAxisGlobalOddFifthComparisonPreLetters,
      generatedAxisGlobalOddFifthComparisonPostLetters, generatedAxisGlobalOddFifthComparisonSign,
      hxi, mul_assoc]

/-- All actual original prefixes retain the full central image of each genuine generator. -/
theorem generatedAxisGlobalOddFifthQStage_actual (k : Fin 2) (n : ℕ) (hn : n ≤ 30)
    (i : Fin 24)
    (hstep : ∀ (k : Fin 2) (n : Fin 30) (i : Fin 24),
      generatedAxisGlobalOddFifthQStageCoordinate k n i =
        generatedAxisGlobalOddFifthQStageCache k ⟨n.val+1, by omega⟩ i) :
    spinConjugation (generatedAxisGlobalOddFifthQStageFiber k n).val.1 (qCoordinateGenerator i) =
      generatedAxisGlobalOddFifthQStageCache k ⟨n, by omega⟩ i := by
  induction n with
  | zero =>
    change spinConjugation 1 (qCoordinateGenerator i) = _
    rw [map_one]
    exact (generatedAxisGlobalOddFifthQStageInitial k i).symm
  | succ n ih =>
    have hlt : n < 30 := by omega
    let m : Fin 30 := ⟨n,hlt⟩
    have hp := ih (by omega) hstep
    have hs := hstep k m i
    rw [generatedAxisGlobalOddFifthQStageFiber, dite_eq_left hlt]
    cases h : generatedAxisGlobalOddFifthQStageLetter k m with
    | none =>
      change spinConjugation (generatedAxisGlobalOddFifthQStageFiber k n).val.1
        (qCoordinateGenerator i) = _
      rw [hp]
      simpa only [generatedAxisGlobalOddFifthQStageCoordinate,h] using hs
    | some l =>
      cases l with
      | inl l =>
        change spinConjugation ((generatedAxisGlobalOddSourceFiberLetter l).val.1 *
          (generatedAxisGlobalOddFifthQStageFiber k n).val.1) (qCoordinateGenerator i) = _
        rw [map_mul]
        change spinConjugation (generatedAxisGlobalOddSourceFiberLetter l).val.1
          (spinConjugation (generatedAxisGlobalOddFifthQStageFiber k n).val.1 (qCoordinateGenerator i)) = _
        rw [hp,generatedAxisGlobalOddSourceFastLetter_actual]
        simpa only [generatedAxisGlobalOddFifthQStageCoordinate,h] using hs
      | inr a =>
        change spinConjugation ((generatedFifthSignFiber a 0).val.1 *
          (generatedAxisGlobalOddFifthQStageFiber k n).val.1) (qCoordinateGenerator i) = _
        rw [map_mul]
        change spinConjugation (generatedFifthSignFiber a 0).val.1
          (spinConjugation (generatedAxisGlobalOddFifthQStageFiber k n).val.1 (qCoordinateGenerator i)) = _
        rw [hp,generatedAxisGlobalSignFull_QImage]
        simpa only [generatedAxisGlobalOddFifthQStageCoordinate,h] using hs

/-- The actual full original Q correction gives exactly the final cached complete generator image. -/
theorem generatedAxisGlobalOddFifthQStageFinal (k : Fin 2) (i : Fin 24) :
    generatedAxisGlobalOddFifthComparisonQ k * generatedAxisGlobalOddFifthQStageCache k 30 i *
      (generatedAxisGlobalOddFifthComparisonQ k)⁻¹ = generatedAxisGlobalOddFifthQCache k i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ (k : Fin 2) (i j : Fin 24),
        toAdd (generatedAxisGlobalOddFifthComparisonQ k * generatedAxisGlobalOddFifthQStageCache k 30 i *
          (generatedAxisGlobalOddFifthComparisonQ k)⁻¹).base j =
            toAdd (generatedAxisGlobalOddFifthQCache k i).base j := by decide +kernel
    exact h k i j
  · apply toAdd.injective
    have h : ∀ (k : Fin 2) (i : Fin 24),
        toAdd (generatedAxisGlobalOddFifthComparisonQ k * generatedAxisGlobalOddFifthQStageCache k 30 i *
          (generatedAxisGlobalOddFifthComparisonQ k)⁻¹).coeff =
            toAdd (generatedAxisGlobalOddFifthQCache k i).coeff := by decide +kernel
    exact h k i

/-- Checked genuine primitive stages bind the whole original final comparison generator action. -/
theorem generatedAxisGlobalOddFifthQStageCache_actual (k : Fin 2) (i : Fin 24)
    (hstep : ∀ (k : Fin 2) (n : Fin 30) (i : Fin 24),
      generatedAxisGlobalOddFifthQStageCoordinate k n i =
        generatedAxisGlobalOddFifthQStageCache k ⟨n.val+1, by omega⟩ i) :
    spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1 (qCoordinateGenerator i) =
      generatedAxisGlobalOddFifthQCache k i := by
  rw [← generatedAxisGlobalOddFifthQStageWord]
  change spinConjugation (spinHolomorphIncl (generatedAxisGlobalOddFifthComparisonQ k) *
    (generatedAxisGlobalOddFifthQStageFiber k 30).val.1) (qCoordinateGenerator i) = _
  rw [map_mul]
  change spinConjugation (spinHolomorphIncl (generatedAxisGlobalOddFifthComparisonQ k))
    (spinConjugation (generatedAxisGlobalOddFifthQStageFiber k 30).val.1 (qCoordinateGenerator i)) = _
  rw [spinConjugation_incl, generatedAxisGlobalOddFifthQStage_actual k 30 (by omega) i hstep]
  exact generatedAxisGlobalOddFifthQStageFinal k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
