/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceInteger

/-! Exact integral separation of physical rank-one tensor packets under original source actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- An entire physical integer tensor given by its spin and spatial factors. -/
def generatedAxisGlobalOddTensorFactor (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) :
    Fin 4096 → Fin 24 → ℤ := fun k i => u k * v i

/-- The complete 64-term spin numerator of the genuine original three-bases operator. -/
def generatedAxisGlobalOddXiSpinInteger (u : Fin 4096 → ℤ) (k : Fin 4096) : ℤ :=
  ∑ a : XiGrayIndex,
    generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase a (golayLabelCoefficients k)) *
      u (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + xiGrayCode a))

/-- The four-term physical spatial numerator of the identical original three-bases operator. -/
def generatedAxisGlobalOddXiSpatialInteger (v : Fin 24 → ℤ) (i : Fin 24) : ℤ :=
  ∑ b : Fin 4, co1XiNumerator i (generatedAxisGlobalXiColumn i b) *
    v (generatedAxisGlobalXiColumn i b)

/-- Integral separation retains all 64 spin terms and all four physical spatial terms. -/
theorem generatedAxisGlobalOddXiInteger_factor (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) :
    generatedAxisGlobalXiIntegerAction (generatedAxisGlobalOddTensorFactor u v) =
      generatedAxisGlobalOddTensorFactor (generatedAxisGlobalOddXiSpinInteger u)
        (generatedAxisGlobalOddXiSpatialInteger v) := by
  ext k i
  simp only [generatedAxisGlobalXiIntegerAction, generatedAxisGlobalOddTensorFactor,
    generatedAxisGlobalOddXiSpinInteger, generatedAxisGlobalOddXiSpatialInteger]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The literal word's complete signed spin pullback on integer coordinates. -/
def generatedAxisGlobalOddMonomialSpinInteger (w : List (Fin 2 × Bool))
    (u : Fin 4096 → ℤ) (k : Fin 4096) : ℤ :=
  let r := generatedFourthMonomialWordPull w (golayLabelCoefficients k)
  generatedAxisGlobalIntSign r.1 * u (generatedAxisGlobalSpinLabel r.2)

/-- The literal word's original physical spatial coordinate pullback. -/
def generatedAxisGlobalOddMonomialSpatialInteger (w : List (Fin 2 × Bool))
    (v : Fin 24 → ℤ) (i : Fin 24) : ℤ :=
  v (((w.map generatedFourthMonomialPermutationLetter).prod).val.symm i)

/-- Every original permutation word separates with its full genuine quadratic spin phase. -/
theorem generatedAxisGlobalOddMonomialInteger_factor (w : List (Fin 2 × Bool))
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) :
    generatedAxisGlobalMonomialIntegerAction w (generatedAxisGlobalOddTensorFactor u v) =
      generatedAxisGlobalOddTensorFactor (generatedAxisGlobalOddMonomialSpinInteger w u)
        (generatedAxisGlobalOddMonomialSpatialInteger w v) := by
  ext k i
  simp only [generatedAxisGlobalMonomialIntegerAction, generatedAxisGlobalOddTensorFactor,
    generatedAxisGlobalOddMonomialSpinInteger, generatedAxisGlobalOddMonomialSpatialInteger,
    mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
