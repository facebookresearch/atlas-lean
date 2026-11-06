/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpatialVectorData

/-! Complete original real spatial directions from exact rational source-word evaluation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Suffix-first physical rational source evaluation, with every signed letter retained. -/
def generatedAxisGlobalOddSpatialVectorWordQ : List (Fin 10) →
    (Fin 24 → ℚ) → (Fin 24 → ℚ)
  | [], v => v
  | l :: ls, v => generatedAxisGlobalOddSpatialLetterQ l *ᵥ
      generatedAxisGlobalOddSpatialVectorWordQ ls v

private theorem oddSpatial_cast_mulVec (M : Matrix (Fin 24) (Fin 24) ℚ)
    (v : Fin 24 → ℚ) :
    M.map (Rat.castHom ℝ) *ᵥ (fun i => (v i : ℝ)) =
      fun i => ((M *ᵥ v) i : ℝ) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Rational evaluation is the full actual spatial word action on every rational input vector. -/
theorem generatedAxisGlobalOddSpatialVectorWordQ_actual (ls : List (Fin 10))
    (v : Fin 24 → ℚ) :
    ((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod).val
        (fun i => (v i : ℝ)) =
      fun i => (generatedAxisGlobalOddSpatialVectorWordQ ls v i : ℝ) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    change (generatedAxisGlobalOddSourceSpatialLetter l).val
      (((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod).val
        (fun i => (v i : ℝ))) = _
    rw [ih, generatedAxisGlobalOddSpatialLetterQ_actual, oddSpatial_cast_mulVec]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
