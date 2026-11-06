/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorXiInverseCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpatialVectorEvaluation

/-! Complete original rational spatial words with four-column Xi and literal permutation pullbacks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Forward original Xi uses precisely its four physical tetrad columns. -/
def generatedAxisGlobalRationalSpatialXi (v : Fin 24 → ℚ) (i : Fin 24) : ℚ :=
  (∑ b : Fin 4, (co1XiNumerator i (generatedAxisGlobalXiColumn i b) : ℚ) *
    v (generatedAxisGlobalXiColumn i b)) / 2

/-- Inverse original Xi uses the four columns of the genuine transposed physical matrix. -/
def generatedAxisGlobalRationalSpatialXiInverse (v : Fin 24 → ℚ) (i : Fin 24) : ℚ :=
  (∑ b : Fin 4, (co1XiNumerator (generatedAxisGlobalXiColumn i b) i : ℚ) *
    v (generatedAxisGlobalXiColumn i b)) / 2

/-- Every complete forward physical Xi coordinate equals the genuine original action. -/
theorem generatedAxisGlobalRationalSpatialXi_actual (v : Fin 24 → ℚ) :
    co1XiIsometry.val (fun i => (v i : ℝ)) =
      fun i => (generatedAxisGlobalRationalSpatialXi v i : ℝ) := by
  funext i
  change (co1XiMatrix *ᵥ (fun j => (v j : ℝ))) i = _
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [generatedAxisGlobalXi_matrix_entry]
  calc
    _ = (∑ j : Fin 24, (co1XiNumerator i j : ℝ) * (v j : ℝ)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [generatedAxisGlobalXi_numerator_row]
      simp [generatedAxisGlobalRationalSpatialXi]

/-- Every complete inverse physical Xi coordinate equals the genuine inverse original action. -/
theorem generatedAxisGlobalRationalSpatialXiInverse_actual (v : Fin 24 → ℚ) :
    (co1XiIsometry⁻¹).val (fun i => (v i : ℝ)) =
      fun i => (generatedAxisGlobalRationalSpatialXiInverse v i : ℝ) := by
  have h := generatedAxisGlobalOddSpatialBaseQ_inverse 0 (fun i => (v i : ℝ))
  change (co1XiIsometry⁻¹).val (fun i => (v i : ℝ)) =
      co1XiMatrixQ.transpose.map (Rat.castHom ℝ) *ᵥ (fun i => (v i : ℝ)) at h
  rw [h]
  funext i
  change (∑ j : Fin 24, (co1XiMatrixQ j i : ℝ) * (v j : ℝ)) = _
  have he (j : Fin 24) : (co1XiMatrixQ j i : ℝ) = (co1XiNumerator j i : ℝ) / 2 := by
    change (((co1XiNumerator j i : ℚ) / 2 : ℚ) : ℝ) = _
    norm_num
  simp_rw [he]
  calc
    _ = (∑ j : Fin 24, (co1XiNumerator j i : ℝ) * (v j : ℝ)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [generatedAxisGlobalXiInverse_numerator_row]
      simp [generatedAxisGlobalRationalSpatialXiInverse]

/-- The original code-basis signs, retaining the full spatial coordinate orientation. -/
def generatedAxisGlobalRationalSpatialBasisSign (j : Fin 12) (v : Fin 24 → ℚ)
    (i : Fin 24) : ℚ :=
  (generatedAxisGlobalIntSign (golayEncoder (Pi.single j 1) i) : ℚ) * v i

/-- Complete sparse physical formulas for all ten original signed source letters. -/
def generatedAxisGlobalRationalSpatialLetterFast (l : Fin 10)
    (v : Fin 24 → ℚ) : Fin 24 → ℚ :=
  ![generatedAxisGlobalRationalSpatialXi v,
    generatedAxisGlobalRationalSpatialXiInverse v,
    generatedAxisGlobalRationalSpatialBasisSign 4 v,
    generatedAxisGlobalRationalSpatialBasisSign 4 v,
    generatedAxisGlobalRationalSpatialBasisSign 5 v,
    generatedAxisGlobalRationalSpatialBasisSign 5 v,
    (fun i => v ((omegaOrbitPermutation 0).symm i)),
    (fun i => v (omegaOrbitPermutation 0 i)),
    (fun i => v ((omegaOrbitPermutation 1).symm i)),
    (fun i => v (omegaOrbitPermutation 1 i))] l

/-- Every sparse rational source-letter formula is its complete genuine physical spatial action. -/
theorem generatedAxisGlobalRationalSpatialLetterFast_actual (l : Fin 10) (v : Fin 24 → ℚ) :
    (generatedAxisGlobalOddSourceSpatialLetter l).val (fun i => (v i : ℝ)) =
      fun i => (generatedAxisGlobalRationalSpatialLetterFast l v i : ℝ) := by
  fin_cases l
  · exact generatedAxisGlobalRationalSpatialXi_actual v
  · exact generatedAxisGlobalRationalSpatialXiInverse_actual v
  · funext i
    change qSign (golayEncoder (Pi.single 4 1) i) * (v i : ℝ) = _
    simp [generatedAxisGlobalRationalSpatialLetterFast,
      generatedAxisGlobalRationalSpatialBasisSign, generatedAxisGlobalIntSign_real]
  · funext i
    change qSign (golayEncoder (Pi.single 4 1) i) * (v i : ℝ) = _
    simp [generatedAxisGlobalRationalSpatialLetterFast,
      generatedAxisGlobalRationalSpatialBasisSign, generatedAxisGlobalIntSign_real]
  · funext i
    change qSign (golayEncoder (Pi.single 5 1) i) * (v i : ℝ) = _
    simp [generatedAxisGlobalRationalSpatialLetterFast,
      generatedAxisGlobalRationalSpatialBasisSign, generatedAxisGlobalIntSign_real]
  · funext i
    change qSign (golayEncoder (Pi.single 5 1) i) * (v i : ℝ) = _
    simp [generatedAxisGlobalRationalSpatialLetterFast,
      generatedAxisGlobalRationalSpatialBasisSign, generatedAxisGlobalIntSign_real]
  · rfl
  · rfl
  · rfl
  · rfl

/-- Exact suffix-first evaluation keeps every original signed source letter. -/
def generatedAxisGlobalRationalSpatialWordFast : List (Fin 10) →
    (Fin 24 → ℚ) → (Fin 24 → ℚ)
  | [], v => v
  | l :: ls, v => generatedAxisGlobalRationalSpatialLetterFast l
      (generatedAxisGlobalRationalSpatialWordFast ls v)

/-- The complete sparse rational word formula is exactly the full genuine original spatial word. -/
theorem generatedAxisGlobalRationalSpatialWordFast_actual (ls : List (Fin 10))
    (v : Fin 24 → ℚ) :
    ((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod).val (fun i => (v i : ℝ)) =
      fun i => (generatedAxisGlobalRationalSpatialWordFast ls v i : ℝ) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    change (generatedAxisGlobalOddSourceSpatialLetter l).val
      (((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod).val
        (fun i => (v i : ℝ))) = _
    rw [ih, generatedAxisGlobalRationalSpatialLetterFast_actual]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
