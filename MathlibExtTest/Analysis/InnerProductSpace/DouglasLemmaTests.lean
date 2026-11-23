/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.DouglasLemma

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Douglas' lemma

* On `EuclideanSpace ℂ (Fin 2)`, with `B = diag(1, 0)`, `A = diag(2, 0)` and
  `C = diag(2, 1)`: the factorization `A = B ∘L C` holds, `A.range ≤ B.range`,
  and the canonical factor `douglasFactor A B _` is `A` itself (it lands in
  `(ker B)ᗮ`, unlike the factor `C`). Majorization holds with constant `‖C‖`,
  and majorization produces a factor of norm at most `‖C‖`.
* Failure cases with `A₂ = diag(0, 1)`: `A₂.range ≰ B.range`, so neither a
  factorization nor majorization holds.
* On `ℂ`, with `A = 2 • 1` and `B = 1`: the factorization, the range inclusion
  and the canonical factor.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.DouglasLemmaTests

open MathlibExt.Analysis.InnerProductSpace.DouglasLemma
open scoped InnerProduct

/-- Diagonal operator on `EuclideanSpace ℂ (Fin 2)` with diagonal `d`. -/
noncomputable def diagCLM (d : Fin 2 → ℂ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Matrix.toEuclideanLin (Matrix.diagonal d)).toContinuousLinearMap

/-- Coordinates of a diagonal operator. -/
theorem diagCLM_apply (d : Fin 2 → ℂ) (x : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    diagCLM d x i = d i * x i := by
  simp [diagCLM, Matrix.toEuclideanLin, Matrix.mulVec, Matrix.diagonal_apply]
  fin_cases i <;> simp

/-- `B = diag(1, 0)` on `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def B : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  diagCLM ![1, 0]

/-- `A = diag(2, 0)` on `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def A : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  diagCLM ![2, 0]

/-- `C = diag(2, 1)`: a factor of `A` through `B` that does not land in
`(ker B)ᗮ`. -/
noncomputable def C : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  diagCLM ![2, 1]

/-- `A₂ = diag(0, 1)`: its range is not contained in the range of `B`. -/
noncomputable def A₂ : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  diagCLM ![0, 1]

/-- The factorization `A = B ∘L C`. -/
theorem factorization_example : A = B ∘L C := by
  ext x i
  fin_cases i <;> simp [A, B, C, diagCLM_apply, ContinuousLinearMap.comp_apply]

/-- The range inclusion `A.range ≤ B.range`. -/
theorem range_example : A.range ≤ B.range :=
  (range_le_iff_exists_factorization A B).mpr ⟨C, factorization_example⟩

/-- `A z` is orthogonal to `ker B`: the first coordinate of `u ∈ ker B` is `0`,
while the second coordinate of `A z` is `0`. -/
theorem mem_orthogonal_example (z : EuclideanSpace ℂ (Fin 2)) : A z ∈ B.kerᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hu0 : u 0 = 0 := by
    have h0 : B u = 0 := hu
    have h1 : B u 0 = 0 := by
      have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 0) h0
      simpa [diagCLM_apply, B] using h2
    simpa [diagCLM_apply, B] using h1
  show inner ℂ u (A z) = 0
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two, hu0, diagCLM_apply, A]

/-- The canonical factor for `A` through `B` is `A` itself. -/
theorem canonical_example : douglasFactor A B range_example = A := by
  apply (douglasFactor_eq_of_mem_orthogonal_and_apply A B _ range_example).symm
  intro z
  refine ⟨mem_orthogonal_example z, ?_⟩
  ext i
  fin_cases i <;> simp [diagCLM_apply, A, B]

/-- The canonical factor indeed factors `A` through `B`. -/
theorem eq_comp_example : A = B ∘L douglasFactor A B range_example :=
  eq_comp_douglasFactor A B range_example

/-- Majorization with constant `‖C‖`. -/
theorem majorization_example (y : EuclideanSpace ℂ (Fin 2)) :
    ‖(A†) y‖ ≤ ‖C‖ * ‖(B†) y‖ :=
  majorization_of_factorization A B factorization_example y

/-- Majorization produces a factor of norm at most `‖C‖`. -/
theorem factorization_of_majorization_example :
    ∃ C' : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      A = B ∘L C' ∧ ‖C'‖ ≤ ‖C‖ := by
  obtain ⟨C', hC', hnorm⟩ := exists_factorization_of_majorization A B (norm_nonneg _)
    (fun y => majorization_of_factorization A B factorization_example y)
  exact ⟨C', hC', hnorm⟩

/-- The range of `A₂ = diag(0, 1)` is not contained in the range of `B`,
since `(0, 1)` is in the range of `A₂` but not in the range of `B`. -/
theorem range_failure : ¬ (A₂.range ≤ B.range) := by
  intro h
  have hmem : A₂ (EuclideanSpace.single 1 1) ∈ B.range :=
    h (LinearMap.mem_range_self
      (A₂ : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) _)
  obtain ⟨w, hw⟩ := hmem
  have h1 : B w 1 = A₂ (EuclideanSpace.single 1 1) 1 :=
    congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) hw
  simp [B, A₂, diagCLM_apply] at h1

/-- No factorization of `A₂` through `B`. -/
theorem factorization_failure :
    ¬ ∃ C' : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2), A₂ = B ∘L C' :=
  (range_le_iff_exists_factorization A₂ B).not.mp range_failure

/-- No majorization for `A₂` through `B`. -/
theorem majorization_failure :
    ¬ ∃ c : ℝ, 0 ≤ c ∧ ∀ y : EuclideanSpace ℂ (Fin 2), ‖(A₂†) y‖ ≤ c * ‖(B†) y‖ :=
  (range_le_iff_majorization A₂ B).not.mp range_failure

/-- The scalar case: `A = 2 • 1` on `ℂ`. -/
noncomputable def As : ℂ →L[ℂ] ℂ := (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)

/-- The scalar case: `B = 1` on `ℂ`. -/
noncomputable def Bs : ℂ →L[ℂ] ℂ := 1

/-- Factorization in the scalar case. -/
theorem scalar_factorization : As = Bs ∘L As := by
  apply ContinuousLinearMap.ext
  intro x
  simp [As, Bs]

/-- Range inclusion in the scalar case. -/
theorem scalar_range : As.range ≤ Bs.range :=
  (range_le_iff_exists_factorization As Bs).mpr ⟨As, scalar_factorization⟩

/-- The canonical factor in the scalar case is `As` itself. -/
theorem scalar_canonical : douglasFactor As Bs scalar_range = As := by
  apply (douglasFactor_eq_of_mem_orthogonal_and_apply As Bs _ scalar_range).symm
  intro x
  refine ⟨?_, ?_⟩
  · rw [Submodule.mem_orthogonal]
    intro u hu
    have hu0 : u = 0 := by
      have h0 : (1 : ℂ →L[ℂ] ℂ) u = 0 := hu
      simpa using h0
    rw [hu0]
    simp
  · simp [Bs]

end MathlibExtTest.Analysis.InnerProductSpace.DouglasLemmaTests
