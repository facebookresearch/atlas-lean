/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.QpGraph

@[expose] public section

open Matrix MathlibExt.Biology.PopulationGenetics.QpGraph

namespace MathlibExtTest.Biology.PopulationGenetics.QpGraph

/-! ### Scores on two basis statistics -/

/-- With identity covariance, `S1` is minus half the squared distance. -/
example : scoreS1 (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] ![2, 2] = -1 := by
  simp [scoreS1, dotProduct, Fin.sum_univ_two]
  norm_num

/-- `S2` with `Q = 1` and `λ = 1`. -/
example : scoreS2 (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 ![1, 3] ![2, 2] = -1 := by
  simp [scoreS2, Fin.sum_univ_two]
  norm_num

/-- Boundary (junk value outside the domain): a term with `Qᵢᵢ + λ = 0` contributes `0`. -/
example : scoreS2 (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 ![1, 3] ![2, 2] = 0 := by
  simp [scoreS2]

/-- Basis invariance of `S1` for the shear `A = !![1, 1; 0, 1]`. -/
example (Q : Matrix (Fin 2) (Fin 2) ℝ) (f g : Fin 2 → ℝ) :
    scoreS1 (!![1, 1; 0, 1] * Q * (!![1, 1; 0, 1])ᵀ) (!![1, 1; 0, 1] *ᵥ f)
      (!![1, 1; 0, 1] *ᵥ g) = scoreS1 Q f g :=
  scoreS1_basis_change _ (by simp [det_fin_two_of]) Q f g

/-! ### GLS with one edge length

One edge (`E = Fin 1`) predicts both statistics equally (`B = (1, 1)ᵀ`); with `Q = 1` the GLS
estimate of the edge length from `f = (1, 3)` is the mean `2`. -/

/-- The design matrix of the example. -/
def B : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

theorem normal_B : (Bᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * B) *ᵥ ![2] =
    (Bᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹) *ᵥ ![1, 3] := by
  ext i
  fin_cases i
  simp [B, mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

example (l : Fin 1 → ℝ) : scoreS1 1 ![1, 3] (B *ᵥ l) ≤ scoreS1 1 ![1, 3] (B *ᵥ ![2]) :=
  scoreS1_le_of_normal_eq PosDef.one B _ normal_B l

theorem injective_B : Function.Injective B.mulVec := by
  intro x y h
  have := congrFun h 0
  ext i
  fin_cases i
  simpa [B, mulVec, dotProduct] using this

example (l : Fin 1 → ℝ) (h : scoreS1 1 ![1, 3] (B *ᵥ l) = scoreS1 1 ![1, 3] (B *ᵥ ![2])) :
    l = ![2] :=
  eq_of_scoreS1_eq PosDef.one injective_B _ normal_B h

example : IsUnit (Bᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * B).det :=
  isUnit_det_gram PosDef.one injective_B

/-- `S2` is not basis independent. -/
example : ∃ (Q A : Matrix (Fin 2) (Fin 2) ℝ) (f g : Fin 2 → ℝ), Q.PosDef ∧ IsUnit A.det ∧
    ∀ lam : ℝ, scoreS2 (A * Q * Aᵀ) lam (A *ᵥ f) (A *ᵥ g) ≠ scoreS2 Q lam f g :=
  exists_scoreS2_basis_change_ne

#print axioms scoreS1_basis_change
#print axioms scoreS1_le_of_normal_eq
#print axioms eq_of_scoreS1_eq

end MathlibExtTest.Biology.PopulationGenetics.QpGraph
