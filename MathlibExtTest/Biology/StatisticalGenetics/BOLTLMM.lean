/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.BOLTLMM
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

open Matrix MathlibExt.Biology.StatisticalGenetics.BOLTLMM

namespace MathlibExtTest.Biology.StatisticalGenetics.BOLTLMM

/-! ### Non-vacuity witnesses -/

/-- A model on two individuals with identity kinship, `σ_g² = 1`, `σ_e² = 1`. -/
noncomputable def M₂ : Model 2 where
  K := 1
  σg2 := 1
  σe2 := 1
  posSemidef_K := PosSemidef.one
  σg2_nonneg := zero_le_one
  σe2_pos := zero_lt_one

/-- Its marginal covariance is `V = 2 I`. -/
example : M₂.V = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Model.V, M₂]
  simp only [one_smul]
  rw [two_smul]

/-- The boundary `σ_g² = 0` (no genetic component): `V = σ_e² I`, ordinary weighted least
squares. -/
noncomputable def M₀ : Model 2 where
  K := 1
  σg2 := 0
  σe2 := 3
  posSemidef_K := PosSemidef.one
  σg2_nonneg := le_rfl
  σe2_pos := by norm_num

example : M₀.V = (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp [Model.V, M₀]

/-! ### The theorems apply to the witness -/

/-- The design with an intercept column only (`X = 1ₙ`). -/
def X₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

lemma injective_X₁ : Function.Injective X₁.mulVec := by
  intro u v h
  have h0 := congrFun h 0
  simp [X₁, mulVec, dotProduct] at h0
  ext i
  fin_cases i
  simpa using h0

example (y : Fin 2 → ℝ) (β : Fin 1 → ℝ) :
    M₂.logLik y (X₁ *ᵥ β) ≤ M₂.logLik y (X₁ *ᵥ M₂.gls X₁ y) :=
  Model.logLik_le_logLik_gls injective_X₁ y β

example : M₂.proj X₁ * M₂.V * M₂.proj X₁ = M₂.proj X₁ :=
  Model.proj_mul_V_mul_proj injective_X₁

/-- A SNP `(1, -1)` orthogonal to the intercept is not in the column space, so its
information is positive. -/
example : 0 < ![1, -1] ⬝ᵥ (M₂.proj X₁ *ᵥ ![1, -1]) := by
  refine Model.info_pos injective_X₁ ?_
  rintro ⟨β, hβ⟩
  have h0 := congrFun hβ 0
  have h1 := congrFun hβ 1
  simp [X₁, mulVec, dotProduct] at h0 h1
  linarith

/-- Henderson's equations for the witness (identity kinship is positive definite). -/
example (y : Fin 2 → ℝ) :
    M₂.IsMMESolution X₁ y (M₂.gls X₁ y) (M₂.blup X₁ y) :=
  (Model.isMMESolution_iff (M := M₂) PosDef.one zero_lt_one injective_X₁ y _ _).mpr ⟨rfl, rfl⟩

/-! ### Boundary: a SNP in the column space -/

/-- With `X = I` every SNP lies in the column space, so `P x = 0` and the score statistic is the
junk value `0 / 0 = 0` (see `Model.scoreStat`). -/
example (x y : Fin 2 → ℝ) : M₂.scoreStat (1 : Matrix (Fin 2) (Fin 2) ℝ) x y = 0 := by
  have hP : M₂.proj (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    simpa using Model.proj_mul_X (M := M₂) (X := (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (fun u v h => by simpa using h)
  simp [Model.scoreStat, hP]

end MathlibExtTest.Biology.StatisticalGenetics.BOLTLMM
