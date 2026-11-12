/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Saturated-design residuals are almost surely zero

For a square full-rank design (`n = p`), the residual-maker matrix is zero, so the
residual vector and the residual sum of squares have Dirac laws at `0`. No error-law
hypothesis is needed; the source measure only needs to be normalized.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

private theorem matrix_eq_zero_of_rank_eq_zero {m : Type*} [Fintype m]
    {A : Matrix m m ℝ} (h : A.rank = 0) : A = 0 := by
  classical
  have hfin : Module.finrank ℝ ↥A.mulVecLin.range = 0 := h
  have hbot : A.mulVecLin.range = ⊥ := (Submodule.finrank_eq_zero).mp hfin
  have hmap : A.mulVecLin = 0 := (LinearMap.range_eq_bot).mp hbot
  apply Matrix.ext_of_mulVec_single
  intro j
  have hA : A *ᵥ Pi.single j (1 : ℝ) = 0 := by
    have hcongr := LinearMap.congr_fun hmap (Pi.single j (1 : ℝ))
    simpa [Matrix.mulVecLin_apply] using hcongr
  calc A *ᵥ Pi.single j (1 : ℝ) = 0 := hA
    _ = (0 : Matrix m m ℝ) *ᵥ Pi.single j (1 : ℝ) := (Matrix.zero_mulVec _).symm

namespace MathlibExt.Probability.Statistics.LinearModel

open Matrix MeasureTheory ProbabilityTheory

/-- The residual-maker matrix of a square full-rank design is zero: at `n = p` the fit is
exact, so there is no residual. -/
theorem residualMatrix_eq_zero_of_square {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] {X : Matrix m k ℝ}
    (hcard : Fintype.card m = Fintype.card k) (hX : IsUnit (Xᵀ * X)) :
    residualMatrix X = 0 := by
  have hRank : (residualMatrix X).rank = Fintype.card m - Fintype.card k :=
    rank_residualMatrix hX
  rw [hcard, Nat.sub_self] at hRank
  exact matrix_eq_zero_of_rank_eq_zero hRank

/-- **Saturated-design Dirac residual**: at `n = p` the residual vector is almost surely
zero, with no Gaussian hypothesis (pure linear algebra). -/
theorem hasLaw_residual_dirac_of_square {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Matrix m k ℝ}
    (hcard : Fintype.card m = Fintype.card k) (hX : IsUnit (Xᵀ * X))
    (β : k → ℝ) (ε : Ω → m → ℝ) :
    HasLaw (fun ω => X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω))
      (Measure.dirac (0 : m → ℝ)) μ := by
  have hM : residualMatrix X = 0 := residualMatrix_eq_zero_of_square hcard hX
  have hpoint : ∀ ω, X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω) = 0 :=
    fun ω => by rw [sub_mulVec_olsEstimator, hM, Matrix.zero_mulVec]
  exact hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall hpoint)

/-- Companion: at `n = p` the residual sum of squares has Dirac law at `0`, not the
(positive-degree) chi-square law. -/
theorem hasLaw_rss_dirac_of_square {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Matrix m k ℝ}
    (hcard : Fintype.card m = Fintype.card k) (hX : IsUnit (Xᵀ * X))
    (β : k → ℝ) (ε : Ω → m → ℝ) :
    HasLaw (fun ω => (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
        (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)))
      (Measure.dirac (0 : ℝ)) μ := by
  have hM : residualMatrix X = 0 := residualMatrix_eq_zero_of_square hcard hX
  have hres : ∀ ω, X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω) = 0 :=
    fun ω => by rw [sub_mulVec_olsEstimator, hM, Matrix.zero_mulVec]
  have hpoint : ∀ ω, (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
      (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) = 0 :=
    fun ω => by rw [hres ω]; exact zero_dotProduct 0
  exact hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall hpoint)

end MathlibExt.Probability.Statistics.LinearModel
