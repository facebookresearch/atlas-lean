/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Least-squares fitted values for arbitrary finite designs -/

@[expose] public section

namespace MathlibExt.Probability.Statistics.LinearModel

open LinearMap Module

/-- **Least-squares fitted values are the orthogonal projection onto the column space.**
For any finite real design matrix `X` and response vector `y`, a coefficient minimizes the
Euclidean norm of the residual exactly when its fitted vector is the projection of `y`
onto the range of the matrix. A minimizer exists; relative to any one minimizer `β₀`, the
other minimizers are precisely those with `β - β₀` in the kernel. The coefficient is unique
if and only if the design has full column rank. No invertibility hypothesis is required.
See Rodríguez, *Generalized Linear Models*, §§2.2.1 and 2.9.1, for the full-rank case. -/
theorem least_squares_fitted_projection {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℝ) (y : EuclideanSpace ℝ m) :
    let A := X.toEuclideanLin
    let K := A.range
    let p := K.starProjection y
    let minimizes := fun β => ∀ γ, ‖y - A β‖ ≤ ‖y - A γ‖
    (∀ β, minimizes β ↔ A β = p) ∧
      (∃ β₀, minimizes β₀ ∧ ∀ β, minimizes β ↔ β - β₀ ∈ A.ker) ∧
      ((∃! β, minimizes β) ↔ X.rank = Fintype.card n) := by
  intro A K p minimizes
  have hp : p ∈ K := Submodule.starProjection_apply_mem K y
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀, A β₀ = p := LinearMap.mem_range.mp hp
  have hdist : BddBelow (Set.range fun w : K => ‖y - (w : EuclideanSpace ℝ m)‖) :=
    ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
  have hproj (β : EuclideanSpace ℝ n) : minimizes β ↔ A β = p := by
    constructor
    · intro hβ
      have hmem : A β ∈ K := ⟨β, rfl⟩
      have hmin : ‖y - A β‖ = ⨅ w : K, ‖y - (w : EuclideanSpace ℝ m)‖ := by
        refine le_antisymm (le_ciInf fun w => ?_) (ciInf_le hdist ⟨A β, hmem⟩)
        obtain ⟨γ, hγ⟩ := LinearMap.mem_range.mp w.property
        rw [← hγ]
        exact hβ γ
      exact (K.eq_starProjection_of_mem_of_inner_eq_zero hmem
        ((K.norm_eq_iInf_iff_inner_eq_zero hmem).mp hmin)).symm
    · intro hβ γ
      rw [hβ, show p = K.starProjection y from rfl, Submodule.starProjection_minimal]
      exact ciInf_le hdist ⟨A γ, ⟨γ, rfl⟩⟩
  have hfiber (β₁ : EuclideanSpace ℝ n) (h₁ : minimizes β₁) (β : EuclideanSpace ℝ n) :
      minimizes β ↔ β - β₁ ∈ A.ker := by
    rw [hproj, LinearMap.mem_ker, map_sub, sub_eq_zero, (hproj β₁).mp h₁]
  have hm₀ : minimizes β₀ := (hproj β₀).mpr hβ₀
  refine ⟨hproj, ⟨β₀, hm₀, hfiber β₀ hm₀⟩, ?_⟩
  have hunique : (∃! β, minimizes β) ↔ A.ker = ⊥ := by
    constructor
    · rintro ⟨β, hβ, huniq⟩
      apply bot_unique
      intro z hz
      have hfit : A (β + z) = p := by
        rw [map_add, LinearMap.mem_ker.mp hz, add_zero, (hproj β).mp hβ]
      have heq := huniq (β + z) ((hproj _).mpr hfit)
      have hz0 : z = 0 := add_left_cancel (heq.trans (add_zero β).symm)
      simpa only [Submodule.mem_bot] using hz0
    · intro hker
      refine ⟨β₀, hm₀, fun β hβ => ?_⟩
      have hz := (hfiber β₀ hm₀ β).mp hβ
      rw [hker, Submodule.mem_bot] at hz
      exact sub_eq_zero.mp hz
  have hrank : X.rank = finrank ℝ K := by
    change X.rank = finrank ℝ (X.toEuclideanLin).range
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.rank_eq_finrank_range_toLin X _ _
  have hrn := A.finrank_range_add_finrank_ker
  rw [finrank_euclideanSpace] at hrn
  rw [hunique, hrank]
  constructor
  · intro hker
    rw [hker, finrank_bot, add_zero] at hrn
    exact hrn
  · intro hfull
    apply Submodule.finrank_eq_zero.mp
    change finrank ℝ K = Fintype.card n at hfull
    change finrank ℝ K + finrank ℝ A.ker = Fintype.card n at hrn
    omega

end MathlibExt.Probability.Statistics.LinearModel
