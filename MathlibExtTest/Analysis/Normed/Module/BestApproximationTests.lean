/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Module.BestApproximation
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

namespace MathlibExt.Analysis.Normed.Module.BestApproximationTests

open MathlibExt.Analysis.Normed.Module.BestApproximation

/-- In `ℝ × ℝ` with the sup norm, every point of the `x`-axis is at distance
at least `1` from `(1, 1)`: the second coordinate already contributes `1`. -/
private theorem one_le_norm_sub_of_mem_span {z : ℝ × ℝ}
    (hz : z ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) :
    1 ≤ ‖(1, 1) - z‖ := by
  rw [Submodule.mem_span_singleton] at hz
  obtain ⟨a, ha⟩ := hz
  have hz2 : z.2 = 0 := by rw [← ha]; simp
  have hpair : (1, 1) - z = (1 - z.1, 1 - z.2) := by ext <;> simp
  rw [hpair, Prod.norm_mk, hz2]
  simp only [sub_zero, norm_one]
  exact le_max_right _ _

/-- Existence: the point `(1, 1)` has a nearest point in the `x`-axis of
`ℝ × ℝ`. -/
example : ∃ y ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)),
    ∀ z ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)),
      ‖(1, 1) - y‖ ≤ ‖(1, 1) - z‖ :=
  exists_bestApproximation_of_finiteDimensional (1, 1)

/-- Existence with the attained value: the nearest point of `(1, 1)` in the
`x`-axis is at distance exactly `1`. -/
example : ∃ y ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)),
    ‖(1, 1) - y‖ = 1 ∧
      ∀ z ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)),
        ‖(1, 1) - y‖ ≤ ‖(1, 1) - z‖ := by
  obtain ⟨y, hyF, hmin⟩ := exists_bestApproximation_of_finiteDimensional (1, 1)
    (F := Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)))
  refine ⟨y, hyF, ?_, hmin⟩
  have hle : ‖(1, 1) - y‖ ≤ 1 := by
    have h := hmin ((0, 0) : ℝ × ℝ)
      (Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))).zero_mem
    simpa using h
  exact le_antisymm hle (one_le_norm_sub_of_mem_span hyF)

/-- Non-uniqueness without strict convexity: in `ℝ × ℝ` with the sup norm,
both `(0, 0)` and `(1, 0)` are nearest to `(1, 1)` in the `x`-axis, so a
best approximation need not be unique. -/
theorem exists_two_distinct_bestApproximations :
    ∃ y₁ y₂ : ℝ × ℝ,
      y₁ ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)) ∧
      y₂ ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)) ∧ y₁ ≠ y₂ ∧
      (∀ z ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)),
        ‖(1, 1) - y₁‖ ≤ ‖(1, 1) - z‖) ∧
      (∀ z ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)),
        ‖(1, 1) - y₂‖ ≤ ‖(1, 1) - z‖) := by
  refine ⟨(0, 0), (1, 0), (Submodule.span ℝ _).zero_mem,
    Submodule.subset_span (Set.mem_singleton _), ?_, ?_, ?_⟩
  · intro h
    exact zero_ne_one (congrArg Prod.fst h)
  · intro z hz
    have h0 : ‖((1, 1) - (0, 0) : ℝ × ℝ)‖ = 1 := by simp [Prod.norm_mk]
    rw [h0]
    exact one_le_norm_sub_of_mem_span hz
  · intro z hz
    have h1 : ‖((1, 1) - (1, 0) : ℝ × ℝ)‖ = 1 := by simp [Prod.norm_mk]
    rw [h1]
    exact one_le_norm_sub_of_mem_span hz

/-- Existence over `ℂ`: the `RCLike` statement also covers complex spaces. -/
example : ∃ y ∈ (⊤ : Submodule ℂ ℂ),
    ∀ z ∈ (⊤ : Submodule ℂ ℂ),
      ‖(2 + 3 * Complex.I) - y‖ ≤ ‖(2 + 3 * Complex.I) - z‖ :=
  exists_bestApproximation_of_finiteDimensional _

/-- Uniqueness: in Euclidean space, two nearest points in the span of the
first basis vector coincide. -/
example (y₁ y₂ : EuclideanSpace ℝ (Fin 2))
    (hy₁ : y₁ ∈ Submodule.span ℝ
      ({EuclideanSpace.single 0 (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 2))))
    (hy₂ : y₂ ∈ Submodule.span ℝ
      ({EuclideanSpace.single 0 (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 2))))
    (h₁ : ∀ z ∈ Submodule.span ℝ
      ({EuclideanSpace.single 0 (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 2))),
      ‖EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) - y₁‖ ≤
        ‖EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) - z‖)
    (h₂ : ∀ z ∈ Submodule.span ℝ
      ({EuclideanSpace.single 0 (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 2))),
      ‖EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) - y₂‖ ≤
        ‖EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) - z‖) :
    y₁ = y₂ :=
  eq_of_isBestApproximation_of_strictConvexSpace (Submodule.convex _) hy₁ hy₂ h₁ h₂

/-- Existence plus uniqueness: the point `e₀ + e₁` in Euclidean space has a
unique nearest point in the span of `e₀`. -/
example : ∃ y ∈ Submodule.span ℝ
      ({EuclideanSpace.single 0 (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 2))),
    (∀ z ∈ Submodule.span ℝ
      ({EuclideanSpace.single 0 (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 2))),
      ‖EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) - y‖ ≤
        ‖EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) - z‖) ∧
    ∀ y' ∈ Submodule.span ℝ
      ({EuclideanSpace.single 0 (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ z ∈ Submodule.span ℝ
        ({EuclideanSpace.single 0 (1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 2))),
        ‖EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) - y'‖ ≤
          ‖EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) - z‖) →
        y' = y :=
  exists_unique_bestApproximation_of_finiteDimensional _

end MathlibExt.Analysis.Normed.Module.BestApproximationTests
