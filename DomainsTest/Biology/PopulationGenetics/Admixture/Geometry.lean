/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Admixture.Geometry

/-!
# Tests for the inner-product geometry of f-statistics

The plane example checks the strict Thales criterion inside, outside, and on the circle. The
remaining examples check the parallel equality case, the degenerate case, and the boundary.
-/

@[expose] public section

open MeasureTheory Metric
open scoped RealInnerProductSpace
open MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.Admixture

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.Geometry

open MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.Admixture

/-- Acceptance 1: Thales on `ℝ²`. With `a = (-1, 0)`, `b = (1, 0)`, the point `(0, 1/2)` is
inside the circle with diameter `[a, b]` and the inner product is negative; `(0, 2)` is outside
and the inner product is positive; `(0, 1)` is on the circle (inner product `0`, not in the
open ball). -/
example :
    let a : EuclideanSpace ℝ (Fin 2) := !₂[-1, 0]
    let b : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
    (⟪!₂[0, 1 / 2] - a, !₂[0, 1 / 2] - b⟫ < 0 ∧ (!₂[0, 1 / 2] : EuclideanSpace ℝ (Fin 2)) ∈
        ball (midpoint ℝ a b) (dist a b / 2)) ∧
      (¬ ⟪!₂[0, 2] - a, !₂[0, 2] - b⟫ < 0 ∧ (!₂[0, 2] : EuclideanSpace ℝ (Fin 2)) ∉
        ball (midpoint ℝ a b) (dist a b / 2)) ∧
      (⟪!₂[0, 1] - a, !₂[0, 1] - b⟫ = 0 ∧ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)) ∉
        ball (midpoint ℝ a b) (dist a b / 2)) := by
  intro a b
  have h1 : ⟪!₂[0, 1 / 2] - a, !₂[0, 1 / 2] - b⟫ = -3 / 4 := by
    simp [a, b, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]; norm_num
  have h2 : ⟪!₂[0, 2] - a, !₂[0, 2] - b⟫ = 3 := by
    simp [a, b, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]; norm_num
  have h3 : ⟪!₂[0, 1] - a, !₂[0, 1] - b⟫ = 0 := by
    simp [a, b, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]
  refine ⟨⟨by rw [h1]; norm_num, (inner_sub_sub_neg_iff_mem_ball a b _).1 (by rw [h1]; norm_num)⟩,
    ⟨by rw [h2]; norm_num, fun h => ?_⟩, ⟨h3, fun h => ?_⟩⟩
  · have := (inner_sub_sub_neg_iff_mem_ball a b _).2 h; rw [h2] at this; norm_num at this
  · have := (inner_sub_sub_neg_iff_mem_ball a b _).2 h; rw [h3] at this; exact lt_irrefl _ this

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {P : Type*} {p : P → Ω → ℝ}

/-- Acceptance 2: equality in Cauchy–Schwarz when `C - D` is parallel to `A - B`
(here `pC - pD = r (pA - pB)` pointwise). -/
example (hp : ∀ X, MemLp (p X) 2 μ) (A B C D : P) (r : ℝ)
    (h : ∀ ω, p C ω - p D ω = r * (p A ω - p B ω)) :
    f4 μ p A B C D ^ 2 = f2 μ p A B * f2 μ p C D := by
  refine (sq_f4_eq_f2_mul_f2_iff hp A B C D).2 (Or.inr ⟨r, ?_⟩)
  refine (Lp.ext_iff).2 ?_
  filter_upwards [Lp.coeFn_sub ((hp C).toLp (p C)) ((hp D).toLp (p D)),
    Lp.coeFn_smul r ((hp A).toLp (p A) - (hp B).toLp (p B)),
    Lp.coeFn_sub ((hp A).toLp (p A)) ((hp B).toLp (p B)), (hp A).coeFn_toLp, (hp B).coeFn_toLp,
    (hp C).coeFn_toLp, (hp D).coeFn_toLp] with ω h1 h2 h3 hA hB hC hD
  rw [h1, h2, Pi.sub_apply, Pi.smul_apply, h3, Pi.sub_apply, hA, hB, hC, hD, h ω, smul_eq_mul]

-- Equality case, degenerate endpoint: `A = B` makes both sides zero.
example (hp : ∀ X, MemLp (p X) 2 μ) (A C D : P) :
    f4 μ p A A C D ^ 2 = f2 μ p A A * f2 μ p C D :=
  (sq_f4_eq_f2_mul_f2_iff hp A A C D).2 (Or.inl (sub_self _))

-- Thales boundary: `C = A` gives `f3 = 0`, so `pA` is not in the open ball.
example (hp : ∀ X, MemLp (p X) 2 μ) (A B : P) :
    (hp A).toLp (p A) ∉ ball (midpoint ℝ ((hp A).toLp (p A)) ((hp B).toLp (p B)))
      (dist ((hp A).toLp (p A)) ((hp B).toLp (p B)) / 2) := by
  rw [← f3_neg_iff_mem_ball hp A A B, f3_eq_inner hp]
  simp

#print axioms inner_sub_sub_neg_iff_mem_ball
#print axioms f4_eq_inner
#print axioms f3_neg_iff_mem_ball
#print axioms sq_f4_eq_f2_mul_f2_iff

end MathlibExtTest.Biology.PopulationGenetics.Admixture.Geometry
