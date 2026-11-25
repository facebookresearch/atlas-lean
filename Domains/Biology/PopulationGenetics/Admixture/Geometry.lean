/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.FStatistics
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Inner-product geometry of f-statistics

For square-integrable allele-frequency functions, `f2`, `f3`, and `f4` are the squared distance
and inner products of the corresponding frequency classes in `L²`.

This gives the Cauchy–Schwarz bound for `f4`, with equality exactly in the parallel case, and
the strict Thales criterion: `f3(C; A, B) < 0` exactly when the class of `C` lies in the open
ball with diameter `[A, B]`.

## References

* B. M. Peter, "A geometric relationship of F2, F3 and F4-statistics with principal component
  analysis", *Philosophical Transactions of the Royal Society B* 377 (2022), 20200413.
-/

@[expose] public section

open MeasureTheory Metric
open scoped RealInnerProductSpace

/-- Strict Thales criterion in a real inner product space: `⟪c - a, c - b⟫ < 0` iff `c` lies in
the open ball with diameter `[a, b]`. Mathlib-only. -/
theorem inner_sub_sub_neg_iff_mem_ball {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (a b c : F) :
    ⟪c - a, c - b⟫ < 0 ↔ c ∈ ball (midpoint ℝ a b) (dist a b / 2) := by
  set x := c - midpoint ℝ a b with hxdef
  set y := (2⁻¹ : ℝ) • (b - a)
  have hxa : c - a = x + y := by
    simp only [x, y, midpoint_eq_smul_add, invOf_eq_inv]; module
  have hxb : c - b = x - y := by
    simp only [x, y, midpoint_eq_smul_add, invOf_eq_inv]; module
  have hy : ‖y‖ = dist a b / 2 := by
    simp only [y, norm_smul, dist_eq_norm, norm_sub_rev b a, norm_inv, Real.norm_ofNat]; ring
  clear_value x y
  have key : ⟪c - a, c - b⟫ = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
    rw [hxa, hxb, inner_add_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm x y]
    ring
  rw [key, mem_ball, dist_eq_norm c (midpoint ℝ a b), ← hxdef, ← hy, sub_neg]
  exact sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)

namespace MathlibExt.Biology.PopulationGenetics.Admixture

open FStatistics

variable {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}

/-- For square-integrable frequencies, `f4 A B C D = ⟪pA - pB, pC - pD⟫` in `L²(μ)`. -/
theorem f4_eq_inner (hp : ∀ X, MemLp (p X) 2 μ) (A B C D : P) :
    f4 μ p A B C D =
      ⟪(hp A).toLp (p A) - (hp B).toLp (p B), (hp C).toLp (p C) - (hp D).toLp (p D)⟫ := by
  rw [MeasureTheory.L2.inner_def]
  unfold f4
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub ((hp A).toLp (p A)) ((hp B).toLp (p B)),
    Lp.coeFn_sub ((hp C).toLp (p C)) ((hp D).toLp (p D)), (hp A).coeFn_toLp, (hp B).coeFn_toLp,
    (hp C).coeFn_toLp, (hp D).coeFn_toLp] with ω h1 h2 hA hB hC hD
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, hA, hB, hC, hD, RCLike.inner_apply, conj_trivial,
    mul_comm]

/-- For square-integrable frequencies, `f3 C A B = ⟪pC - pA, pC - pB⟫` in `L²(μ)`. -/
theorem f3_eq_inner (hp : ∀ X, MemLp (p X) 2 μ) (C A B : P) :
    f3 μ p C A B =
      ⟪(hp C).toLp (p C) - (hp A).toLp (p A), (hp C).toLp (p C) - (hp B).toLp (p B)⟫ :=
  f4_eq_inner hp C A C B

/-- For square-integrable frequencies, `f2 X Y = ‖pX - pY‖²` in `L²(μ)`. -/
theorem f2_eq_norm_sq (hp : ∀ X, MemLp (p X) 2 μ) (X Y : P) :
    f2 μ p X Y = ‖(hp X).toLp (p X) - (hp Y).toLp (p Y)‖ ^ 2 := by
  rw [f2_eq_f4, f4_eq_inner hp, real_inner_self_eq_norm_sq]

/-- Cauchy–Schwarz for f-statistics of square-integrable frequencies:
`f4(A, B; C, D)² ≤ f2(A, B) f2(C, D)`. -/
theorem sq_f4_le_f2_mul_f2 (hp : ∀ X, MemLp (p X) 2 μ) (A B C D : P) :
    f4 μ p A B C D ^ 2 ≤ f2 μ p A B * f2 μ p C D := by
  rw [f4_eq_inner hp, f2_eq_norm_sq hp, f2_eq_norm_sq hp, ← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2

/-- Equality case of Cauchy–Schwarz, for square-integrable frequencies: `f4² = f2 f2` iff
`pA - pB = 0` in `L²(μ)` or `pC - pD` is a real multiple of `pA - pB` in `L²(μ)`. -/
theorem sq_f4_eq_f2_mul_f2_iff (hp : ∀ X, MemLp (p X) 2 μ) (A B C D : P) :
    f4 μ p A B C D ^ 2 = f2 μ p A B * f2 μ p C D ↔
      (hp A).toLp (p A) - (hp B).toLp (p B) = 0 ∨
        ∃ r : ℝ, (hp C).toLp (p C) - (hp D).toLp (p D) =
          r • ((hp A).toLp (p A) - (hp B).toLp (p B)) := by
  rw [f4_eq_inner hp, f2_eq_norm_sq hp, f2_eq_norm_sq hp, ← mul_pow, ← sq_abs,
    sq_eq_sq₀ (abs_nonneg _) (by positivity), ← Real.norm_eq_abs]
  exact (norm_inner_eq_norm_tfae ℝ _ _).out 1 3

/-- Thales criterion for `f3`, for square-integrable frequencies: `f3(C; A, B) < 0` iff `pC` lies
in the open `L²(μ)` ball whose diameter is the segment `[pA, pB]`. -/
theorem f3_neg_iff_mem_ball (hp : ∀ X, MemLp (p X) 2 μ) (C A B : P) :
    f3 μ p C A B < 0 ↔
      (hp C).toLp (p C) ∈ ball (midpoint ℝ ((hp A).toLp (p A)) ((hp B).toLp (p B)))
        (dist ((hp A).toLp (p A)) ((hp B).toLp (p B)) / 2) := by
  rw [f3_eq_inner hp]
  exact inner_sub_sub_neg_iff_mem_ball _ _ _

end MathlibExt.Biology.PopulationGenetics.Admixture
