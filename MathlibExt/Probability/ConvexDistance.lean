/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Talagrand's convex distance

For a subset `A` of a product `Ω^N` and a point `x ∈ Ω^N`, Talagrand (1995) measures how far
`x` is from `A` through the set
`U_A(x) = {s ∈ {0, 1}^N : ∃ y ∈ A, s_i = 0 ⇒ y_i = x_i}`
of the coordinate patterns along which `x` can be moved into `A`, its convex hull `V_A(x)` in
`ℝ^N`, and the Euclidean distance `f_c(A, x)` from `0` to `V_A(x)`. The point `x` lies in `A`
exactly when `0 ∈ U_A(x)`, and `f_c(A, x)` is at most the square root of the Hamming distance
from `x` to any point of `A`. Talagrand's convex-distance inequality
(`MathlibExt.Probability.ConvexDistanceInequality`) bounds `∫ exp(f_c(A, ·)² / 4) dP ≤ 1 / P(A)`
for every product probability `P`.

When `A` is empty, `U_A(x)` is empty and `Metric.infDist` returns `0`, whereas the source's
distance to an empty set is `+∞`; the inequality is unaffected (its right-hand side is then `+∞`).

## References

* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205, Section 4.1 (definitions before Theorem 4.1.1).
-/

@[expose] public section

namespace MathlibExt.Probability.ConvexDistance

open Metric

variable {Ω : Type*} {N : ℕ}

/-- **Talagrand's set `U_A(x)`** (Talagrand, *Concentration of measure and isoperimetric
inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Section 4.1). For `A ⊆ Ω^N` and
`x ∈ Ω^N`, `U_A(x)` is the set of `s ∈ {0, 1}^N ⊆ ℝ^N` for which some `y ∈ A` agrees with `x`
on every coordinate where `s` vanishes. -/
def convexSupport (A : Set (Fin N → Ω)) (x : Fin N → Ω) : Set (EuclideanSpace ℝ (Fin N)) :=
  {s | ∃ y ∈ A, (∀ i, s i = 0 ∨ s i = 1) ∧ ∀ i, s i = 0 → y i = x i}

/-- **Talagrand's convex distance** (Talagrand, *Concentration of measure and isoperimetric
inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Section 4.1). `f_c(A, x)` is the
Euclidean distance from `0` to the convex hull `V_A(x)` of `U_A(x)` in `ℝ^N`. -/
noncomputable def convexDistance (A : Set (Fin N → Ω)) (x : Fin N → Ω) : ℝ :=
  infDist (0 : EuclideanSpace ℝ (Fin N)) (convexHull ℝ (convexSupport A x))

theorem convexDistance_nonneg (A : Set (Fin N → Ω)) (x : Fin N → Ω) : 0 ≤ convexDistance A x :=
  infDist_nonneg

/-- **Points of `A` are at convex distance zero** (Talagrand, *Concentration of measure and
isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Section 4.1: "`V_A(x)`
contains zero if and only if `x` belongs to `A`", the direction from `x ∈ A`). -/
theorem convexDistance_eq_zero_of_mem {A : Set (Fin N → Ω)} {x : Fin N → Ω} (hx : x ∈ A) :
    convexDistance A x = 0 := by
  have h0 : (0 : EuclideanSpace ℝ (Fin N)) ∈ convexSupport A x :=
    ⟨x, hx, fun _ => Or.inl rfl, fun _ _ => rfl⟩
  exact infDist_zero_of_mem (subset_convexHull ℝ _ h0)

theorem convexSupport_nonempty {A : Set (Fin N → Ω)} (hA : A.Nonempty) (x : Fin N → Ω) :
    (convexSupport A x).Nonempty := by
  classical
  obtain ⟨y, hy⟩ := hA
  refine ⟨WithLp.toLp 2 fun i => if x i ≠ y i then 1 else 0, y, hy, fun i => ?_, fun i hi => ?_⟩
  · by_cases h : x i ≠ y i <;> simp [h]
  · by_cases h : x i ≠ y i
    · simp [h] at hi
    · exact (not_not.mp h).symm

/-- **The convex distance decreases as the set grows.** For sets `A ⊆ B ⊆ Ω^N` with `A` nonempty
and every `x ∈ Ω^N`, `f_c(B, x) ≤ f_c(A, x)`, since `U_A(x) ⊆ U_B(x)`. Nonemptiness of `A` is
needed: `f_c(∅, x) = 0` by the convention of `Metric.infDist`. -/
theorem convexDistance_le_convexDistance_of_subset {A B : Set (Fin N → Ω)} (hAB : A ⊆ B)
    (hA : A.Nonempty) (x : Fin N → Ω) : convexDistance B x ≤ convexDistance A x :=
  infDist_le_infDist_of_subset (convexHull_mono fun _ ⟨y, hy, hs⟩ => ⟨y, hAB hy, hs⟩)
    ((convexSupport_nonempty hA x).mono (subset_convexHull ℝ _))

open Classical in
/-- **The convex distance is at most the square root of the Hamming distance** (Talagrand,
*Concentration of measure and isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81
(1995), Section 4.1; compare Lemma 4.1.2 with all `α_i = 1`). For every `y ∈ A`,
`f_c(A, x) ≤ √(card {i : x_i ≠ y_i})`: the indicator of `{i : x_i ≠ y_i}` lies in `U_A(x)`. -/
theorem convexDistance_le_sqrt_card {A : Set (Fin N → Ω)} {x y : Fin N → Ω} (hy : y ∈ A) :
    convexDistance A x ≤ Real.sqrt ((Finset.univ.filter fun i => x i ≠ y i).card) := by
  classical
  set s : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun i => if x i ≠ y i then 1 else 0
  have hs : s ∈ convexSupport A x := by
    refine ⟨y, hy, fun i => ?_, fun i hi => ?_⟩
    · by_cases h : x i ≠ y i <;> simp [s, h]
    · by_cases h : x i ≠ y i
      · simp [s, h] at hi
      · exact (not_not.mp h).symm
  calc convexDistance A x ≤ dist (0 : EuclideanSpace ℝ (Fin N)) s :=
        infDist_le_dist_of_mem (subset_convexHull ℝ _ hs)
    _ = ‖s‖ := by rw [dist_comm, dist_zero_right]
    _ = Real.sqrt ((Finset.univ.filter fun i => x i ≠ y i).card) := by
        rw [EuclideanSpace.norm_eq]
        congr 1
        simp only [s, Real.norm_eq_abs, sq_abs]
        rw [Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : x i ≠ y i <;> simp [h]

end MathlibExt.Probability.ConvexDistance
