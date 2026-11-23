/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.LocalInverseBridge
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for local injectivity from a nonsingular derivative

The smallest nondegenerate case is `x ↦ x + x ^ 3` on `ℝ` at `0`, whose derivative is `1`.
The degenerate map `x ↦ x ^ 2` at `0` is injective on no neighbourhood, so the equivalence
hypothesis cannot be dropped. On the zero-dimensional space every map is injective.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace MathlibExtTest.Analysis.Calculus.LocalInverseBridge

open MathlibExt.Analysis.Calculus.LocalInverseBridge

/-- Smallest nondegenerate dimension: `x ↦ x + x ^ 3` is locally injective at `0`. -/
example : ∃ s ∈ 𝓝 (0 : ℝ), InjOn (fun x : ℝ => x + x ^ 3) s := by
  have h : HasStrictDerivAt (fun x : ℝ => x + x ^ 3) 1 0 := by
    have h0 := (hasStrictDerivAt_id (0 : ℝ)).add (hasStrictDerivAt_pow 3 (0 : ℝ))
    norm_num at h0
    exact h0.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)
  refine exists_mem_nhds_injOn_of_hasStrictFDerivAt (f' := ContinuousLinearEquiv.refl ℝ ℝ) ?_
  convert h.hasStrictFDerivAt using 1
  ext
  simp

/-- Degenerate derivative: `x ↦ x ^ 2` (derivative `0` at `0`) is injective on no
neighbourhood of `0`. -/
example : ¬ ∃ s ∈ 𝓝 (0 : ℝ), InjOn (fun x : ℝ => x ^ 2) s := by
  rintro ⟨s, hs, hinj⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hpos : 0 < ε / 2 := half_pos hε
  have h1 : ε / 2 ∈ s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hpos]
    linarith
  have h2 : -(ε / 2) ∈ s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hpos]
    linarith
  have hEq := hinj h1 h2 (by simp only [neg_sq])
  linarith

/-- Rank-zero space: every map out of the zero-dimensional space is injective. -/
example (f : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) (a : EuclideanSpace ℝ (Fin 0)) :
    ∃ s ∈ 𝓝 a, InjOn f s :=
  ⟨univ, univ_mem, fun x _ y _ _ => Subsingleton.elim x y⟩

#print axioms exists_mem_nhds_injOn_of_hasStrictFDerivAt
#print axioms exists_mem_nhds_injOn_of_contDiffAt

end MathlibExtTest.Analysis.Calculus.LocalInverseBridge
