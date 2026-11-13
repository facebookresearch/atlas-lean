/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesRSIntegralCalculus
import Mathlib.Tactic

namespace MetaMathlibExt.StieltjesRSIntegralCalculusTest

open Set Filter Topology MathlibExt.Analysis.Integration MathlibExt.Analysis.Integration.RSCalculus

/-! ### The hypothesis `hRS` is satisfiable -/

/-- The refinement Riemann–Stieltjes integral written out: the definition of `HasRSIntegral` in
`StieltjesRSIntegral.lean` with `rsSum` unfolded. -/
def RSRef (f h : ℝ → ℝ) (a b I : ℝ) : Prop :=
  ∀ ε > 0, ∃ P : Partition a b, ∀ T : TaggedPartition a b, T.toPartition.IsRefinement P →
    |∑ i : Fin T.n, f (T.tags i) * (h (T.points i.succ) - h (T.points i.castSucc)) - I| < ε

/-- `RSRef` satisfies the hypothesis `hRS` of the calculus file by definition. -/
theorem rsRef_iff (f h : ℝ → ℝ) (a b I : ℝ) : RSRef f h a b I ↔
    ∀ ε > 0, ∃ P : Partition a b, ∀ T : TaggedPartition a b, T.toPartition.IsRefinement P →
      |∑ i : Fin T.n, f (T.tags i) * (h (T.points i.succ) - h (T.points i.castSucc)) - I| < ε :=
  Iff.rfl

/-! ### Integrals computed from the definition -/

/-- The one-subinterval partition of `[a, b]`. -/
def unitPart {a b : ℝ} (hab : a < b) : Partition a b where
  n := 1
  points i := if i = 0 then a else b
  ordered := Fin.strictMono_iff_lt_succ.mpr fun i => by
    rw [Fin.fin_one_eq_zero i]
    simp [hab]
  first := rfl
  last := rfl

/-- From the definition: `∫ₐᵇ c dx = c (b - a)`, since the subinterval lengths telescope. -/
theorem rsRef_const_id (c : ℝ) {a b : ℝ} (hab : a < b) : RSRef (fun _ => c) id a b (c * (b - a)) :=
  fun ε hε => ⟨unitPart hab, fun T _ => by
    simp only [id, ← Finset.mul_sum, T.sum_sub_eq, sub_self, abs_zero]
    exact hε⟩

/-- From the definition: against a constant integrator every sum vanishes. -/
theorem rsRef_id_const (c : ℝ) {a b : ℝ} (hab : a < b) : RSRef id (fun _ => c) a b 0 :=
  fun ε hε => ⟨unitPart hab, fun T _ => by simpa using hε⟩

/-! ### Integration by parts against definition-level values -/

/-- Integration by parts turns `∫₀¹ c dx = c` into `∫₀¹ x d(c) = c·1 - c·0 - c`, and the
definition gives `∫₀¹ x d(c) = 0`: the two values agree. -/
example (c : ℝ) : c * id 1 - c * id 0 - c * (1 - 0) = 0 := by
  have h := hasRS_integration_by_parts RSRef rsRef_iff (rsRef_const_id c zero_lt_one)
  exact eq_of_hasRS RSRef rsRef_iff h (rsRef_id_const c zero_lt_one)

/-- Integration by parts applied twice returns the original value. -/
example (c : ℝ) : RSRef (fun _ => c) id 0 1 (c * (1 - 0)) := by
  have h := hasRS_integration_by_parts RSRef rsRef_iff
    (hasRS_integration_by_parts RSRef rsRef_iff (rsRef_const_id c zero_lt_one))
  convert h using 1
  simp

/-! ### Additivity against definition-level values -/

/-- Gluing `∫₀¹ c dx = c` and `∫₁² c dx = c` gives `2c`, which is the definition-level value
`∫₀² c dx = c (2 - 0)`. -/
example (c : ℝ) : c * (1 - 0) + c * (2 - 1) = c * (2 - 0) :=
  eq_of_hasRS RSRef rsRef_iff
    (hasRS_add_adjacent RSRef rsRef_iff (rsRef_const_id c zero_lt_one)
      (rsRef_const_id c one_lt_two))
    (rsRef_const_id c two_pos)

/-- Splitting `∫₀² c dx` at `1` gives pieces equal to the definition-level values. -/
example (c : ℝ) : ∃ I₁ I₂, RSRef (fun _ => c) id 0 1 I₁ ∧ RSRef (fun _ => c) id 1 2 I₂ ∧
    I₁ = c * (1 - 0) ∧ I₂ = c * (2 - 1) := by
  obtain ⟨I₁, I₂, h₁, h₂, -⟩ :=
    exists_hasRS_split RSRef rsRef_iff (rsRef_const_id c two_pos) zero_le_one one_le_two
  exact ⟨I₁, I₂, h₁, h₂, eq_of_hasRS RSRef rsRef_iff h₁ (rsRef_const_id c zero_lt_one),
    eq_of_hasRS RSRef rsRef_iff h₂ (rsRef_const_id c one_lt_two)⟩

/-! ### Existence: the hypotheses hold for a pure-jump integrator -/

/-- The unit jump at `1`. -/
noncomputable def jump (x : ℝ) : ℝ := if 1 ≤ x then 1 else 0

theorem jump_rightLim (x : ℝ) : ∃ l, Tendsto jump (𝓝[>] x) (𝓝 l) := by
  rcases le_or_gt 1 x with hx | hx
  · refine ⟨1, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [jump, hx.trans (le_of_lt hy)]
  · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hx] with y hy
    simp [jump, not_le.mpr hy.2]

theorem jump_leftLim (x : ℝ) : ∃ l, Tendsto jump (𝓝[<] x) (𝓝 l) := by
  rcases lt_or_ge 1 x with hx | hx
  · refine ⟨1, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hx] with y hy
    simp [jump, le_of_lt hy.1]
  · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [jump, not_le.mpr ((show y < x from hy).trans_le hx)]

/-- `jump` is not continuous within `[0, 2]` at `1`: it is `0` just left of `1` and `1` at `1`. -/
theorem not_continuousWithinAt_jump : ¬ ContinuousWithinAt jump (Icc 0 2) 1 := by
  intro hc
  obtain ⟨δ, hδ, H⟩ := Metric.continuousWithinAt_iff.mp hc (1 / 2) (by norm_num)
  set y := 1 - min (δ / 2) (1 / 2)
  have hm : 0 < min (δ / 2) (1 / 2) := lt_min (half_pos hδ) (by norm_num)
  have hm' : min (δ / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hy : y ∈ Icc (0 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hdist : dist y 1 < δ := by
    rw [Real.dist_eq, show y - 1 = -min (δ / 2) (1 / 2) by ring, abs_neg, abs_of_pos hm]
    linarith [min_le_left (δ / 2) (1 / 2)]
  have := H hy hdist
  simp only [jump, show ¬ (1 : ℝ) ≤ y by linarith, le_refl, ite_true, ite_false] at this
  norm_num at this

/-- Existence of `∫₀² x d(jump)`: `x ↦ x` has bounded variation and is continuous, and `jump` is
regulated. -/
example : ∃ I, RSRef id jump 0 2 I :=
  exists_hasRS_of_boundedVariationOn_of_regulated RSRef rsRef_iff zero_le_two
    (monotoneOn_id.boundedVariationOn (C := 2) fun x hx => by
      rw [id, abs_of_nonneg hx.1]; exact hx.2)
    (fun x _ => jump_rightLim x) (fun x _ => jump_leftLim x)
    (fun _ _ => Or.inl continuous_id.continuousWithinAt)

/-- Existence of `∫₀² jump dx`, the regulated integrand against a monotone integrator. -/
example : ∃ I, RSRef jump id 0 2 I :=
  exists_hasRS_of_regulated_of_monotoneOn RSRef rsRef_iff zero_le_two
    (fun x _ => jump_rightLim x) (fun x _ => jump_leftLim x) monotoneOn_id
    (fun _ _ => Or.inr continuous_id.continuousWithinAt)

/-! ### Boundary: a common jump violates the hypothesis -/

/-- For `f = h = jump` on `[0, 2]` (where the integral does not exist, see the test file of
`StieltjesRSIntegral.lean`), both functions are regulated, and the no-common-discontinuity
hypothesis is exactly what fails, at `1`. -/
example : (∀ x ∈ Ico (0 : ℝ) 2, ∃ l, Tendsto jump (𝓝[>] x) (𝓝 l)) ∧
    (∀ x ∈ Ioc (0 : ℝ) 2, ∃ l, Tendsto jump (𝓝[<] x) (𝓝 l)) ∧
    ¬ (∀ x ∈ Icc (0 : ℝ) 2,
      ContinuousWithinAt jump (Icc 0 2) x ∨ ContinuousWithinAt jump (Icc 0 2) x) :=
  ⟨fun x _ => jump_rightLim x, fun x _ => jump_leftLim x, fun h =>
    (h 1 ⟨zero_le_one, one_le_two⟩).elim not_continuousWithinAt_jump not_continuousWithinAt_jump⟩

end MetaMathlibExt.StieltjesRSIntegralCalculusTest
