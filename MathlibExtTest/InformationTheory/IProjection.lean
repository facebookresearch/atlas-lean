/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.IProjection
public import MathlibExt.InformationTheory.LogSum

open MathlibExt.InformationTheory.IProjection Finset Real

/-- Joint satisfiability: on `Bool`, `Γ` = all probability vectors (convex), `Q` uniform; by
Gibbs' inequality `Q` itself is the I-projection, and the theorem applies to every `P ∈ Γ`. -/
example (P : Bool → ℝ) (hP : (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1) :
    ∑ a, P a * log (P a / (1 / 2)) + ∑ _a : Bool, (1 / 2 : ℝ) * log ((1 / 2) / (1 / 2)) ≤
      ∑ a, P a * log (P a / (1 / 2)) := by
  have hconv : Convex ℝ {R : Bool → ℝ | (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1} := by
    intro x hx y hy s t hs ht hst
    refine ⟨fun a => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hx.1 a; have := hy.1 a; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx.2, hy.2, mul_one, hst]
  have hgibbs : ∀ R ∈ {R : Bool → ℝ | (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1},
      ∑ _a : Bool, (1 / 2 : ℝ) * log ((1 / 2) / (1 / 2)) ≤ ∑ a, R a * log (R a / (1 / 2)) := by
    intro R hR
    have h := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div univ R (fun _ => (1 / 2 : ℝ))
      (fun i _ => hR.1 i) (fun _ _ => by norm_num)
    have hq : ∑ _a : Bool, (1 / 2 : ℝ) = 1 := by norm_num
    rw [hR.2, hq, div_one, log_one, mul_zero] at h
    simpa using h
  have hQmem : (fun _ : Bool => (1 / 2 : ℝ)) ∈
      {R : Bool → ℝ | (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1} :=
    ⟨fun _ => by norm_num, by norm_num⟩
  exact (support_and_pythagorean (Q := fun _ : Bool => (1 / 2 : ℝ)) (fun _ => by norm_num)
    hconv (fun R hR => hR) hQmem hgibbs hP).2

/-- The tangent-line inequality at a concrete point: `x = 0`, `y = 1`. -/
example : (1 : ℝ) * log 1 - 0 * log 0 ≤ (1 - 0) * (log 1 + 1) :=
  mul_log_sub_mul_log_le le_rfl one_pos

/-- Existence of an I-projection, on the closed set of all probability vectors on `Bool`. -/
example : ∃ Ps ∈ {R : Bool → ℝ | (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1},
    ∀ P ∈ {R : Bool → ℝ | (∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1},
      ∑ a, Ps a * log (Ps a / (1 / 2)) ≤ ∑ a, P a * log (P a / (1 / 2)) := by
  refine exists_isMinOn (fun _ => by norm_num) ⟨fun _ => 1 / 2, fun _ => by norm_num, by norm_num⟩
    ?_ fun R hR => hR
  have h1 : IsClosed {R : Bool → ℝ | ∀ a, 0 ≤ R a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a)
  have h2 : IsClosed {R : Bool → ℝ | ∑ a, R a = 1} :=
    isClosed_eq (continuous_finsetSum _ fun a _ => continuous_apply a) continuous_const
  exact h1.inter h2

/-- The linear-family identity is non-vacuous: on `Bool`, the family `{P : P(true) = 1/2}` with the
uniform `Q`, whose I-projection is `Q` itself (Gibbs' inequality). -/
example (P : Bool → ℝ)
    (hP : P ∈ {R : Bool → ℝ | ((∀ a, 0 ≤ R a) ∧ ∑ a, R a = 1) ∧
      ∀ _i : Unit, ∑ a, R a * (if a then (1 : ℝ) else 0) = 1 / 2}) :
    ∑ a, P a * log (P a / (1 / 2)) =
      ∑ a, P a * log (P a / (1 / 2)) + ∑ _a : Bool, (1 / 2 : ℝ) * log ((1 / 2) / (1 / 2)) := by
  refine pythagorean_eq_linearFamily (Q := fun _ : Bool => (1 / 2 : ℝ)) (fun _ => by norm_num)
    (fun (_ : Unit) a => if a then (1 : ℝ) else 0) (fun _ => 1 / 2)
    ⟨⟨fun _ => by norm_num, by norm_num⟩, fun _ => by norm_num⟩ (fun R hR => ?_) hP
  have h := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div univ R (fun _ => (1 / 2 : ℝ))
    (fun i _ => hR.1.1 i) (fun _ _ => by norm_num)
  have hq : ∑ _a : Bool, (1 / 2 : ℝ) = 1 := by norm_num
  rw [hR.1.2, hq, div_one, log_one, mul_zero] at h
  simpa using h
