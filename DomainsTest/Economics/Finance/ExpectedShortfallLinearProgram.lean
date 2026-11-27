/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Finance.ExpectedShortfallLinearProgram
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for the finite expected-shortfall linear program -/

open Set MathlibExt.Probability.Finance.ExpectedShortfall

namespace DomainsTest.ExpectedShortfallLinearProgram

noncomputable section

-- One signed loss. Both its value and a strictly smaller threshold attain the zero-level risk.
example : let cost := thresholdCost (fun _ : Fin 1 => 1) 0 (fun _ => -2)
    let risk := expectedShortfall (fun _ : Fin 1 => 1) 0 (fun _ => -2)
    risk = -2 ∧ cost (-2) = risk ∧ cost (-3) = risk := by
  intro cost risk
  have h := isLeast_range_thresholdCost (p := fun _ : Fin 1 => 1) (fun _ => zero_le_one)
    (by simp) (α := 0) le_rfl zero_lt_one (fun _ => -2)
  obtain ⟨z, hz⟩ := h.1
  have hle := h.2 (mem_range_self (-2))
  have h₁ : cost (-2) = -2 := by norm_num [cost, thresholdCost, liftCost]
  have h₂ : cost (-3) = -2 := by norm_num [cost, thresholdCost, liftCost]
  change cost z = risk at hz
  change risk ≤ cost (-2) at hle
  have hge : -2 ≤ risk := by
    rw [← hz]
    simp only [cost, thresholdCost, liftCost, Fin.sum_univ_one, one_mul, sub_zero, div_one]
    linarith [le_max_left (-2 - z) (0 : ℝ)]
  have heq := le_antisymm (hle.trans_eq h₁) hge
  exact ⟨heq, h₁.trans heq.symm, h₂.trans heq.symm⟩

-- S is the interval [0,1]. Positive-mass losses are x and 1-x; the null scenario loses 100.
private def A : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => ![-1, 1] i
private def b : Fin 2 → ℝ := ![0, 1]
private def C : Matrix (Fin 3) (Fin 1) ℝ := fun i _ => ![1, -1, 0] i
private def d : Fin 3 → ℝ := ![0, 1, 100]
private def p : Fin 3 → ℝ := ![1/2, 1/2, 0]
private def S : Set (Fin 1 → ℝ) := {x | A.mulVec x ≤ b}
private def L (x : Fin 1 → ℝ) := C.mulVec x + d
private abbrev P := feasibleLift S L
private def center : Fin 1 → ℝ := fun _ => 1/2
private def slack : Fin 3 → ℝ := ![0, 0, 100]
private abbrev Point := (Fin 1 → ℝ) × ℝ × (Fin 3 → ℝ)
private def cost (q : Point) := liftCost p (1/2) q.2.1 q.2.2
private def risk (x : Fin 1 → ℝ) := expectedShortfall p (1/2) (L x)

private lemma hp (s : Fin 3) : 0 ≤ p s := by fin_cases s <;> norm_num [p]
private lemma hp1 : ∑ s, p s = 1 := by norm_num [Fin.sum_univ_three, p]

private lemma mem_decisions (x : Fin 1 → ℝ) : x ∈ S ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
  change (∀ i, A.mulVec x i ≤ b i) ↔ _
  simp [Fin.forall_fin_succ, A, b, Matrix.mulVec_apply_eq_sum]

private lemma center_mem : center ∈ S := (mem_decisions _).2 (by norm_num [center])

private lemma loss_values (x : Fin 1 → ℝ) : L x 0 = x 0 ∧ L x 1 = 1 - x 0 ∧ L x 2 = 100 := by
  simp [L, C, d, Matrix.mulVec_apply_eq_sum, sub_eq_add_neg, add_comm]

private lemma cost_eq (q : Point) : cost q = q.2.1 + q.2.2 0 + q.2.2 1 := by
  simp [cost, liftCost, Fin.sum_univ_three, p]
  ring

private lemma center_lift : (center, 1/2, slack) ∈ P := by
  refine ⟨center_mem, fun s => ?_⟩
  obtain ⟨h₀, h₁, h₂⟩ := loss_values center
  fin_cases s <;> norm_num [h₀, h₁, h₂, center, slack]

-- Prove optimality against *arbitrary* feasible triples: cost dominates each of x and 1-x.
private lemma center_optimal : IsMinOn cost P (center, 1/2, slack) := by
  apply isMinOn_iff.mpr
  rintro ⟨x, z, u⟩ ⟨_, hu⟩
  obtain ⟨h₀, h₁, _⟩ := loss_values x
  obtain ⟨hn₀, hl₀⟩ := hu 0
  obtain ⟨hn₁, hl₁⟩ := hu 1
  change L x 0 - z ≤ u 0 at hl₀
  change L x 1 - z ≤ u 1 at hl₁
  rw [h₀] at hl₀
  rw [h₁] at hl₁
  simp only [cost_eq]
  change 1/2 + 0 + 0 ≤ z + u 0 + u 1
  linarith

-- Project the concrete LP optimizer and recover the scalar risk, despite strictly nontight null slack.
example : (center ∈ S ∧ IsMinOn risk S center) ∧ risk center = 1/2 ∧
    max (L center 2 - 1/2) 0 < slack 2 := by
  obtain ⟨_, _, _, project, characterize⟩ := expectedShortfall_linearProgram A b
    ⟨center, center_mem⟩ C d hp hp1 (α := 1/2) (by norm_num) (by norm_num)
  have hmin := (project center).2 ⟨1/2, slack, center_lift, center_optimal⟩
  have hz := ((characterize _ center_lift).1 center_optimal).2.1
  change thresholdCost p (1/2) (L center) (1/2) = risk center at hz
  obtain ⟨h₀, h₁, h₂⟩ := loss_values center
  refine ⟨hmin, ?_, ?_⟩
  · rw [← hz]
    norm_num [thresholdCost, liftCost, p, Fin.sum_univ_three, h₀, h₁, center]
  · norm_num [h₂, slack]

-- Exactly the two positive-mass coordinates must be tight at *every* optimizer.
example (q : Point) (hq : q ∈ P) (hopt : IsMinOn cost P q) :
    q.2.2 0 = max (q.1 0 - q.2.1) 0 ∧ q.2.2 1 = max (1 - q.1 0 - q.2.1) 0 := by
  obtain ⟨_, _, _, _, characterize⟩ := expectedShortfall_linearProgram A b
    ⟨center, center_mem⟩ C d hp hp1 (α := 1/2) (by norm_num) (by norm_num)
  have tight := ((characterize q hq).1 hopt).2.2
  obtain ⟨h₀, h₁, _⟩ := loss_values q.1
  exact ⟨(tight 0 (by norm_num [p])).trans (by rw [← h₀]; rfl),
    (tight 1 (by norm_num [p])).trans (by rw [← h₁]; rfl)⟩

-- An unrestricted decision and a single affine loss x-3: the LP and risk have no real lower bound.
example : let A₀ : Matrix (Fin 0) (Fin 1) ℝ := 0
    let b₀ : Fin 0 → ℝ := 0
    let C₁ : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
    let S₀ := {x | A₀.mulVec x ≤ b₀}
    let L₁ := fun x => C₁.mulVec x + (fun _ => -3)
    lowerBounds ((fun x => expectedShortfall (fun _ => 1) 0 (L₁ x)) '' S₀) = ∅ := by
  intro A₀ b₀ C₁ S₀ L₁
  have mem (x : Fin 1 → ℝ) : x ∈ S₀ := fun i => Fin.elim0 i
  obtain ⟨_, _, bounds, _, _⟩ := expectedShortfall_linearProgram A₀ b₀ ⟨0, mem 0⟩ C₁
    (fun _ => -3) (p := fun _ => 1) (fun _ => zero_le_one) (by simp) (α := 0) le_rfl zero_lt_one
  rw [bounds, eq_empty_iff_forall_notMem]
  intro a ha
  let x : Fin 1 → ℝ := fun _ => a
  have hq : (x, a - 3, fun _ => 0) ∈ feasibleLift S₀ L₁ := by
    refine ⟨mem x, fun i => ⟨le_rfl, ?_⟩⟩
    change C₁.mulVec x i + (-3) - (a - 3) ≤ 0
    rw [Matrix.mulVec_apply_eq_sum]
    simp [C₁, x]
  have hle := ha (mem_image_of_mem _ hq)
  change a ≤ liftCost (fun _ : Fin 1 => 1) 0 (a - 3) (fun _ => 0) at hle
  norm_num [liftCost] at hle

end

end DomainsTest.ExpectedShortfallLinearProgram
