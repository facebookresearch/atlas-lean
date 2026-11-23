/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.DCFlowNetworkBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Fixtures for the grounded DC load-flow solve: a three-bus radial network on
which every hypothesis holds and the solve has nonzero angles; networks that
violate connectivity, positivity, or balance, on which the conclusion fails;
and a two-bus line at zero, small, and large angle.
-/

@[expose] public section

namespace PhyslibExtTest.Circuits.DCFlowNetworkBridge

open Matrix
open MathlibExt.Combinatorics.Graph.ArcNetwork
open PhyslibExt.Circuits.ArcPortSigns
open PhyslibExt.Circuits.LosslessDCFlowModel
open PhyslibExt.Circuits.DCFlowNetworkBridge
open MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian (positiveArcGraph)

/-! ## Three-bus radial network: arcs `0 → 1` (`b = 1`), `1 → 2` (`b = 2`), reference `0` -/

/-- Branch tails of the radial network. -/
def tail3 : Fin 2 → Fin 3 := ![0, 1]

/-- Branch heads of the radial network. -/
def head3 : Fin 2 → Fin 3 := ![1, 2]

/-- Branch susceptances of the radial network. -/
noncomputable def b3 : Fin 2 → ℝ := ![1, 2]

/-- Balanced injections: `1/10` in at bus `0`, out at bus `2`. -/
noncomputable def p3 : Fin 3 → ℝ := ![1 / 10, 0, -1 / 10]

/-- The grounded solution of the radial network. -/
noncomputable def θ3 : Fin 3 → ℝ := ![0, -1 / 10, -3 / 20]

lemma L3_mulVec (θ : Fin 3 → ℝ) :
    weightedLaplacian 3 2 tail3 head3 b3 *ᵥ θ =
      ![θ 0 - θ 1, -(θ 0 - θ 1) + 2 * (θ 1 - θ 2), -(2 * (θ 1 - θ 2))] := by
  ext v
  fin_cases v <;>
  simp [weightedLaplacian, electricalIncidence, incidenceMatrix, mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_succ, tail3, head3, b3, diagonal] <;> ring

/-- Hypothesis `hb` holds. -/
lemma b3_pos : ∀ e, 0 < b3 e := by
  intro e; fin_cases e <;> simp [b3]

/-- Hypothesis `hconn` holds. -/
lemma conn3 : (positiveArcGraph tail3 head3 (fun _ => (1 : ℝ))).Connected := by
  have h01 : (positiveArcGraph tail3 head3 (fun _ => (1 : ℝ))).Adj 0 1 := by
    simp only [positiveArcGraph, SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inl ⟨0, one_pos, rfl, rfl⟩⟩
  have h12 : (positiveArcGraph tail3 head3 (fun _ => (1 : ℝ))).Adj 1 2 := by
    simp only [positiveArcGraph, SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inl ⟨1, one_pos, rfl, rfl⟩⟩
  have hr : ∀ v, (positiveArcGraph tail3 head3 (fun _ => (1 : ℝ))).Reachable 0 v := by
    intro v
    fin_cases v
    · rfl
    · exact h01.reachable
    · exact h01.reachable.trans h12.reachable
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

/-- Hypothesis `hp` holds with nonzero injections. -/
example : ∑ v, p3 v = 0 ∧ p3 ≠ 0 := by
  refine ⟨by simp [p3, Fin.sum_univ_succ]; norm_num, fun h => ?_⟩
  have := congrFun h 0
  simp [p3] at this

lemma θ3_solves : weightedLaplacian 3 2 tail3 head3 b3 *ᵥ θ3 = p3 := by
  rw [L3_mulVec]; ext v; fin_cases v <;> simp [θ3, p3] <;> norm_num

/-- The constructive grounded solve returns `θ3`, which has nonzero angles. -/
example : groundedAngles 3 2 tail3 head3 b3 0 p3 = θ3 ∧ θ3 ≠ 0 := by
  refine ⟨(eq_groundedAngles 3 2 tail3 head3 b3 b3_pos 0 conn3 p3 θ3 (by simp [θ3])
    θ3_solves).symm, fun h => ?_⟩
  have := congrFun h 1; simp [θ3] at this

/-- The headline's unique solution is `θ3`. -/
example : ∀ θ : Fin 3 → ℝ, θ 0 = 0 ∧ weightedLaplacian 3 2 tail3 head3 b3 *ᵥ θ = p3 →
    θ = θ3 := by
  obtain ⟨⟨_, _, huniq⟩, -⟩ := l2_correct 3 2 tail3 head3 b3 b3_pos 0 conn3 p3
    (by simp [p3, Fin.sum_univ_succ]; norm_num)
  intro θ hθ
  exact (huniq θ hθ).trans (huniq θ3 ⟨by simp [θ3], θ3_solves⟩).symm

/-- Its flows: `f₀₁ = 1/10`, `f₁₂ = 1/10`, the injection transported along the path. -/
example : dcBranchFlow 3 2 tail3 head3 b3 θ3 = ![1 / 10, 1 / 10] := by
  ext e
  fin_cases e <;> simp [dcBranchFlow_apply, tail3, head3, b3, θ3] <;> norm_num

/-- Shifting by a constant keeps `L θ = p` but breaks `θ ref = 0`: the grounding clause is
what pins the solution. -/
example : weightedLaplacian 3 2 tail3 head3 b3 *ᵥ (fun v => θ3 v + 1) = p3 ∧
    (fun v => θ3 v + 1) (0 : Fin 3) ≠ 0 := by
  refine ⟨?_, by simp [θ3]⟩
  rw [L3_mulVec]; ext v; fin_cases v <;> simp [θ3, p3] <;> norm_num

/-! ## Violated hypotheses: each falsifies the unique-solve conclusion -/

/-- Disconnected network (two buses, no branch): `L = 0`, so with `p = 0` both `0` and
`![0, 1]` are grounded solutions. Uniqueness fails. -/
example : ¬ ∃! θ : Fin 2 → ℝ, θ 0 = 0 ∧
    weightedLaplacian 2 0 Fin.elim0 Fin.elim0 Fin.elim0 *ᵥ θ = 0 := by
  rintro ⟨θ, -, huniq⟩
  have hL : ∀ x : Fin 2 → ℝ, weightedLaplacian 2 0 Fin.elim0 Fin.elim0 Fin.elim0 *ᵥ x = 0 := by
    intro x; ext v
    simp [weightedLaplacian, mulVec, dotProduct, Matrix.mul_apply]
  have h0 := huniq 0 ⟨rfl, hL 0⟩
  have h1 := huniq ![0, 1] ⟨rfl, hL _⟩
  have := congrFun (h1.trans h0.symm) 1
  simp at this

/-- Zero susceptance on the only branch (connected graph, `hb` violated): `L = 0` again,
so uniqueness fails. -/
example : ¬ ∃! θ : Fin 2 → ℝ, θ 0 = 0 ∧
    weightedLaplacian 2 1 ![0] ![1] ![0] *ᵥ θ = 0 := by
  rintro ⟨θ, -, huniq⟩
  have hL : ∀ x : Fin 2 → ℝ, weightedLaplacian 2 1 ![0] ![1] ![0] *ᵥ x = 0 := by
    intro x; ext v
    simp [weightedLaplacian, mulVec, dotProduct, Matrix.mul_apply, diagonal]
  have h0 := huniq 0 ⟨rfl, hL 0⟩
  have h1 := huniq ![0, 1] ⟨rfl, hL _⟩
  have := congrFun (h1.trans h0.symm) 1
  simp at this

/-- Unbalanced injection on the connected two-bus network with `b = 1`: no angle vector
solves `L θ = p`. Existence fails. -/
example : ¬ ∃ θ : Fin 2 → ℝ, weightedLaplacian 2 1 ![0] ![1] ![1] *ᵥ θ = ![1, 0] := by
  rintro ⟨θ, hθ⟩
  have e0 := congrFun hθ 0
  have e1 := congrFun hθ 1
  simp [weightedLaplacian, electricalIncidence, incidenceMatrix, mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_succ, diagonal] at e0 e1
  linarith

/-- On the disconnected network the reduced matrix is the `1 × 1` zero matrix, Mathlib's `⁻¹`
returns `0`, and `groundedAngles` returns the zero vector whatever `p` is, so for
`p = ![1, -1]` it does not solve the system: the construction is not trivially a solution. -/
example : weightedLaplacian 2 0 Fin.elim0 Fin.elim0 Fin.elim0 *ᵥ
    groundedAngles 2 0 Fin.elim0 Fin.elim0 Fin.elim0 0 ![1, -1] ≠ ![1, -1] := by
  intro h
  have := congrFun h 0
  simp [weightedLaplacian, mulVec, dotProduct, Matrix.mul_apply] at this

/-! ## Two-bus line: one branch `0 → 1`, `b = 1`, reference `0` -/

/-- Branch tail of the two-bus line. -/
def t2 : Fin 1 → Fin 2 := ![0]

/-- Branch head of the two-bus line. -/
def h2 : Fin 1 → Fin 2 := ![1]

/-- Branch susceptance of the two-bus line. -/
noncomputable def b2 : Fin 1 → ℝ := ![1]

lemma b2_pos : ∀ e, 0 < b2 e := by intro e; fin_cases e; simp [b2]

lemma conn2 : (positiveArcGraph t2 h2 (fun _ => (1 : ℝ))).Connected := by
  have h01 : (positiveArcGraph t2 h2 (fun _ => (1 : ℝ))).Adj 0 1 := by
    simp only [positiveArcGraph, SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inl ⟨0, one_pos, rfl, rfl⟩⟩
  have hr : ∀ v, (positiveArcGraph t2 h2 (fun _ => (1 : ℝ))).Reachable 0 v := by
    intro v; fin_cases v
    · rfl
    · exact h01.reachable
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma L2_mulVec (θ : Fin 2 → ℝ) :
    weightedLaplacian 2 1 t2 h2 b2 *ᵥ θ = ![θ 0 - θ 1, -(θ 0 - θ 1)] := by
  ext v; fin_cases v <;>
  simp [weightedLaplacian, electricalIncidence, incidenceMatrix, mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_succ, t2, h2, b2, diagonal] <;> ring

/-- The grounded solution for injection `![s, -s]` is `![0, -s]`. -/
lemma grounded2 (s : ℝ) : groundedAngles 2 1 t2 h2 b2 0 ![s, -s] = ![0, -s] := by
  refine (eq_groundedAngles 2 1 t2 h2 b2 b2_pos 0 conn2 _ _ (by simp) ?_).symm
  rw [L2_mulVec]; ext v; fin_cases v <;> simp

/-- Zero angle: zero injection gives zero angles, and AC power equals DC flow. -/
example : groundedAngles 2 1 t2 h2 b2 0 ![0, -0] = 0 ∧
    acBranchRealPower 2 1 t2 h2 b2 (groundedAngles 2 1 t2 h2 b2 0 ![0, -0]) 0 =
      dcBranchFlow 2 1 t2 h2 b2 (groundedAngles 2 1 t2 h2 b2 0 ![0, -0]) 0 := by
  rw [grounded2]
  refine ⟨by ext v; fin_cases v <;> simp, ?_⟩
  rw [acBranchRealPower_eq_mul_sin, dcBranchFlow_apply]
  simp [t2, h2, b2]

/-- Small angle: injection `1/10` gives DC flow `1/10`, and the headline bound on the AC
sending-end power is `(1/10)^3/6 = 1/6000`. -/
example : dcBranchFlow 2 1 t2 h2 b2 (groundedAngles 2 1 t2 h2 b2 0 ![1 / 10, -(1 / 10)]) 0 =
      1 / 10 ∧
    |acBranchRealPower 2 1 t2 h2 b2 (groundedAngles 2 1 t2 h2 b2 0 ![1 / 10, -(1 / 10)]) 0 -
        1 / 10| ≤ 1 / 6000 := by
  have hl := (l2_correct 2 1 t2 h2 b2 b2_pos 0 conn2 ![1 / 10, -(1 / 10)] (by simp)).2.2.2.2.2.2 0
  have hf : dcBranchFlow 2 1 t2 h2 b2 (groundedAngles 2 1 t2 h2 b2 0 ![1 / 10, -(1 / 10)]) 0 =
      1 / 10 := by
    rw [grounded2, dcBranchFlow_apply]; simp [t2, h2, b2]
  refine ⟨hf, ?_⟩
  rw [hf, grounded2] at hl
  rw [grounded2]
  simp only [t2, h2, b2] at hl ⊢
  norm_num at hl ⊢
  exact hl

/-- Large angle: injection `π` gives AC power `sin π = 0` and DC flow `π`. The absolute bound
still holds, but the relative error is 100%, so no relative-error claim is made. -/
example : acBranchRealPower 2 1 t2 h2 b2 (groundedAngles 2 1 t2 h2 b2 0 ![Real.pi, -Real.pi]) 0
      = 0 ∧
    dcBranchFlow 2 1 t2 h2 b2 (groundedAngles 2 1 t2 h2 b2 0 ![Real.pi, -Real.pi]) 0 =
      Real.pi := by
  rw [grounded2, acBranchRealPower_eq_mul_sin, dcBranchFlow_apply]
  simp [t2, h2, b2]

/-- Flow transfer: the non-grounded solution `![5, 5 - s]` carries the grounded flow. -/
example (s : ℝ) : dcBranchFlow 2 1 t2 h2 b2 ![5, 5 - s] =
    dcBranchFlow 2 1 t2 h2 b2 (groundedAngles 2 1 t2 h2 b2 0 ![s, -s]) :=
  dcBranchFlow_eq_groundedAngles 2 1 t2 h2 b2 b2_pos 0 conn2 _ _ (by
    rw [L2_mulVec]; ext v; fin_cases v <;> simp)

end PhyslibExtTest.Circuits.DCFlowNetworkBridge
