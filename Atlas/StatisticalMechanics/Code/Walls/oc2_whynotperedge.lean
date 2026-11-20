/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Walls.oc_firstedgerevealone
import Code.Walls.oc_revealmuleone

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.DecisionTree
open StatMech.OSSS.AdaptMConditional
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.FKRevealmentClose

variable {E : Type*} [Fintype E] [DecidableEq E]














theorem oc2_reveal_lt_one_of_missing {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (T : DecisionTree E) (e : E) (ω₀ : ConfigSpace E)
    (hw₀ : 0 < weight ν ω₀) (hmiss : e ∉ T.queried ω₀) :
    reveal ν T e < 1 := by
  unfold reveal OSSS.expect
  
  have hterm : ∀ ω, weight ν ω * (if e ∈ T.queried ω then (1 : ℝ) else 0)
      ≤ weight ν ω * 1 := by
    intro ω
    have hwnn : 0 ≤ weight ν ω := Finset.prod_nonneg (fun e' _ => hν.nonneg e' (ω e'))
    apply mul_le_mul_of_nonneg_left _ hwnn
    split <;> norm_num
  have hstrict : weight ν ω₀ * (if e ∈ T.queried ω₀ then (1 : ℝ) else 0)
      < weight ν ω₀ * 1 := by
    rw [if_neg hmiss]
    simpa using hw₀
  calc (∑ ω, weight ν ω * (if e ∈ T.queried ω then (1 : ℝ) else 0))
      < ∑ ω, weight ν ω * 1 :=
        Finset.sum_lt_sum (fun ω _ => hterm ω) ⟨ω₀, Finset.mem_univ ω₀, hstrict⟩
    _ = ∑ ω, weight ν ω := by simp only [mul_one]
    _ = 1 := by
        have := expect_one hν
        unfold OSSS.expect at this; simpa [mul_one] using this






















theorem oc2_revealAdapt_first_ne_reveal {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X)
    {ν : E → Bool → ℝ} (T : DecisionTree E) (hlt : reveal ν T e₀ < 1) :
    revealAdapt μ σ f e₀ ≠ reveal ν T e₀ := by
  rw [oc_revealAdapt_first_eq_one hpos hμ1 σ f e₀ he₀ hnc]
  exact fun h => absurd (h ▸ hlt) (by norm_num)










theorem oc2_revealAdapt_first_ne_reveal_of_missing {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e₀ : E) (he₀ : (σ.symm e₀ : ℕ) = 0)
    (hnc : ∀ X, ¬ ∀ w, f w = f X)
    {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (T : DecisionTree E) (ω₀ : ConfigSpace E)
    (hw₀ : 0 < weight ν ω₀) (hmiss : e₀ ∉ T.queried ω₀) :
    revealAdapt μ σ f e₀ ≠ reveal ν T e₀ :=
  oc2_revealAdapt_first_ne_reveal hpos hμ1 σ f e₀ he₀ hnc T
    (oc2_reveal_lt_one_of_missing hν T e₀ ω₀ hw₀ hmiss)











theorem oc2_no_perEdge_match {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) :
    ¬ ∃ (ν : E → Bool → ℝ) (T : DecisionTree E),
        reveal ν T e₀ < 1 ∧ revealAdapt μ σ f e₀ = reveal ν T e₀ := by
  rintro ⟨ν, T, hlt, heq⟩
  exact oc2_revealAdapt_first_ne_reveal hpos hμ1 σ f e₀ he₀ hnc T hlt heq






theorem oc2_perEdge_match_forces_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X)
    {ν : E → Bool → ℝ} (T : DecisionTree E)
    (hmatch : revealAdapt μ σ f e₀ = reveal ν T e₀) :
    reveal ν T e₀ = 1 := by
  rw [← hmatch]
  exact oc_revealAdapt_first_eq_one hpos hμ1 σ f e₀ he₀ hnc

















theorem oc2_not_forall_revealAdapt_eq_reveal {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X)
    {ν : E → Bool → ℝ} (T : DecisionTree E) (hlt : reveal ν T e₀ < 1) :
    ¬ (∀ e, revealAdapt μ σ f e = reveal ν T e) := by
  intro hall
  exact oc2_revealAdapt_first_ne_reveal hpos hμ1 σ f e₀ he₀ hnc T hlt (hall e₀)











theorem oc2_uniformWeight_isProb :
    IsProbWeight (fun (_ : Fin 2) (_ : Bool) => (1 : ℝ) / 2) where
  nonneg := fun _ _ => by norm_num
  normalized := fun _ => by norm_num



theorem oc2_reveal_leaf_eq_zero {ν : E → Bool → ℝ} (b : Bool) (e : E) :
    reveal ν (DecisionTree.leaf b) e = 0 := by
  unfold reveal OSSS.expect
  apply Finset.sum_eq_zero
  intro ω _
  simp only []
  rw [if_neg]
  · ring
  · unfold DecisionTree.queried; simp










theorem oc2_revealAdapt_first_ne_reveal_witness :
    revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ))
        (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2)
      ≠ reveal (fun (_ : Fin 2) (_ : Bool) => (1 : ℝ) / 2) (DecisionTree.leaf false) (0 : Fin 2) := by
  rw [oc_first_edge_reveal_one_witness, oc2_reveal_leaf_eq_zero]
  norm_num

end Walls
end StatMech
