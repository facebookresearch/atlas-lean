/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.PolynomialNetworks.DeficiencyZero
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Deficiency zero for an irreversible reaction with a self-loop -/

open MathlibExt.Biology.Dynamics.ComplexBalanced

namespace MathlibExtTest.Dynamics.PolynomialNetworks.DeficiencyZero

-- The reactions are 0 → 0 and 0 → A, in that order.
private def oneWay : ReactionNetwork Unit Bool where
  src := fun _ _ => 0
  prod := fun r _ => if r then 1 else 0

private def vertex (b : Bool) : oneWay.complexes :=
  ⟨oneWay.prod b, Or.inr ⟨b, rfl⟩⟩

private theorem vertex_surjective : Function.Surjective vertex := by
  rintro ⟨_, ⟨b, rfl⟩ | ⟨b, rfl⟩⟩
  · exact ⟨false, rfl⟩
  · exact ⟨b, rfl⟩

private theorem vertex_injective : Function.Injective vertex := by
  intro a b h
  have hcoeff := congrArg (fun c : oneWay.complexes => c.val ()) h
  cases a <;> cases b <;> first | rfl | simp [vertex, oneWay] at hcoeff

private theorem oneWay_deficiency : oneWay.deficiency = 0 := by
  classical
  have hcomplexes : Nat.card oneWay.complexes = 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective vertex ⟨vertex_injective, vertex_surjective⟩)]
    simp
  have hedge : oneWay.linkageGraph.Adj (vertex false) (vertex true) := by
    rw [ReactionNetwork.linkageGraph, SimpleGraph.fromRel_adj]
    exact ⟨fun h => Bool.noConfusion (vertex_injective h), Or.inl ⟨true, rfl, rfl⟩⟩
  have hcomponents : oneWay.numLinkageClasses = 1 := by
    apply SimpleGraph.card_connectedComponent_eq_one_iff.mpr
    refine (SimpleGraph.connected_iff _).mpr ⟨?_, ⟨vertex false⟩⟩
    intro c d
    obtain ⟨a, rfl⟩ := vertex_surjective c
    obtain ⟨b, rfl⟩ := vertex_surjective d
    cases a <;> cases b
    · exact .rfl
    · exact hedge.reachable
    · exact hedge.symm.reachable
    · exact .rfl
  have hspan : oneWay.stoichiometricSubspace = ⊤ := by
    apply top_unique
    intro f _
    have hv : (fun _ : Unit => (1 : ℝ)) ∈ oneWay.stoichiometricSubspace := by
      unfold ReactionNetwork.stoichiometricSubspace
      exact Submodule.subset_span ⟨true, funext fun s => by simp [oneWay]⟩
    have hf : f () • (fun _ : Unit => (1 : ℝ)) = f := by
      funext s
      cases s
      simp
    rw [← hf]
    exact oneWay.stoichiometricSubspace.smul_mem _ hv
  rw [ReactionNetwork.deficiency, hcomplexes, hcomponents, hspan, finrank_top,
    Module.finrank_fintype_fun_eq_card]
  decide

private theorem oneWay_not_weaklyReversible : ¬ oneWay.IsWeaklyReversible := by
  intro h
  rcases (h true).cases_head with hsame | ⟨_, ⟨_, hsrc, _⟩, _⟩
  · simpa [oneWay] using congrFun hsame ()
  · simpa [oneWay] using congrFun hsrc ()

example {k : Bool → ℝ} (hk : ∀ r, 0 < k r) :
    ¬ ∃ x : Unit → ℝ, (∀ s, 0 < x s) ∧ oneWay.massActionField k x = 0 :=
  oneWay.not_exists_positive_equilibrium oneWay_deficiency oneWay_not_weaklyReversible hk

end MathlibExtTest.Dynamics.PolynomialNetworks.DeficiencyZero
