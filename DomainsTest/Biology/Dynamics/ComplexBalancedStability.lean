/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.ComplexBalancedStability
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Complex-balanced stability for the reversible pair

The network `A ⇌ B` has two species, two reactions, unit rate constants, and the positive
complex-balanced equilibrium `![1, 1]`. We instantiate forward existence, stability, and
class-relative attractivity. Constant equilibria outside its class can be arbitrarily close
to `![1, 1]` without converging to it, while forward existence and stability still hold across
classes.
-/

public section

open MathlibExt.Biology.Dynamics.ComplexBalanced
open ReactionNetwork
open Domains.Biology.Dynamics.ComplexBalancedStability
open scoped Topology

namespace DomainsTest.Biology.Dynamics.ComplexBalancedStability

/-- **The reversible pair `A ⇌ B`.** Two species and the two reactions `A → B` and `B → A`, in
that order (`0 = A`, `1 = B`). -/
def reversiblePair : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 1]]
  prod := ![![0, 1], ![1, 0]]

/-- **`(1, 1)` is complex balanced.** With unit rate constants, `![1, 1]` is a complex-balanced
point of `A ⇌ B`. -/
theorem reversiblePair_complexBalanced :
    reversiblePair.IsComplexBalanced (fun _ => 1) ![1, 1] := by
  classical
  intro z
  simp only [Finset.sum_filter, Fin.sum_univ_two]
  simp [ReactionNetwork.rate, reversiblePair, add_comm]

/-- **The field of `A ⇌ B`.** With unit rate constants, the mass-action field at `z` is
`(z 1 - z 0, z 0 - z 1)`. -/
theorem reversiblePair_field (z : Fin 2 → ℝ) :
    reversiblePair.massActionField (fun _ => 1) z = ![z 1 - z 0, z 0 - z 1] := by
  ext s
  fin_cases s <;> simp [ReactionNetwork.massActionField, reversiblePair,
    Fin.sum_univ_two, Fin.prod_univ_two] <;> ring

/-- **Diagonal equilibria.** With unit rate constants, every `(a, a)` is an equilibrium of
`A ⇌ B`. -/
theorem reversiblePair_equilibrium (a : ℝ) :
    reversiblePair.massActionField (fun _ => 1) ![a, a] = 0 := by
  rw [reversiblePair_field]
  ext s
  fin_cases s <;> simp

/-- **Forward solutions near `(1, 1)` in its class.** `exists_solution_of_near` for `A ⇌ B` with
unit rate constants at the equilibrium `(1, 1)`. -/
theorem reversiblePair_exists_solution_of_near :
    ∃ η > (0 : ℝ), ∀ z : Fin 2 → ℝ,
      z - ![1, 1] ∈ reversiblePair.stoichiometricSubspace → ‖z - ![1, 1]‖ < η →
      ∃ x : ℝ → Fin 2 → ℝ, x 0 = z ∧
        ∀ t, 0 ≤ t → HasDerivAt x (reversiblePair.massActionField (fun _ => 1) (x t)) t := by
  exact exists_solution_of_near reversiblePair (fun _ => 1) (by simp)
    ![1, 1] (by intro s; fin_cases s <;> norm_num) reversiblePair_complexBalanced
    ![1, 1] (by intro s; fin_cases s <;> norm_num) (reversiblePair_equilibrium 1)

/-- **Lyapunov stability of `(1, 1)`.** `stable` for `A ⇌ B` with unit rate constants at the
equilibrium `(1, 1)`. -/
theorem reversiblePair_stable (ε : ℝ) (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ x : ℝ → Fin 2 → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (reversiblePair.massActionField (fun _ => 1) (x t)) t) →
      x 0 - ![1, 1] ∈ reversiblePair.stoichiometricSubspace → ‖x 0 - ![1, 1]‖ < η →
      ∀ t, 0 ≤ t → ‖x t - ![1, 1]‖ < ε := by
  exact stable reversiblePair (fun _ => 1) (by simp)
    ![1, 1] (by intro s; fin_cases s <;> norm_num) reversiblePair_complexBalanced
    ![1, 1] (by intro s; fin_cases s <;> norm_num) (reversiblePair_equilibrium 1) ε hε

/-- **Attraction to `(1, 1)` within its class.** `attractive` for `A ⇌ B` with unit rate
constants at the equilibrium `(1, 1)`. -/
theorem reversiblePair_attractive :
    ∃ η > (0 : ℝ), ∀ x : ℝ → Fin 2 → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (reversiblePair.massActionField (fun _ => 1) (x t)) t) →
      x 0 - ![1, 1] ∈ reversiblePair.stoichiometricSubspace → ‖x 0 - ![1, 1]‖ < η →
      Filter.Tendsto x Filter.atTop (nhds ![1, 1]) := by
  exact attractive reversiblePair (fun _ => 1) (by simp)
    ![1, 1] (by intro s; fin_cases s <;> norm_num) reversiblePair_complexBalanced
    ![1, 1] (by intro s; fin_cases s <;> norm_num) (reversiblePair_equilibrium 1)

/-- **Conservation of `A + B`.** Every vector of the stoichiometric subspace of `A ⇌ B` has
coordinate sum zero. -/
theorem reversiblePair_conservation {v : Fin 2 → ℝ}
    (hv : v ∈ reversiblePair.stoichiometricSubspace) : v 0 + v 1 = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨r, rfl⟩ := hv
    fin_cases r <;> norm_num [reversiblePair]
  | zero => simp
  | add u v _ _ hu hv => simp only [Pi.add_apply]; linarith
  | smul c v _ hv => simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_add, hv, mul_zero]

/-- An equilibrium outside the compatibility class. The class restriction is required for
attractivity to the fixed equilibrium; Lyapunov stability also holds across classes. -/
theorem reversiblePair_outside_class :
    reversiblePair.massActionField (fun _ => 1) ![2, 2] = 0 ∧
      ![2, 2] - ![1, 1] ∉ reversiblePair.stoichiometricSubspace := by
  refine ⟨reversiblePair_equilibrium 2, fun h => ?_⟩
  have hc := reversiblePair_conservation h
  norm_num at hc

/-- The reversible pair is Lyapunov stable for initial states in every class. -/
theorem reversiblePair_stable_all_classes (ε : ℝ) (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ x : ℝ → Fin 2 → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (reversiblePair.massActionField (fun _ => 1) (x t)) t) →
      ‖x 0 - ![1, 1]‖ < η → ∀ t, 0 ≤ t → ‖x t - ![1, 1]‖ < ε := by
  exact stable_all_classes reversiblePair (by simp)
    (by intro s; fin_cases s <;> norm_num) reversiblePair_complexBalanced hε

/-- Forward solutions exist from nearby states of every class: for small `δ > 0` the state
`(1 + δ, 1)` is not an equilibrium, lies outside the class of `![1, 1]`, and still starts a
solution on `[0, ∞)`. -/
theorem reversiblePair_exists_solution_all_classes :
    ∃ η > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < η →
      reversiblePair.massActionField (fun _ => 1) ![1 + δ, 1] ≠ 0 ∧
      ![1 + δ, 1] - ![1, 1] ∉ reversiblePair.stoichiometricSubspace ∧
      ∃ x : ℝ → Fin 2 → ℝ, x 0 = ![1 + δ, 1] ∧
        ∀ t, 0 ≤ t → HasDerivAt x (reversiblePair.massActionField (fun _ => 1) (x t)) t := by
  obtain ⟨η, hη, hexists⟩ := exists_solution_of_near_all_classes reversiblePair
    (k := fun _ => 1) (by simp) (by intro s; fin_cases s <;> norm_num)
    reversiblePair_complexBalanced
  refine ⟨η, hη, fun δ hδ hδη => ⟨fun h => ?_, fun h => ?_, hexists _ ?_⟩⟩
  · have h0 := congrFun h 0
    rw [reversiblePair_field] at h0
    simp at h0
    linarith
  · have hc := reversiblePair_conservation h
    simp at hc
    linarith
  · apply (pi_norm_lt_iff hη).mpr
    intro s
    fin_cases s <;> simp [Real.norm_eq_abs, abs_of_pos hδ] <;> linarith

/-- Arbitrarily near equilibria outside the reference class need not converge to it.
This shows why the class restriction is necessary for attractivity; stability holds across
classes. -/
theorem reversiblePair_attractivity_needs_class (η : ℝ) (hη : 0 < η) :
    ∃ x : ℝ → Fin 2 → ℝ,
      (∀ t, x t = x 0) ∧
      (∀ t, reversiblePair.massActionField (fun _ => 1) (x t) = 0) ∧
      (∀ t, 0 ≤ t → HasDerivAt x
        (reversiblePair.massActionField (fun _ => 1) (x t)) t) ∧
      ‖x 0 - ![1, 1]‖ < η ∧
      x 0 - ![1, 1] ∉ reversiblePair.stoichiometricSubspace ∧
      ¬ Filter.Tendsto x Filter.atTop (nhds ![1, 1]) := by
  let a := 1 + η / 2
  let x : ℝ → Fin 2 → ℝ := fun _ => ![a, a]
  have heq : ∀ t, reversiblePair.massActionField (fun _ => 1) (x t) = 0 :=
    fun _ => reversiblePair_equilibrium a
  refine ⟨x, fun _ => rfl, heq, ?_, ?_, ?_, ?_⟩
  · intro t _
    rw [heq t]
    exact hasDerivAt_const t ![a, a]
  · apply (pi_norm_lt_iff hη).mpr
    intro s
    fin_cases s <;> simp [x, a, Real.norm_eq_abs, abs_of_pos hη] <;> linarith
  · intro h
    have hc := reversiblePair_conservation h
    simp [x, a] at hc
    linarith
  · intro h
    have hlimit : Filter.Tendsto x Filter.atTop (nhds ![a, a]) := tendsto_const_nhds
    have hsame := tendsto_nhds_unique hlimit h
    have hzero := congrFun hsame 0
    simp [a] at hzero
    linarith

#print axioms Domains.Biology.Dynamics.ComplexBalancedStability.exists_solution_of_near
#print axioms Domains.Biology.Dynamics.ComplexBalancedStability.exists_solution_of_near_all_classes
#print axioms Domains.Biology.Dynamics.ComplexBalancedStability.stable
#print axioms Domains.Biology.Dynamics.ComplexBalancedStability.attractive
#print axioms Domains.Biology.Dynamics.ComplexBalancedStability.stable_all_classes
#print axioms reversiblePair_complexBalanced
#print axioms reversiblePair_field
#print axioms reversiblePair_equilibrium
#print axioms reversiblePair_exists_solution_of_near
#print axioms reversiblePair_stable
#print axioms reversiblePair_attractive
#print axioms reversiblePair_conservation
#print axioms reversiblePair_outside_class
#print axioms reversiblePair_attractivity_needs_class
#print axioms reversiblePair_stable_all_classes
#print axioms reversiblePair_exists_solution_all_classes

end DomainsTest.Biology.Dynamics.ComplexBalancedStability
