/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.DeficiencyZero.StabilityComposition

/-!
# Deficiency-zero local asymptotic stability

`localAsymptoticStability` on the reversible isomerization `A ⇌ B` with unit rate constants. The
network is weakly reversible and has deficiency zero; `(3/2, 3/2)` is the only positive
equilibrium in the compatibility class of `(1, 2)`, and solutions that start in that class near it
stay near it and converge to it.
-/

open MathlibExt.Biology.Dynamics.ComplexBalanced ReactionNetwork
open Domains.Biology.Dynamics.DeficiencyZero

namespace DomainsTest.Biology.Dynamics.DeficiencyZero.StabilityComposition

-- The reactions are `A → B` and `B → A`, in that order (`0 = A`, `1 = B`).
private def revAB : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 1]]
  prod := ![![0, 1], ![1, 0]]

private theorem revAB_deficiency : revAB.deficiency = 0 := by
  refine revAB.deficiency_eq_zero_iff.2 fun α hα η => ?_
  have h0 := congrFun hα 0
  simp [revAB, Fin.sum_univ_two] at h0
  simp only [revAB, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : α 1 = α 0 := by linarith
  rw [this]
  ring

private theorem revAB_isWeaklyReversible : revAB.IsWeaklyReversible :=
  isWeaklyReversible_of_reversible fun r => by
    fin_cases r
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨0, rfl, rfl⟩

private theorem pos_one_two : ∀ s, 0 < (![1, 2] : Fin 2 → ℝ) s := by
  intro s
  fin_cases s <;> norm_num

private theorem pos_equilibrium : ∀ s, 0 < (![3 / 2, 3 / 2] : Fin 2 → ℝ) s := by
  intro s
  fin_cases s <;> norm_num

-- With unit rate constants, `(3/2, 3/2)` is an equilibrium.
private theorem revAB_equilibrium :
    revAB.massActionField (fun _ => 1) ![3 / 2, 3 / 2] = 0 := by
  ext s
  fin_cases s <;>
    simp [ReactionNetwork.massActionField, revAB, Fin.sum_univ_two, Fin.prod_univ_two]

-- `(3/2, 3/2) - (1, 2)` is half the reaction vector of `B → A`.
private theorem revAB_mem_class :
    (![3 / 2, 3 / 2] : Fin 2 → ℝ) - ![1, 2] ∈ revAB.stoichiometricSubspace := by
  have h : (![3 / 2, 3 / 2] : Fin 2 → ℝ) - ![1, 2] =
      (1 / 2 : ℝ) • fun s => (revAB.prod 1 s : ℝ) - revAB.src 1 s := by
    ext s
    fin_cases s <;> norm_num [revAB]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)

/-- The only positive equilibrium in the class of `(1, 2)` is `(3/2, 3/2)`. -/
example (x : Fin 2 → ℝ) (hx : (∀ s, 0 < x s) ∧ x - ![1, 2] ∈ revAB.stoichiometricSubspace ∧
    revAB.massActionField (fun _ => 1) x = 0) : x = ![3 / 2, 3 / 2] :=
  (localAsymptoticStability revAB revAB_deficiency revAB_isWeaklyReversible
    (k := fun _ => 1) (fun _ => one_pos) pos_one_two).1.unique hx
    ⟨pos_equilibrium, revAB_mem_class, revAB_equilibrium⟩

/-- Solutions in the class that start near `(3/2, 3/2)` stay within `ε` of it. -/
example (ε : ℝ) (hε : 0 < ε) : ∃ η > 0, ∀ x : ℝ → Fin 2 → ℝ,
    (∀ t, 0 ≤ t → HasDerivAt x (revAB.massActionField (fun _ => 1) (x t)) t) →
    x 0 - ![3 / 2, 3 / 2] ∈ revAB.stoichiometricSubspace → ‖x 0 - ![3 / 2, 3 / 2]‖ < η →
    ∀ t, 0 ≤ t → ‖x t - ![3 / 2, 3 / 2]‖ < ε :=
  ((localAsymptoticStability revAB revAB_deficiency revAB_isWeaklyReversible
    (k := fun _ => 1) (fun _ => one_pos) pos_one_two).2 _ pos_equilibrium revAB_mem_class
    revAB_equilibrium).2.1 ε hε

/-- Solutions in the class that start close enough to `(3/2, 3/2)` converge to it. -/
example : ∃ η > 0, ∀ x : ℝ → Fin 2 → ℝ,
    (∀ t, 0 ≤ t → HasDerivAt x (revAB.massActionField (fun _ => 1) (x t)) t) →
    x 0 - ![3 / 2, 3 / 2] ∈ revAB.stoichiometricSubspace → ‖x 0 - ![3 / 2, 3 / 2]‖ < η →
    Filter.Tendsto x Filter.atTop (nhds ![3 / 2, 3 / 2]) :=
  ((localAsymptoticStability revAB revAB_deficiency revAB_isWeaklyReversible
    (k := fun _ => 1) (fun _ => one_pos) pos_one_two).2 _ pos_equilibrium revAB_mem_class
    revAB_equilibrium).2.2

#print axioms Domains.Biology.Dynamics.DeficiencyZero.localAsymptoticStability

end DomainsTest.Biology.Dynamics.DeficiencyZero.StabilityComposition
