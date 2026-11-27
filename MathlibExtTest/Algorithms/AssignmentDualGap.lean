/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algorithms.AssignmentDualGap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open AssignmentDual

private noncomputable def cost : Fin 2 → Fin 2 → ℝ :=
  ![![2, -Real.sqrt 2], ![1 + Real.sqrt 2, 4]]

-- The swap uses both irrational entries, one negative. The column potential is nonconstant.
example (τ : Equiv.Perm (Fin 2)) :
    ∑ i, cost i (Equiv.swap 0 1 i) ≤ ∑ i, cost i (τ i) :=
  optimal_of_tight cost ![-Real.sqrt 2, 1] ![Real.sqrt 2, 0] (Equiv.swap 0 1)
    (by norm_num [Fin.forall_fin_two, cost]) (by norm_num [Fin.forall_fin_two, cost]) τ

-- Independently of the certificate, the identity costs five more than the swap.
example : (∑ i, cost i i) - (∑ i, cost i (Equiv.swap 0 1 i)) = 5 := by
  norm_num [Fin.sum_univ_two, cost, add_left_comm, add_comm, add_assoc]

-- With no rows the feasibility and tightness hypotheses are vacuous, for arbitrary potentials.
example (w : Fin 0 → Fin 0 → ℝ) (u v : Fin 0 → ℝ) (σ : Equiv.Perm (Fin 0)) :
    (∑ i, w i (σ i)) = (∑ i, u i) + ∑ j, v j :=
  (cost_eq_dual_iff w u v (fun i ↦ Fin.elim0 i) σ).2 (fun i ↦ Fin.elim0 i)

-- If both rows use column zero, the potential bound fails even though every entry is tight.
example : let v : Fin 2 → ℝ := ![0, 1]
    let w : Fin 2 → Fin 2 → ℝ := fun _ j ↦ v j
    (∀ i j, 0 + v j = w i j) ∧ (∑ i : Fin 2, w i 0) < (∑ j, v j) := by
  norm_num [Fin.sum_univ_two]
