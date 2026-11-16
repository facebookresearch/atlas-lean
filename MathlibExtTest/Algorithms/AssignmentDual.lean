/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.AssignmentDual
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

@[expose] public section

/-- With constant unit costs, the potentials `u = 0` and `v = 1` are feasible and tight along
every permutation, so the certificate compares any two assignments `σ` and `τ`. -/
example {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    ∑ i, (fun _ _ => (1 : ℚ)) i (σ i) ≤ ∑ i, (fun _ _ => (1 : ℚ)) i (τ i) :=
  assignment_optimal_of_dual (fun _ _ => 1) (fun _ => 0) (fun _ => 1) σ
    (fun _ _ => by norm_num) (fun _ => by norm_num) τ

/-- For the costs `![![1, 3], ![2, 5]]`, the potentials `u = ![-1, 0]` and `v = ![2, 4]` are
feasible and tight along the swap, so the swap costs no more than any assignment `τ`. -/
example (τ : Equiv.Perm (Fin 2)) :
    ∑ i, ![![(1 : ℚ), 3], ![2, 5]] i (Equiv.swap 0 1 i) ≤
      ∑ i, ![![(1 : ℚ), 3], ![2, 5]] i (τ i) :=
  assignment_optimal_of_dual _ ![-1, 0] ![2, 4] _
    (by norm_num [Fin.forall_fin_two]) (by norm_num [Fin.forall_fin_two]) τ

end
