/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.ArcNetworkCriticalPath
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Arc-network critical-path checks

Concrete consumers of `MathlibExt.Combinatorics.Graph.ArcNetworkCriticalPath`: the
parallel-arc network `0 : 0 → 1` (2 ticks), `1 : 0 → 1` (5), `2 : 1 → 2` (1) with feasible
schedule `(0, 5, 6)` meeting the bound on `[1, 2]`, the non-walk `[1, 1, 2]` overrunning it,
earliest dates on a one-arc network, and controls for both premises of the existence result.
Elaboration and non-vacuity checks, not new results.
-/

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

/-- Parallel arcs: `(0, 5, 6)` is feasible, `[1, 2]` is a walk of duration `6` meeting the
bound with equality, and `(0, 4, 5)` is infeasible. -/
private theorem parallelArcs :
    IsFeasibleSchedule (![0, 0, 1] : Fin 3 → Fin 3) ![1, 1, 2] ![2, 5, 1] ![0, 5, 6] ∧
    IsArcWalk (![0, 0, 1] : Fin 3 → Fin 3) ![1, 1, 2] 0 2 [1, 2] ∧
    (![0, 5, 6] : Fin 3 → ℕ) 0 + (([1, 2] : List (Fin 3)).map ![2, 5, 1]).sum = 6 ∧
    ¬ IsFeasibleSchedule (![0, 0, 1] : Fin 3 → Fin 3) ![1, 1, 2] ![2, 5, 1] ![0, 4, 5] := by
  refine ⟨by unfold IsFeasibleSchedule; decide, ⟨by simp, by simp, by simp, by simp⟩,
    by decide, by unfold IsFeasibleSchedule; decide⟩

/-- The bound at the parallel-arc witness, through the owner theorem. -/
example : (![0, 5, 6] : Fin 3 → ℕ) 0 + (([1, 2] : List (Fin 3)).map ![2, 5, 1]).sum
    ≤ (![0, 5, 6] : Fin 3 → ℕ) 2 :=
  parallelArcs.1.add_sum_map_le parallelArcs.2.1

/-- `[1, 1, 2]` is not a walk from `0` to `2`, and its duration `11` exceeds `τ 2 - τ 0 = 6`
under the feasible `(0, 5, 6)`: the bound needs the walk premise. -/
example : ¬ IsArcWalk (![0, 0, 1] : Fin 3 → Fin 3) ![1, 1, 2] 0 2 [1, 1, 2] ∧
    ¬ (0 : ℕ) + (([1, 1, 2] : List (Fin 3)).map ![2, 5, 1]).sum ≤ 6 :=
  ⟨fun h => by simpa [List.isChain_cons] using h.2.2.1, by decide⟩

/-- The single arc of the one-arc network is a walk from `0` to `1`. -/
private theorem oneArcWalk :
    IsArcWalk (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1) 0 1 [0] :=
  ⟨by simp, by simp, by simp, by simp⟩

/-- The one-arc network has no nonempty closed walk: its only arc leaves `0` for `1`. -/
private theorem oneArc_acyc (v : Fin 2) (l : List (Fin 1))
    (hl : IsArcWalk (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1) v v l) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l =>
    have h1 : (0 : Fin 2) = v := hl.2.1 a (by simp)
    cases l with
    | nil =>
      have h2 : (1 : Fin 2) = v := hl.2.2.2 a (by simp)
      exact absurd (h1.trans h2.symm) (by decide)
    | cons b l =>
      have h2 := hl.2.2.1
      rw [List.isChain_cons] at h2
      exact absurd (h2.1 b (by simp)) (by decide : (1 : Fin 2) ≠ 0)

/-- Earliest dates on the one-arc network `0 → 1` of duration `7`: some feasible schedule has
`τ 0 = 0` and `τ 1 = 7`, and every feasible schedule has `τ' 0 + 7 ≤ τ' 1`. -/
example : ∃ τ : Fin 2 → ℕ,
    IsFeasibleSchedule (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1) (fun _ => 7) τ ∧
      τ 0 = 0 ∧ τ 1 = 7 ∧
      ∀ τ' : Fin 2 → ℕ,
        IsFeasibleSchedule (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1) (fun _ => 7) τ' →
          τ' 0 + 7 ≤ τ' 1 := by
  have hreach : ∀ v, ∃ l, IsArcWalk (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1) 0 v l := by
    intro v
    fin_cases v
    · exact ⟨[], ⟨by simp, by simp, by simp, by simp⟩⟩
    · exact ⟨[0], oneArcWalk⟩
  obtain ⟨τ, hτ, hτ0, hτv⟩ :=
    exists_isFeasibleSchedule_eq_sum (fun _ => 7) oneArc_acyc hreach
  obtain ⟨l, hl, hsum⟩ := hτv 1
  have hlen : l.length = 1 := by
    cases l with
    | nil => simp [IsArcWalk] at hl
    | cons a l =>
      cases l with
      | nil => rfl
      | cons b l =>
        have h2 := hl.2.2.1
        rw [List.isChain_cons] at h2
        exact absurd (h2.1 b (by simp)) (by decide : (1 : Fin 2) ≠ 0)
  have h1 : τ 1 = 7 := by
    rw [← hsum]
    simp [List.map_const, List.sum_replicate, hlen]
  exact ⟨τ, hτ, hτ0, h1, fun τ' hτ' => by simpa using hτ'.add_sum_map_le oneArcWalk⟩

/-- The closed-walk premise cannot be dropped: the one-event loop of duration `1` admits no
feasible schedule at all. -/
example : ¬ ∃ τ : Fin 1 → ℕ,
    IsFeasibleSchedule (fun _ : Fin 1 => (0 : Fin 1)) (fun _ => 0) (fun _ => 1) τ ∧
      τ 0 = 0 := by
  rintro ⟨τ, hτ, -⟩
  have h : τ 0 + 1 ≤ τ 0 := hτ 0
  omega

/-- The reachability premise cannot be dropped: with no arcs, event `1` has no walk from the
source `0`, so no schedule meets the conclusion. -/
example : ¬ ∃ τ : Fin 2 → ℕ, τ 0 = 0 ∧
    ∀ v, ∃ l, IsArcWalk (fun a : Empty => a.elim) (fun a => a.elim) 0 v l ∧
      (l.map (fun a : Empty => a.elim)).sum = τ v := by
  rintro ⟨τ, -, hτ⟩
  obtain ⟨l, hl, -⟩ := hτ 1
  cases l with
  | nil => simp [IsArcWalk] at hl
  | cons a _ => exact a.elim

end MathlibExt.Combinatorics.Graph.ArcNetwork

#print axioms MathlibExt.Combinatorics.Graph.ArcNetwork.IsFeasibleSchedule.add_sum_map_le
#print axioms MathlibExt.Combinatorics.Graph.ArcNetwork.exists_isFeasibleSchedule_eq_sum
