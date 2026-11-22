/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.ArcNetworkWalk
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Arc-network walk checks

Concrete consumers of `MathlibExt.Combinatorics.Graph.ArcNetworkWalk` on the network
with nodes `Fin 3` and arcs `Fin 4`: `0 : 0 → 1`, `1 : 0 → 1` (parallel), `2 : 1 → 2`,
`3 : 2 → 0`. Valid and invalid walks, parallel roads, and node balance
`![-6, 0, 6]`.

These are elaboration and non-vacuity checks, not new results.
-/

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

open Matrix

/-- The public statement shapes of the walk and volume results. -/
example {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype P]
    {tail head : E → V} {orig dest : P → V} {edges : P → List E}
    (hwalk : ∀ p, IsArcWalk tail head (orig p) (dest p) (edges p)) (f : P → ℝ)
    (hf : ∀ p, 0 ≤ f p) (v : V) (e : E)
    :
    0 ≤ edgeVolume edges f e ∧
      (incidenceMatrix tail head).mulVec (edgeVolume edges f) v =
        ∑ p, f p * ((if dest p = v then 1 else 0) - (if orig p = v then 1 else 0)) :=
  ⟨edgeVolume_nonneg edges hf e, incidenceMatrix_mulVec_edgeVolume hwalk f v⟩

/-- The empty walk at one node is valid. -/
example :
    IsArcWalk (![0, 0, 1, 2] : Fin 4 → Fin 3) (![1, 1, 2, 0] : Fin 4 → Fin 3) 0 0
      ([] : List (Fin 4)) :=
  ⟨fun _ => rfl, by simp, List.IsChain.nil, by simp⟩

/-- The route `[0, 2]` is a valid walk from `0` to `2`. -/
example :
    IsArcWalk (![0, 0, 1, 2] : Fin 4 → Fin 3) (![1, 1, 2, 0] : Fin 4 → Fin 3) 0 2
      ([0, 2] : List (Fin 4)) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro e he
    simp only [List.head?_cons, Option.mem_some] at he
    rw [← he]
    decide
  · refine List.isChain_cons.mpr ⟨?_, List.IsChain.singleton _⟩
    intro b hb
    simp only [List.head?_cons, Option.mem_some] at hb
    rw [← hb]
    decide
  · intro e he
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some] at he
    rw [← he]
    decide

/-- The parallel route `[1, 2]` is a valid walk from `0` to `2`. -/
example :
    IsArcWalk (![0, 0, 1, 2] : Fin 4 → Fin 3) (![1, 1, 2, 0] : Fin 4 → Fin 3) 0 2
      ([1, 2] : List (Fin 4)) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro e he
    simp only [List.head?_cons, Option.mem_some] at he
    rw [← he]
    decide
  · refine List.isChain_cons.mpr ⟨?_, List.IsChain.singleton _⟩
    intro b hb
    simp only [List.head?_cons, Option.mem_some] at hb
    rw [← hb]
    decide
  · intro e he
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some] at he
    rw [← he]
    decide

/-- The closed walk `[0, 2, 3]` from `0` to `0` is valid. -/
example :
    IsArcWalk (![0, 0, 1, 2] : Fin 4 → Fin 3) (![1, 1, 2, 0] : Fin 4 → Fin 3) 0 0
      ([0, 2, 3] : List (Fin 4)) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro e he
    simp only [List.head?_cons, Option.mem_some] at he
    rw [← he]
    decide
  · refine List.isChain_cons.mpr ⟨?_, List.isChain_cons.mpr ⟨?_, List.IsChain.singleton _⟩⟩
    · intro b hb
      simp only [List.head?_cons, Option.mem_some] at hb
      rw [← hb]
      decide
    · intro b hb
      simp only [List.head?_cons, Option.mem_some] at hb
      rw [← hb]
      decide
  · intro e he
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some] at he
    rw [← he]
    decide

/-- Invalid route control: arc `2` alone does not start at `0`, so `[2]` is no walk
from `0` to `2`. -/
example :
    ¬ IsArcWalk (![0, 0, 1, 2] : Fin 4 → Fin 3) (![1, 1, 2, 0] : Fin 4 → Fin 3) 0 2
      ([2] : List (Fin 4)) := by
  intro h
  have h1 := arcWalk_tail_head h
  exact (by decide : (![0, 0, 1, 2] : Fin 4 → Fin 3) 2 ≠ 0) h1

/-- Node balance: flows `4` and `2` on the parallel routes `[0, 2]` and `[1, 2]` give
inflow minus outflow `![-6, 0, 6]`. -/
example :
    (incidenceMatrix ![0, 0, 1, 2] ![1, 1, 2, 0]).mulVec
        (edgeVolume ![([0, 2] : List (Fin 4)), [1, 2]] ![4, 2]) = ![-6, 0, 6] := by
  have hwalk : ∀ p : Fin 2,
      IsArcWalk (![0, 0, 1, 2] : Fin 4 → Fin 3) (![1, 1, 2, 0] : Fin 4 → Fin 3) 0 2
        ((![([0, 2] : List (Fin 4)), [1, 2]]) p) := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor <;>
      · refine ⟨by simp, ?_, ?_, ?_⟩
        · intro e he
          simp only [List.head?_cons, Option.mem_some] at he
          rw [← he]
          decide
        · refine List.isChain_cons.mpr ⟨?_, List.IsChain.singleton _⟩
          intro b hb
          simp only [List.head?_cons, Option.mem_some] at hb
          rw [← hb]
          decide
        · intro e he
          simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some] at he
          rw [← he]
          decide
  funext v
  rw [incidenceMatrix_mulVec_edgeVolume hwalk]
  fin_cases v <;> simp [Fin.sum_univ_two, Fin.ext_iff] <;> norm_num

/-! ### Travel-time pairing at fixed link costs -/

/-- Link travel times with distinct slopes per arc: `t e x = (e + 1) x + 1`. -/
noncomputable def tt (e : Fin 4) (x : ℝ) : ℝ := (((e : ℕ) : ℝ) + 1) * x + 1

/-- Two routes sharing arc `2`; the parallel arcs `0` and `1` stay distinct. -/
abbrev sharedRoutes : Fin 2 → List (Fin 4) := ![[0, 2], [1, 2]]
/-- Route `0` traverses arcs `0` and `2` twice. -/
abbrev doubleRoutes : Fin 2 → List (Fin 4) := ![[0, 2, 3, 0, 2], [0, 2]]
/-- `sharedRoutes` plus the route `[0, 2, 3, 0, 2]`, which will carry zero flow. -/
abbrev zeroFlowRoutes : Fin 3 → List (Fin 4) := ![[0, 2], [1, 2], [0, 2, 3, 0, 2]]

example {P E : Type*} [Fintype P] [Fintype E] [DecidableEq E] (edges : P → List E)
    (f : P → ℝ) (c : E → ℝ) :
    ∑ p, f p * ((edges p).map c).sum = ∑ e, edgeVolume edges f e * c e :=
  sum_mul_sum_map_eq_sum_edgeVolume_mul edges f fun e _ => c e

/-! ### Two routes share an arc, with distinct costs -/

private theorem sharedArcVolume : edgeVolume sharedRoutes ![1, 2] = ![1, 2, 3, 0] := by
  funext e
  fin_cases e <;> simp [edgeVolume, Fin.sum_univ_two] <;> norm_num

example : (fun e => tt e (edgeVolume sharedRoutes ![1, 2] e)) = ![2, 5, 10, 1] := by
  rw [sharedArcVolume]
  funext e
  fin_cases e <;> simp [tt] <;> norm_num

example : ∑ p, (![1, 2] : Fin 2 → ℝ) p *
    ((sharedRoutes p).map fun e => tt e (edgeVolume sharedRoutes ![1, 2] e)).sum = 42 := by
  rw [sharedArcVolume]
  simp [tt, Fin.sum_univ_two]
  norm_num

example : ∑ e, edgeVolume sharedRoutes ![1, 2] e * tt e (edgeVolume sharedRoutes ![1, 2] e) = 42 := by
  rw [sharedArcVolume]
  simp [tt, Fin.sum_univ_four]
  norm_num

/-! ### Zero path flow -/

example {P E : Type*} [Fintype P] [Fintype E] [DecidableEq E] (edges : P → List E)
    (t : E → ℝ → ℝ) :
    ∑ p, (0 : P → ℝ) p * ((edges p).map fun e => t e (edgeVolume edges 0 e)).sum = 0 ∧
      ∑ e, edgeVolume edges (0 : P → ℝ) e * t e (edgeVolume edges 0 e) = 0 := by
  simp [edgeVolume]

/-- A zero-flow route leaves the volumes unchanged (arc `3`, used only by it, has volume 0). -/
private theorem zeroFlowVolume : edgeVolume zeroFlowRoutes ![1, 2, 0] = ![1, 2, 3, 0] := by
  funext e
  fin_cases e <;> simp [edgeVolume, Fin.sum_univ_three] <;> norm_num

/-- The zero-flow route has route time 25, yet both sides stay 42. -/
example : ((zeroFlowRoutes 2).map fun e => tt e (edgeVolume zeroFlowRoutes ![1, 2, 0] e)).sum = 25 ∧
    ∑ p, (![1, 2, 0] : Fin 3 → ℝ) p *
      ((zeroFlowRoutes p).map fun e => tt e (edgeVolume zeroFlowRoutes ![1, 2, 0] e)).sum = 42 ∧
    ∑ e, edgeVolume zeroFlowRoutes ![1, 2, 0] e * tt e (edgeVolume zeroFlowRoutes ![1, 2, 0] e) = 42 := by
  rw [zeroFlowVolume]
  refine ⟨?_, ?_, ?_⟩
  · simp [tt]
    norm_num
  · simp [tt, Fin.sum_univ_three]
    norm_num
  · simp [tt, Fin.sum_univ_four]
    norm_num

/-! ### A route traversing an arc twice (multiplicity counted) -/

example : ([0, 2, 3, 0, 2] : List (Fin 4)).count 0 = 2 := by decide

private theorem doubleTraversalVolume : edgeVolume doubleRoutes ![3, 1] = ![7, 0, 7, 3] := by
  funext e
  fin_cases e <;> simp [edgeVolume, Fin.sum_univ_two] <;> norm_num

example : ∑ p, (![3, 1] : Fin 2 → ℝ) p *
    ((doubleRoutes p).map fun e => tt e (edgeVolume doubleRoutes ![3, 1] e)).sum = 249 := by
  rw [doubleTraversalVolume]
  simp [tt, Fin.sum_univ_two]
  norm_num

example : ∑ e, edgeVolume doubleRoutes ![3, 1] e * tt e (edgeVolume doubleRoutes ![3, 1] e) = 249 := by
  rw [doubleTraversalVolume]
  simp [tt, Fin.sum_univ_four]
  norm_num

/-- Set-based volumes (membership count), a mutant of `edgeVolume`. -/
def setVol {P E : Type*} [Fintype P] [DecidableEq E] (edges : P → List E) (f : P → ℝ)
    (e : E) : ℝ :=
  ∑ p with e ∈ edges p, f p

theorem doubleTraversalSetVolume : setVol doubleRoutes ![3, 1] = ![4, 0, 4, 3] := by
  funext e
  fin_cases e <;> simp [setVol, Finset.sum_filter, Fin.sum_univ_two] <;> norm_num

/-- Control: arc-list route times with set-based volumes; the identity fails (165 ≠ 111). -/
example : ¬ ∀ (edges : Fin 2 → List (Fin 4)) (f : Fin 2 → ℝ) (t : Fin 4 → ℝ → ℝ),
    ∑ p, f p * ((edges p).map fun e => t e (setVol edges f e)).sum =
      ∑ e, setVol edges f e * t e (setVol edges f e) := by
  intro h
  have h1 := h doubleRoutes ![3, 1] tt
  rw [doubleTraversalSetVolume] at h1
  simp [tt, Fin.sum_univ_two, Fin.sum_univ_four] at h1
  norm_num at h1


end MathlibExt.Combinatorics.Graph.ArcNetwork

#print axioms MathlibExt.Combinatorics.Graph.ArcNetwork.sum_mul_sum_map_eq_sum_edgeVolume_mul
