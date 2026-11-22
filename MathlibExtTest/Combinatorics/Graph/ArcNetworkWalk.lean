/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.ArcNetworkWalk
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Arc-network walk checks

Concrete consumers of `MathlibExt.Combinatorics.Graph.ArcNetworkWalk` on the network
with nodes `Fin 3` and arcs `Fin 4`: `0 : 0 → 1`, `1 : 0 → 1` (parallel), `2 : 1 → 2`,
`3 : 2 → 0`. Valid and invalid walks, parallel roads, node balance `![-6, 0, 6]`, the
link-simple bridge instance with both sides `![1, 2, 3, 0]`, and the non-simple
counterexample (`edgeFlow` 4 against `edgeVolume` 7 on arc 0).

These are elaboration and non-vacuity checks, not new results.
-/

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

open Matrix

/-- The public statement shapes of the walk and volume results. -/
example {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype P]
    {tail head : E → V} {orig dest : P → V} {edges : P → List E}
    (hwalk : ∀ p, IsArcWalk tail head (orig p) (dest p) (edges p)) (f : P → ℝ)
    (hf : ∀ p, 0 ≤ f p) (v : V) (e : E) (ℓ : E → ℝ → ℝ)
    (hsimple : ∀ p, (edges p).Nodup) :
    0 ≤ edgeVolume edges f e ∧
      (incidenceMatrix tail head).mulVec (edgeVolume edges f) v =
        ∑ p, f p * ((if dest p = v then 1 else 0) - (if orig p = v then 1 else 0)) ∧
      MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow
          { commodity := fun p => (orig p, dest p), edges := fun p => (edges p).toFinset,
            latency := ℓ } f e =
        edgeVolume edges f e :=
  ⟨edgeVolume_nonneg edges hf e, incidenceMatrix_mulVec_edgeVolume hwalk f v,
    edgeFlow_eq_edgeVolume orig dest edges ℓ hsimple f e⟩

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

/-- Bridge instance: on the arc-simple routes `[0, 2]`, `[1, 2]` with flows `1`, `2`,
the set-based `edgeFlow` and the multiplicity `edgeVolume` both equal `![1, 2, 3, 0]`
(the parallel arcs `0` and `1` stay distinct, arc `2` is shared). -/
example :
    edgeVolume ![([0, 2] : List (Fin 4)), [1, 2]] ![1, 2] = ![1, 2, 3, 0] ∧
      (fun e => MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow
        { commodity := fun _ : Fin 2 => ((0 : Fin 3), (2 : Fin 3)),
          edges := fun p => (![([0, 2] : List (Fin 4)), [1, 2]] p).toFinset,
          latency := fun _ _ => 0 } ![1, 2] e) = ![1, 2, 3, 0] := by
  constructor
  · funext e
    fin_cases e <;> simp [edgeVolume, Fin.sum_univ_two] <;> norm_num
  · funext e
    rw [edgeFlow_eq_edgeVolume (fun _ => 0) (fun _ => 2)
      ![([0, 2] : List (Fin 4)), [1, 2]] (fun _ _ => 0)
      (fun p => by fin_cases p <;> decide) ![1, 2] e]
    fin_cases e <;> simp [edgeVolume, Fin.sum_univ_two] <;> norm_num

/-- Non-simple counterexample: the route `[0, 2, 3, 0, 2]` traverses arc `0` twice, so
with flows `3` on it and `1` on `[0, 2]`, arc `0` has `edgeVolume` `7` but set-based
`edgeFlow` `4`; the bridge does not apply. -/
example :
    edgeVolume ![([0, 2, 3, 0, 2] : List (Fin 4)), [0, 2]] ![3, 1] 0 = 7 ∧
      MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow
          { commodity := fun _ : Fin 2 => ((0 : Fin 3), (2 : Fin 3)),
            edges := fun p => (![([0, 2, 3, 0, 2] : List (Fin 4)), [0, 2]] p).toFinset,
            latency := fun _ _ => 0 } ![3, 1] 0 = 4 ∧
      ¬ ([0, 2, 3, 0, 2] : List (Fin 4)).Nodup := by
  refine ⟨?_, ?_, by decide⟩
  · simp [edgeVolume, Fin.sum_univ_two] <;> norm_num
  · simp [MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow, Finset.sum_filter,
      Fin.sum_univ_two] <;> norm_num

end MathlibExt.Combinatorics.Graph.ArcNetwork
