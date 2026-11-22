/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.SelfishRoutingArcWalkBridge
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Arc-walk bridge checks

Concrete consumers of `MathlibExt.GameTheory.SelfishRoutingArcWalkBridge`: the
arc-simple bridge instance with both sides `![1, 2, 3, 0]`, and the non-simple
counterexample (`edgeFlow` 4 against `edgeVolume` 7 on arc 0).

These are elaboration and non-vacuity checks, not new results.
-/

open MathlibExt.Combinatorics.Graph.ArcNetwork
open Matrix

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
    rw [
      MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow_eq_edgeVolume
        (fun _ => 0) (fun _ => 2)
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
