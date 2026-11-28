/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.PointToPointConnectionDefs

namespace MetaMathlibExt.Complexity.NPComplete.PointToPointConnection

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Complexity.Karp (edgeGraph)

private theorem accepts_encoding (i : PointToPointConnectionInstance) :
    pointToPointConnectionDec (bitEncode i) = true ↔
      WellFormed i ∧ PointToPointConnectionFeasible i := by
  simp [pointToPointConnectionDec, bitDecode_bitEncode]

/-- A vertex set closed under adjacency contains everything reachable from its members. -/
private theorem not_reachable {n : ℕ} {es : List (ℕ × ℕ)} (P : Fin n → Prop)
    (hP : ∀ u v, (edgeGraph n es).Adj u v → P u → P v) {u v : Fin n} (hu : P u) (hv : ¬ P v) :
    ¬ (edgeGraph n es).Reachable u v := by
  rintro ⟨p⟩
  induction p with
  | nil => exact hv hu
  | cons h _ ih => exact ih (hP _ _ h hu) hv

/-- A lone continuation bit is a truncated instance encoding. -/
example : pointToPointConnectionDec [true] = false := by
  have h : bitDecode (α := PointToPointConnectionInstance) [true] = none := rfl
  simp [pointToPointConnectionDec, h]

/-- The path `0 - 1 - 2` of weight two connects `0` to `2`, avoiding the direct edge of weight
five. -/
example :
    pointToPointConnectionDec
      (bitEncode ((3, [(0, 1, 1), (1, 2, 1), (0, 2, 5)], [(0, 2)], 2) :
        PointToPointConnectionInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [(0, 1, 1), (1, 2, 1)], by decide, by decide, ?_⟩
  intro q hq hs hd
  simp only [List.mem_singleton] at hq
  subst hq
  have h₀₁ : (edgeGraph 3 [(0, 1), (1, 2)]).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
    unfold edgeGraph
    simp only [SimpleGraph.fromRel_adj]
    decide
  have h₁₂ : (edgeGraph 3 [(0, 1), (1, 2)]).Adj ⟨1, by decide⟩ ⟨2, by decide⟩ := by
    unfold edgeGraph
    simp only [SimpleGraph.fromRel_adj]
    decide
  exact h₀₁.reachable.trans h₁₂.reachable

/-- The only edge has weight three, above the bound two, and without it `1` is unreachable from
`0`. -/
example :
    pointToPointConnectionDec
      (bitEncode ((2, [(0, 1, 3)], [(0, 1)], 2) : PointToPointConnectionInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨E', hsub, hw, hr⟩ := ((accepts_encoding _).1 h).2
  rcases List.sublist_singleton.1 hsub with rfl | rfl
  · have hr' := hr (0, 1) (by simp) (by decide) (by decide)
    refine not_reachable (fun v => v.val = 0) ?_ rfl (by decide) hr'
    intro u v huv
    unfold edgeGraph at huv
    simp at huv
  · simp at hw

/-- Vertex `2` has no incident edge, so no edge set connects `0` to `2` whatever the budget. -/
example :
    pointToPointConnectionDec
      (bitEncode ((3, [(0, 1, 1)], [(0, 2)], 5) : PointToPointConnectionInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨E', hsub, -, hr⟩ := ((accepts_encoding _).1 h).2
  have hr' := hr (0, 2) (by simp) (by decide) (by decide)
  refine not_reachable (fun v => v.val ≠ 2) ?_ (by decide) (by simp) hr'
  intro u v huv _
  unfold edgeGraph at huv
  rw [SimpleGraph.fromRel_adj] at huv
  have hes : ∀ e ∈ E'.map (fun e => (e.1, e.2.1)), e = (0, 1) := by
    intro e he
    have := (hsub.map (fun e => (e.1, e.2.1))).subset he
    simpa using this
  rcases huv.2 with h' | h'
  · have := hes _ h'
    simp only [Prod.mk.injEq] at this
    omega
  · have := hes _ h'
    simp only [Prod.mk.injEq] at this
    omega

end MetaMathlibExt.Complexity.NPComplete.PointToPointConnection
