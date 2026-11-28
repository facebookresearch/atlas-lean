/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HypergraphPlanarSupportDefs

namespace MetaMathlibExt.Complexity.NPComplete.HypergraphPlanarSupport

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HypergraphPlanarSupportInstance) :
    hypergraphPlanarSupportDec (bitEncode i) = true ↔
      WellFormed i ∧ HypergraphPlanarSupportFeasible i := by
  simp [hypergraphPlanarSupportDec, bitDecode_bitEncode]

/-- The graph on `Fin 3` with the single edge `0 - 1`. -/
private abbrev edge01 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun a b => a.val = 0 ∧ b.val = 1

private theorem pair_of_adj {v w : Fin 3} (h : edge01.Adj v w) :
    ({v, w} : Set (Fin 3)) = {0, 1} := by
  simp only [SimpleGraph.fromRel_adj] at h
  rcases h with ⟨-, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
  · rw [show v = 0 from Fin.ext h₁, show w = 1 from Fin.ext h₂]
  · rw [show v = 1 from Fin.ext h₂, show w = 0 from Fin.ext h₁, Set.pair_comm]

/-- A one-edge graph is drawn on the `x`-axis; with a single edge there is no pair of distinct
edges to check. -/
private theorem edge01_planar : edge01.IsPlanar := by
  refine Or.inr ⟨fun v => (((v : ℕ) : ℝ), 0), ?_, ?_, ?_⟩
  · intro a b h
    simp only [Prod.mk.injEq, and_true, Nat.cast_inj] at h
    exact Fin.ext h
  · intro v w h hf
    simp only [Prod.mk.injEq, and_true, Nat.cast_inj] at hf
    exact h.ne (Fin.ext hf)
  · intro v w x y hvw hxy hne
    exact absurd ((pair_of_adj hvw).trans (pair_of_adj hxy).symm) hne

/-- A lone continuation bit is a truncated instance encoding. -/
example : hypergraphPlanarSupportDec [true] = false := by
  have h : bitDecode (α := HypergraphPlanarSupportInstance) [true] = none := rfl
  simp [hypergraphPlanarSupportDec, h]

/-- On three vertices with hyperedges `{0, 1}` and `{2}`, the planar graph with the single edge
`0 - 1` is a support. -/
example :
    hypergraphPlanarSupportDec
      (bitEncode ((3, [[0, 1], [2]]) : HypergraphPlanarSupportInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, edge01, edge01_planar, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  rcases hc with rfl | rfl
  · refine ⟨⟨0, by simp [hyperedgeSet]⟩, fun ⟨w, hw⟩ => ?_⟩
    simp only [hyperedgeSet, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with hw | hw
    · obtain rfl : w = 0 := Fin.ext hw
      exact SimpleGraph.Reachable.refl _
    · obtain rfl : w = 1 := Fin.ext hw
      exact SimpleGraph.Adj.reachable (by simp)
  · refine ⟨⟨2, by simp [hyperedgeSet]⟩, fun ⟨w, hw⟩ => ?_⟩
    simp only [hyperedgeSet, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    obtain rfl : w = 2 := Fin.ext hw
    exact SimpleGraph.Reachable.refl _

/-- The hyperedge `{0, 2}` names a vertex outside `Fin 2`. Read as a vertex set it is just `{0}`,
which every graph supports, so only well-formedness rejects this encoding. -/
example :
    hypergraphPlanarSupportDec (bitEncode ((2, [[0, 2]]) : HypergraphPlanarSupportInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro hacc
  have hwf := ((accepts_encoding _).1 hacc).1
  revert hwf
  unfold WellFormed
  decide

/-- The out-of-range instance above does satisfy the support predicate itself, witnessed by the
empty graph. -/
example : HypergraphPlanarSupportFeasible ((2, [[0, 2]]) : HypergraphPlanarSupportInstance) := by
  refine ⟨⊥, Or.inr ⟨fun v => (((v : ℕ) : ℝ), 0), ?_, fun _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩,
    ?_⟩
  · intro a b h
    simp only [Prod.mk.injEq, and_true, Nat.cast_inj] at h
    exact Fin.ext h
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨0, by simp [hyperedgeSet]⟩, fun ⟨w, hw⟩ => ?_⟩
    simp only [hyperedgeSet, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with hw | hw
    · obtain rfl : w = 0 := Fin.ext hw
      exact SimpleGraph.Reachable.refl _
    · exact absurd w.isLt (by omega)

end MetaMathlibExt.Complexity.NPComplete.HypergraphPlanarSupport
