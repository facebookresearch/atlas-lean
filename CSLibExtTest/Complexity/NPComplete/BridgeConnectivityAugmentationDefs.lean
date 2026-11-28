/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BridgeConnectivityAugmentationDefs

namespace MetaMathlibExt.Complexity.NPComplete.BridgeConnectivityAugmentation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open BiconnectivityAugmentation (BiconnectivityAugmentationInstance weight)
open Cslib.Complexity.Karp (edgeGraph)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : BiconnectivityAugmentationInstance) :
    bridgeConnectivityAugmentationDec (bitEncode i) = true ↔
      WellFormed i ∧ BridgeConnectivityAugmentationFeasible i := by
  simp [bridgeConnectivityAugmentationDec, bitDecode_bitEncode]

/-- The weights `w({0, 1}) = w({1, 2}) = 1` and `w({0, 2}) = 2`. -/
private abbrev W : List (List ℕ) := [[0, 1, 2], [1, 0, 1], [2, 1, 0]]

/-- The path `0 - 1 - 2` with the weights `W` and budget `B`. -/
private abbrev path3 (B : ℕ) : BiconnectivityAugmentationInstance := (3, [(0, 1), (1, 2)], W, B)

example : WellFormed (path3 1) := by unfold WellFormed; decide

example : WellFormed (path3 2) := by unfold WellFormed; decide

/-- A graph on three vertices in which every two distinct vertices are adjacent has no bridge. -/
private theorem complete_isEdgeConnected_two (G : SimpleGraph (Fin 3))
    (hG : ∀ u v : Fin 3, u ≠ v → G.Adj u v) : G.IsEdgeConnected 2 := by
  rw [SimpleGraph.isEdgeConnected_two_iff_forall_preconnected]
  intro e u v
  have step : ∀ a b : Fin 3, a ≠ b → s(a, b) ≠ e → (G.deleteEdges {e}).Reachable a b :=
    fun a b hab he => SimpleGraph.Adj.reachable (by simp [hG a b hab, he])
  by_cases huv : u = v
  · subst huv; rfl
  by_cases he : s(u, v) = e
  · have third : ∀ u v : Fin 3, u ≠ v → ∃ w : Fin 3, w ≠ u ∧ w ≠ v := by decide
    obtain ⟨w, hwu, hwv⟩ := third u v huv
    subst he
    exact (step u w (Ne.symm hwu) (by simp [hwv, huv])).trans
      (step w v hwv (by simp [hwu, hwv]))
  · exact step u v huv he

/-- Yes-instance: adding `{0, 2}` (weight `2`) closes the path into a triangle. -/
example : bridgeConnectivityAugmentationDec (bitEncode (path3 2)) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, [(0, 2)], by decide, by decide,
    complete_isEdgeConnected_two _ ?_⟩
  intro u v huv
  fin_cases u <;> fin_cases v <;> simp [edgeGraph] at huv ⊢

/-- A member of a list of naturals is at most its sum. -/
private theorem le_sum_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

/-- With budget `1` only the existing edges `{0, 1}` and `{1, 2}` can be added. -/
private theorem path3_one_added {E' : List (ℕ × ℕ)}
    (hE : ∀ e ∈ E', e.1 < 3 ∧ e.2 < 3 ∧ e.1 ≠ e.2)
    (hw : (E'.map fun e => weight W e.1 e.2).sum ≤ 1) :
    ∀ e ∈ E', e ∈ [(0, 1), (1, 0), (1, 2), (2, 1)] := by
  have key : ∀ a b : Fin 3, (a : ℕ) ≠ b → weight W a b ≤ 1 →
      ((a : ℕ), (b : ℕ)) ∈ [(0, 1), (1, 0), (1, 2), (2, 1)] := by decide
  intro e he
  obtain ⟨h1, h2, h3⟩ := hE e he
  exact key ⟨e.1, h1⟩ ⟨e.2, h2⟩ h3 ((le_sum_of_mem (List.mem_map.2 ⟨e, he, rfl⟩)).trans hw)

/-- In the path with such edges added, the only neighbour of `0` is `1`. -/
private theorem adj_zero {E' : List (ℕ × ℕ)}
    (hE : ∀ e ∈ E', e ∈ [(0, 1), (1, 0), (1, 2), (2, 1)]) (v : Fin 3)
    (h : (edgeGraph 3 ([(0, 1), (1, 2)] ++ E')).Adj 0 v) : v = 1 := by
  have sub : ∀ x ∈ [(0, 1), (1, 2)] ++ E', x ∈ [(0, 1), (1, 0), (1, 2), (2, 1)] := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide
    · exact hE x hx
  simp only [edgeGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, h⟩ := h
  have hL := h.imp (sub _) (sub _)
  clear h
  revert hL hne
  revert v
  decide

/-- With budget `1` the path keeps the bridge `{0, 1}`. -/
private theorem path3_one_not_feasible :
    ¬ BridgeConnectivityAugmentationFeasible (path3 1) := by
  rintro ⟨E', hE, hw, hc⟩
  have hE' := path3_one_added hE hw
  have hr := hc 0 1 (s := {s(0, 1)}) (by simp)
  obtain ⟨p⟩ := hr
  have stays : ∀ {u v : Fin 3},
      ((edgeGraph 3 ([(0, 1), (1, 2)] ++ E')).deleteEdges {s(0, 1)}).Walk u v →
        u = 0 → v = 0 := by
    intro u v q
    induction q with
    | nil => exact id
    | cons h _ _ =>
      rintro rfl
      rw [SimpleGraph.deleteEdges_adj] at h
      obtain ⟨h, hne⟩ := h
      exact (hne (by rw [adj_zero hE' _ h]; exact Set.mem_singleton _)).elim
  exact absurd (stays p rfl) (by decide)

/-- No-instance: well formed, but every edge set within budget `1` leaves a bridge. -/
example : bridgeConnectivityAugmentationDec (bitEncode (path3 1)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => path3_one_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: an asymmetric weight matrix is rejected, although adding `{0, 2}` at its listed
weight `2` would be within budget. -/
example : bridgeConnectivityAugmentationDec (bitEncode
    ((3, [(0, 1), (1, 2)], [[0, 1, 2], [1, 0, 1], [1, 1, 0]], 2) :
      BiconnectivityAugmentationInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := BiconnectivityAugmentationInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : bridgeConnectivityAugmentationDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BridgeConnectivityAugmentation
