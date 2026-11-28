/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BiconnectivityAugmentationDefs

namespace MetaMathlibExt.Complexity.NPComplete.BiconnectivityAugmentation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Complexity.Karp (edgeGraph)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : BiconnectivityAugmentationInstance) :
    biconnectivityAugmentationDec (bitEncode i) = true ↔
      WellFormed i ∧ BiconnectivityAugmentationFeasible i := by
  simp [biconnectivityAugmentationDec, bitDecode_bitEncode]

/-- The weights `w({0, 1}) = w({1, 2}) = 1` and `w({0, 2}) = 2`. -/
private abbrev W : List (List ℕ) := [[0, 1, 2], [1, 0, 1], [2, 1, 0]]

/-- The path `0 - 1 - 2` with the weights `W` and budget `B`. -/
private abbrev path3 (B : ℕ) : BiconnectivityAugmentationInstance := (3, [(0, 1), (1, 2)], W, B)

example : WellFormed (path3 1) := by unfold WellFormed; decide

example : WellFormed (path3 2) := by unfold WellFormed; decide

/-- A graph on three vertices in which every two distinct vertices are adjacent is
2-vertex-connected: deleting at most one vertex leaves a nonempty complete graph. -/
private theorem complete_isVertexConnected_two (G : SimpleGraph (Fin 3))
    (hG : ∀ u v : Fin 3, u ≠ v → G.Adj u v) : G.IsVertexConnected 2 := by
  refine ⟨by simp, fun S hS => ?_⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ?_⟩
  · by_cases huv : u = v
    · subst huv; rfl
    · exact SimpleGraph.Adj.reachable (by simpa using hG u v (fun h => huv (Subtype.ext h)))
  · by_contra hne
    have hall : ∀ v, v ∈ S := fun v => by
      by_contra hv
      exact hne ⟨⟨v, hv⟩⟩
    have : S = Finset.univ := Finset.eq_univ_of_forall hall
    subst this
    simp at hS

/-- Yes-instance: adding `{0, 2}` (weight `2`) closes the path into a biconnected triangle. -/
example : biconnectivityAugmentationDec (bitEncode (path3 2)) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, [(0, 2)], by decide, by decide,
    complete_isVertexConnected_two _ ?_⟩
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

/-- With budget `1` the vertex `1` stays a cut vertex. -/
private theorem path3_one_not_feasible :
    ¬ BiconnectivityAugmentationFeasible (path3 1) := by
  rintro ⟨E', hE, hw, -, hc⟩
  have hE' := path3_one_added hE hw
  have h1 := hc {1} (by simp)
  let G := edgeGraph 3 ([(0, 1), (1, 2)] ++ E')
  have stays : ∀ {u v : ((({1} : Finset (Fin 3)) : Set (Fin 3))ᶜ : Set (Fin 3))},
      (G.induce _).Walk u v → (u : Fin 3) = 0 → (v : Fin 3) = 0 := by
    intro u v q
    induction q with
    | nil => exact id
    | @cons a b _ h _ ih =>
      intro ha
      have hab : G.Adj a b := by simpa using h
      rw [ha] at hab
      have hb := b.2
      simp [adj_zero hE' _ hab] at hb
  obtain ⟨p⟩ := h1.preconnected ⟨0, by simp⟩ ⟨2, by simp⟩
  exact absurd (stays p rfl) (by decide)

/-- No-instance: well formed, but every edge set within budget `1` leaves the cut vertex `1`. -/
example : biconnectivityAugmentationDec (bitEncode (path3 1)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => path3_one_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: an asymmetric weight matrix is rejected, although adding `{0, 2}` at its listed
weight `2` would be within budget. -/
example : biconnectivityAugmentationDec (bitEncode
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
example : biconnectivityAugmentationDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BiconnectivityAugmentation
