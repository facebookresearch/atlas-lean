/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.VertexMinMaxMulticenterDefs
import Mathlib.Tactic.FinCases

namespace MetaMathlibExt.Complexity.NPComplete.VertexMinMaxMulticenter

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MinMaxMulticenter (MinMaxMulticenterInstance Graph walkLength weight edgeLength)

private theorem accepts_encoding (i : MinMaxMulticenterInstance) :
    vertexMinMaxMulticenterDec (bitEncode i) = true ↔
      MinMaxMulticenter.WellFormed i ∧ VertexMinMaxMulticenterFeasible i := by
  simp [vertexMinMaxMulticenterDec, bitDecode_bitEncode]

/-- A walk between distinct vertices has length at least the smallest length of its edges. -/
private theorem le_walkLength {i : MinMaxMulticenterInstance} {c : ℕ}
    (hc : ∀ e ∈ (Graph i).edgeSet, c ≤ edgeLength i e) {u v : Fin i.1} (huv : u ≠ v)
    (W : (Graph i).Walk u v) : c ≤ walkLength i W := by
  cases W with
  | nil => exact absurd rfl huv
  | cons h W' =>
    have := hc _ ((SimpleGraph.mem_edgeSet _).2 h)
    simp only [walkLength, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
    omega

/-- There is no walk between distinct vertices of an edgeless graph. -/
private theorem no_walk {i : MinMaxMulticenterInstance} (hno : ∀ a b, ¬ (Graph i).Adj a b)
    {u v : Fin i.1} (huv : u ≠ v) (W : (Graph i).Walk u v) : False := by
  cases W with
  | nil => exact huv rfl
  | cons h _ => exact hno _ _ h

/-- A lone continuation bit is a truncated instance encoding. -/
example : vertexMinMaxMulticenterDec [true] = false := by
  have h : bitDecode (α := MinMaxMulticenterInstance) [true] = none := rfl
  simp [vertexMinMaxMulticenterDec, h]

/-- A center at vertex `0` serves vertex `1` across the edge of length one, within the bound
`1 / 1`. -/
example :
    vertexMinMaxMulticenterDec
      (bitEncode ((2, [(0, 1, 1)], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance)) =
        true := by
  apply (accepts_encoding _).2
  have hadj : (Graph ((2, [(0, 1, 1)], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance)).Adj
      ⟨1, by decide⟩ ⟨0, by decide⟩ := by
    unfold Graph Cslib.Complexity.Karp.edgeGraph
    simp only [SimpleGraph.fromRel_adj]
    decide
  refine ⟨by unfold MinMaxMulticenter.WellFormed; decide, ({0} : Finset (Fin 2)), by decide, ?_⟩
  intro v
  fin_cases v
  · refine ⟨⟨0, by decide⟩, by simp, .nil, ?_⟩
    simp [walkLength]
  · refine ⟨⟨0, by decide⟩, by simp, .cons hadj .nil, ?_⟩
    have he : edgeLength ((2, [(0, 1, 1)], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance)
        s((1 : Fin 2), 0) = 1 := by decide
    have hw : ∀ v, weight ((2, [(0, 1, 1)], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance) v =
        1 := by decide
    simp [walkLength, he, hw]

/-- Without edges, one center cannot reach the other vertex. -/
example :
    vertexMinMaxMulticenterDec
      (bitEncode ((2, [], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨P, hcard, hP⟩ := ((accepts_encoding _).1 h).2
  obtain ⟨p₀, hp₀, W₀, -⟩ := hP ⟨0, by decide⟩
  obtain ⟨p₁, hp₁, W₁, -⟩ := hP ⟨1, by decide⟩
  have hp : p₀ = p₁ := Finset.card_le_one.1 hcard p₀ hp₀ p₁ hp₁
  subst hp
  have hno :
      ∀ a b, ¬ (Graph ((2, [], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance)).Adj a b := by
    intro a b hab
    simp [Graph, Cslib.Complexity.Karp.edgeGraph] at hab
  by_cases h₀ : p₀ = ⟨0, by decide⟩
  · subst h₀
    exact no_walk hno (by decide) W₁
  · exact no_walk hno (Ne.symm h₀) W₀

/-- Vertex `1` sits across an edge of length three, so serving it from a center at `0` costs
three, above the bound `1 / 1`, and symmetrically for a center at `1`. -/
example :
    vertexMinMaxMulticenterDec
      (bitEncode ((2, [(0, 1, 3)], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance)) =
        false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨P, hcard, hP⟩ := ((accepts_encoding _).1 h).2
  obtain ⟨p₀, hp₀, W₀, h₀⟩ := hP ⟨0, by decide⟩
  obtain ⟨p₁, hp₁, W₁, h₁⟩ := hP ⟨1, by decide⟩
  have hp : p₀ = p₁ := Finset.card_le_one.1 hcard p₀ hp₀ p₁ hp₁
  subst hp
  have hc : ∀ e ∈
      (Graph ((2, [(0, 1, 3)], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance)).edgeSet,
      3 ≤ edgeLength _ e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet] at he
      revert he
      revert a b
      unfold Graph Cslib.Complexity.Karp.edgeGraph edgeLength
      simp only [SimpleGraph.fromRel_adj]
      decide
  have hw : ∀ v, weight ((2, [(0, 1, 3)], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance) v =
      1 := by
    decide
  by_cases e₀ : p₀ = ⟨0, by decide⟩
  · subst e₀
    have := le_walkLength hc (by decide) W₁
    rw [hw] at h₁
    norm_num at h₁
    omega
  · have := le_walkLength hc (Ne.symm e₀) W₀
    rw [hw] at h₀
    norm_num at h₀
    omega

/-- A bound `K` above the number of vertices is malformed. -/
example :
    vertexMinMaxMulticenterDec
      (bitEncode ((2, [(0, 1, 1)], [1, 1], 3, (1, 1)) : MinMaxMulticenterInstance)) =
        false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1
  revert hw
  unfold MinMaxMulticenter.WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.VertexMinMaxMulticenter
