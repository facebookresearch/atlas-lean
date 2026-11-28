/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.PlanarThreeDimensionalMatchingDefs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeDimensionalMatching

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching
  (ThreeDimensionalMatchingInstance ThreeDimensionalMatchingFeasible)

private theorem accepts_encoding (i : ThreeDimensionalMatchingInstance) :
    planarThreeDimensionalMatchingDec (bitEncode i) = true ↔
      WellFormed i ∧ PlanarThreeDimensionalMatchingFeasible i := by
  simp [planarThreeDimensionalMatchingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : planarThreeDimensionalMatchingDec [true] = false := by
  have h : bitDecode (α := ThreeDimensionalMatchingInstance) [true] = none := rfl
  simp [planarThreeDimensionalMatchingDec, h]

/-- The incidence graph of the single triple `(0, 0, 0)` is a star: the triple vertex `3` is
adjacent to exactly the three element vertices. -/
private theorem star_adj (u v : Fin 4) :
    (incidenceGraph ((1, [(0, 0, 0)]) : ThreeDimensionalMatchingInstance)).Adj u v ↔
      (u = 3 ∧ v ≠ 3) ∨ (v = 3 ∧ u ≠ 3) := by
  unfold incidenceGraph
  simp only [SimpleGraph.fromRel_adj]
  revert u v
  decide

/-- The star is drawn with its center at the origin and its leaves on three different rays. -/
private theorem star_isPlanar :
    (incidenceGraph ((1, [(0, 0, 0)]) : ThreeDimensionalMatchingInstance)).IsPlanar := by
  right
  refine ⟨![(1, 0), (0, 1), (-1, 0), (0, 0)], ?_, ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all <;> linarith
  · intro v w h
    rw [star_adj] at h
    fin_cases v <;> fin_cases w <;> simp_all
  · intro v w x y h₁ h₂ hne p hp
    rw [star_adj] at h₁ h₂
    obtain ⟨⟨t, ht₀, ht₁, hx, hy⟩, ⟨s, hs₀, hs₁, hx', hy'⟩⟩ := hp
    fin_cases v <;> fin_cases w <;> fin_cases x <;> fin_cases y <;>
      simp at h₁ h₂ hx hy hx' hy' ⊢ <;>
      first
      | exact absurd rfl hne
      | exact absurd (Set.pair_comm _ _) hne
      | (have e₁ : p.1 = 0 := by linarith
         have e₂ : p.2 = 0 := by linarith
         have e : p = (0, 0) := Prod.ext e₁ e₂
         simp [e])

/-- The single triple `(0, 0, 0)` is a perfect matching for part size one, and its star-shaped
incidence graph is planar. -/
example :
    planarThreeDimensionalMatchingDec
      (bitEncode ((1, [(0, 0, 0)]) : ThreeDimensionalMatchingInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨⟨by unfold ThreeDimensionalMatching.WellFormed; decide, by decide, star_isPlanar⟩,
    [(0, 0, 0)], by decide, by decide, ?_, ?_, ?_⟩ <;>
  · intro a ha
    obtain rfl : a = 0 := by omega
    exact ⟨(0, 0, 0), by simp, fun t ht => by simpa using ht.1⟩

/-- Without triples there is no matching of size one. -/
example :
    planarThreeDimensionalMatchingDec
      (bitEncode ((1, []) : ThreeDimensionalMatchingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨M, hM, hlen, -⟩ := ((accepts_encoding _).1 h).2
  rw [List.sublist_nil.1 hM] at hlen
  simp at hlen

/-- Listing the triple `(0, 0, 0)` twice is malformed, although it contains a matching. -/
example :
    planarThreeDimensionalMatchingDec
      (bitEncode ((1, [(0, 0, 0), (0, 0, 0)]) : ThreeDimensionalMatchingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2.1
  revert hw
  decide

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeDimensionalMatching
