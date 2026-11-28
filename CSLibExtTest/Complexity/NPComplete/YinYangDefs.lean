/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.YinYangDefs

namespace MetaMathlibExt.Complexity.NPComplete.YinYang

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : YinYangInstance) :
    yinYangDec (bitEncode i) = true ↔ WellFormed i ∧ YinYangFeasible i := by
  simp [yinYangDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : yinYangDec [true] = false := by
  have h : bitDecode (α := YinYangInstance) [true] = none := rfl
  simp [yinYangDec, h]

/-- An induced subgraph on a set with exactly one element is connected. -/
private theorem connected_of_unique {V : Type*} (G : SimpleGraph V) (s : Set V) (a : V)
    (ha : a ∈ s) (hs : ∀ x ∈ s, x = a) : (G.induce s).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, ⟨⟨a, ha⟩⟩⟩
  have hxy : x = y := Subtype.ext ((hs x x.2).trans (hs y y.2).symm)
  subst hxy
  rfl

/-- A black circle next to a white circle: each color is a single cell, and one row has no
two-by-two square. -/
example : yinYangDec (bitEncode ((2, [[1, 2]]) : YinYangInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, fun u => decide ((u.2 : ℕ) = 0), ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := u
    simp at ha hb
    subst ha
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp_all [entry]
  · intro u hu
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := u
    simp at ha hb
    subst ha
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp_all [entry]
  · refine connected_of_unique _ _ (⟨0, by simp⟩, ⟨0, by simp⟩) (by simp) ?_
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hx
    simp at ha hb hx
    simp [ha, hx]
  · refine connected_of_unique _ _ (⟨0, by simp⟩, ⟨1, by simp⟩) (by simp) ?_
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hx
    simp at ha hb hx
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    omega
  · intro u h₁
    simp at h₁

/-- Black circles on one diagonal of a two-by-two grid and white circles on the other are
rejected: the two black cells are not adjacent, and both their neighbours are white. -/
example : yinYangDec (bitEncode ((2, [[1, 2], [2, 1]]) : YinYangInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, black, hb, hw, hconn, -, -⟩
  have h00 : black (⟨0, by simp⟩, ⟨0, by simp⟩) = true := hb _ (by simp [entry])
  have h11 : black (⟨1, by simp⟩, ⟨1, by simp⟩) = true := hb _ (by simp [entry])
  have h01 : black (⟨0, by simp⟩, ⟨1, by simp⟩) = false := hw _ (by simp [entry])
  have h10 : black (⟨1, by simp⟩, ⟨0, by simp⟩) = false := hw _ (by simp [entry])
  obtain ⟨p⟩ := hconn.preconnected ⟨_, h00⟩ ⟨_, h11⟩
  cases p with
  | @cons _ z _ h _ =>
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb'⟩⟩, hz⟩ := z
    simp only [SimpleGraph.comap_adj, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj] at h
    simp at ha hb' hz h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Bool.noConfusion (hz.symm.trans h10)
    · exact Bool.noConfusion (hz.symm.trans h01)

/-- The rejected instance is well formed, so the rejection comes from connectivity. -/
example : WellFormed ((2, [[1, 2], [2, 1]]) : YinYangInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.YinYang
