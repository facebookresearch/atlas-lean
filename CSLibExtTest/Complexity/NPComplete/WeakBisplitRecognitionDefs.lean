/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.WeakBisplitRecognitionDefs

namespace MetaMathlibExt.Complexity.NPComplete.WeakBisplitRecognition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : WeakBisplitRecognitionInstance) :
    weakBisplitRecognitionDec (bitEncode i) = true ↔
      WellFormed i ∧ WeakBisplitRecognitionFeasible i := by
  simp [weakBisplitRecognitionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : weakBisplitRecognitionDec [true] = false := by
  have h : bitDecode (α := WeakBisplitRecognitionInstance) [true] = none := rfl
  simp [weakBisplitRecognitionDec, h]

/-- The triangle is weak bisplit: removing the stable set `{0}` leaves the edge `12`, a
bi-clique with sides `{1}` and `{2}`. -/
example :
    weakBisplitRecognitionDec
      (bitEncode ((3, [(0, 1), (1, 2), (0, 2)]) : WeakBisplitRecognitionInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, {0}, ?_, fun v => decide (v = 1), ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · have key : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 →
        ((Graph ((3, [(0, 1), (1, 2), (0, 2)]) : WeakBisplitRecognitionInstance)).Adj a b ↔
          decide (a = 1) ≠ decide (b = 1)) := by
      simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj]
      decide
    rintro ⟨u, hu⟩ ⟨v, hv⟩ -
    simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff] at hu hv
    exact key u v hu hv

/-- `K₄` is not weak bisplit: a stable set holds at most one vertex, and the three remaining
pairwise adjacent vertices cannot be split into two sides. -/
example :
    weakBisplitRecognitionDec
      (bitEncode ((4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]) :
        WeakBisplitRecognitionInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, X, hind, s, hs⟩
  have hadj : ∀ a b : Fin 4, a ≠ b →
      (Graph ((4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]) :
        WeakBisplitRecognitionInstance)).Adj a b := by
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj]
    decide
  have hX : ∀ a b : Fin 4, a ≠ b → a ∈ X → b ∈ X → False :=
    fun a b hab ha hb => hind ha hb hab (hadj a b hab)
  have hsplit : ∀ a b : Fin 4, a ≠ b → a ∉ X → b ∉ X → s a ≠ s b := by
    intro a b hab ha hb
    have hreach := (SimpleGraph.Adj.reachable (G := (Graph ((4, [(0, 1), (0, 2), (0, 3), (1, 2),
      (1, 3), (2, 3)]) : WeakBisplitRecognitionInstance)).induce (X : Set (Fin 4))ᶜ)
      (u := ⟨a, by simpa using ha⟩) (v := ⟨b, by simpa using hb⟩) (by simpa using hadj a b hab))
    exact (hs _ _ hreach).1 (hadj a b hab)
  have hbool : ∀ x y z : Bool, x ≠ y → x ≠ z → y ≠ z → False := by decide
  by_cases h0 : (0 : Fin 4) ∈ X
  · have h1 : (1 : Fin 4) ∉ X := fun h => hX 0 1 (by decide) h0 h
    have h2 : (2 : Fin 4) ∉ X := fun h => hX 0 2 (by decide) h0 h
    have h3 : (3 : Fin 4) ∉ X := fun h => hX 0 3 (by decide) h0 h
    exact hbool _ _ _ (hsplit 1 2 (by decide) h1 h2) (hsplit 1 3 (by decide) h1 h3)
      (hsplit 2 3 (by decide) h2 h3)
  by_cases h1 : (1 : Fin 4) ∈ X
  · have h2 : (2 : Fin 4) ∉ X := fun h => hX 1 2 (by decide) h1 h
    have h3 : (3 : Fin 4) ∉ X := fun h => hX 1 3 (by decide) h1 h
    exact hbool _ _ _ (hsplit 0 2 (by decide) h0 h2) (hsplit 0 3 (by decide) h0 h3)
      (hsplit 2 3 (by decide) h2 h3)
  by_cases h2 : (2 : Fin 4) ∈ X
  · have h3 : (3 : Fin 4) ∉ X := fun h => hX 2 3 (by decide) h2 h
    exact hbool _ _ _ (hsplit 0 1 (by decide) h0 h1) (hsplit 0 3 (by decide) h0 h3)
      (hsplit 1 3 (by decide) h1 h3)
  exact hbool _ _ _ (hsplit 0 1 (by decide) h0 h1) (hsplit 0 2 (by decide) h0 h2)
    (hsplit 1 2 (by decide) h1 h2)

/-- The rejected instance is well formed, so the rejection comes from the bisplit condition. -/
example :
    WellFormed ((4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]) :
      WeakBisplitRecognitionInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.WeakBisplitRecognition
