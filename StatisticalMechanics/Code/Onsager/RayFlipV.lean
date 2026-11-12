/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.JordanParity











namespace StatMech.Onsager.RayFlipV

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


def midSet (d : Fin n → Fin 4) (a b : ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun k : Fin n =>
    isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k + 1)).1) = a ∧ (pos d k).2 = b)



theorem upCross_vsplit (d : Fin n → Fin 4) (a b : ℤ) :
    upCross d a b = upCross d a (b + 1) + (midSet d a (b + 1)).card := by
  unfold upCross midSet
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hH, hm, hlt⟩
      rcases lt_or_eq_of_le (show b + 1 ≤ (pos d k).2 from by omega) with h | h
      · exact Or.inl ⟨hH, hm, h⟩
      · exact Or.inr ⟨hH, hm, h.symm⟩
    · rintro (⟨hH, hm, hlt⟩ | ⟨hH, hm, he⟩)
      · exact ⟨hH, hm, by omega⟩
      · exact ⟨hH, hm, by omega⟩
  · rw [Finset.disjoint_filter]
    rintro k _ ⟨_, _, h1⟩ ⟨_, _, h2⟩; omega



theorem rayParity_vflip (d : Fin n → Fin 4) (a b : ℤ)
    (hodd : (midSet d a (b + 1)).card % 2 = 1) :
    rayParity d a b = rayParity d a (b + 1) + 1 := by
  have hsplit := upCross_vsplit d a b
  have hmid : ((midSet d a (b + 1)).card : ZMod 2) = 1 := by
    have h2 : (midSet d a (b + 1)).card = 2 * ((midSet d a (b + 1)).card / 2) + 1 := by omega
    rw [h2]; push_cast
    rw [show (2 : ZMod 2) = 0 from by decide]; ring
  rw [rayParity, rayParity, hsplit]
  push_cast
  rw [hmid]

end StatMech.Onsager.RayFlipV
