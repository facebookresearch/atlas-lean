/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.JordanParity














namespace StatMech.Onsager.RayFlipH

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


def straddleSet (d : Fin n → Fin 4) (a b : ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun k : Fin n =>
    isVertEdge (d k) ∧ (pos d k).1 = a + 1 ∧
      min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧ b < max ((pos d k).2) ((pos d (k + 1)).2))



theorem upCross_hstep_gen (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ) :
    upCross d a b + upCross d (a + 1) b + (straddleSet d a b).card
      = 2 * (Finset.univ.filter (fun k : Fin n =>
          ¬ ((pos d k).1 = a + 1 ∧ b + 1 ≤ (pos d k).2) ∧
            ((pos d (k + 1)).1 = a + 1 ∧ b + 1 ≤ (pos d (k + 1)).2))).card := by
  classical
  set Pin : Fin n → Prop := fun k => (pos d k).1 = a + 1 ∧ b + 1 ≤ (pos d k).2 with hPin
  set g : Fin n → ℤ := fun k => if Pin k then (1 : ℤ) else 0 with hg
  have hshift : (∑ k : Fin n, g (k + 1)) = ∑ k, g k :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n)) g
  have htel : (∑ k : Fin n, (g (k + 1) - g k)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  have hper : ∀ k : Fin n, g (k + 1) - g k
      = (if (¬ Pin k ∧ Pin (k + 1)) then (1 : ℤ) else 0)
        - (if (Pin k ∧ ¬ Pin (k + 1)) then (1 : ℤ) else 0) := by
    intro k
    simp only [hg]
    by_cases h1 : Pin k <;> by_cases h2 : Pin (k + 1) <;> simp [h1, h2]
  have hentexit :
      (Finset.univ.filter (fun k : Fin n => ¬ Pin k ∧ Pin (k + 1))).card
        = (Finset.univ.filter (fun k : Fin n => Pin k ∧ ¬ Pin (k + 1))).card := by
    have hcong : (∑ k : Fin n,
          ((if (¬ Pin k ∧ Pin (k + 1)) then (1 : ℤ) else 0)
            - (if (Pin k ∧ ¬ Pin (k + 1)) then (1 : ℤ) else 0)))
        = ∑ k : Fin n, (g (k + 1) - g k) :=
      Finset.sum_congr rfl (fun k _ => (hper k).symm)
    have hsum : (∑ k : Fin n,
          ((if (¬ Pin k ∧ Pin (k + 1)) then (1 : ℤ) else 0)
            - (if (Pin k ∧ ¬ Pin (k + 1)) then (1 : ℤ) else 0))) = 0 := by
      rw [hcong]; exact htel
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, sub_eq_zero] at hsum
    exact_mod_cast hsum
  
  set L := Finset.univ.filter (fun k : Fin n => isHorizEdge (d k) ∧
    min ((pos d k).1) ((pos d (k + 1)).1) = a ∧ b < (pos d k).2) with hL
  set R := Finset.univ.filter (fun k : Fin n => isHorizEdge (d k) ∧
    min ((pos d k).1) ((pos d (k + 1)).1) = a + 1 ∧ b < (pos d k).2) with hR
  have hdisjLR : Disjoint L R := by
    rw [hL, hR, Finset.disjoint_filter]
    intro k _ hl hr; obtain ⟨_, hla, _⟩ := hl; obtain ⟨_, hra, _⟩ := hr; omega
  have hdisjLS : Disjoint L (straddleSet d a b) := by
    rw [hL, straddleSet, Finset.disjoint_filter]
    intro k _ hl hs
    exact absurd hs.1 (by have := hl.1; rcases this with h | h <;> rw [h] <;> decide)
  have hdisjRS : Disjoint R (straddleSet d a b) := by
    rw [hR, straddleSet, Finset.disjoint_filter]
    intro k _ hr hs
    exact absurd hs.1 (by have := hr.1; rcases this with h | h <;> rw [h] <;> decide)
  have hdisjEE : Disjoint
      (Finset.univ.filter (fun k : Fin n => ¬ Pin k ∧ Pin (k + 1)))
      (Finset.univ.filter (fun k : Fin n => Pin k ∧ ¬ Pin (k + 1))) := by
    rw [Finset.disjoint_filter]
    intro k _ he hx; exact absurd hx.1 he.1
  
  have hunion : (L ∪ R) ∪ straddleSet d a b
      = Finset.univ.filter (fun k : Fin n =>
          (¬ Pin k ∧ Pin (k + 1)) ∨ (Pin k ∧ ¬ Pin (k + 1))) := by
    ext k
    simp only [hL, hR, straddleSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, hPin]
    have hx := fst_step d hclosed k
    have hy := snd_step d hclosed k
    rcases stepOf_coords (d k) with ⟨hd, hs⟩ | ⟨hd, hs⟩ | ⟨hd, hs⟩ | ⟨hd, hs⟩
    · have hsx : (stepOf (d k)).1 = 1 := by rw [hs]
      have hsy : (stepOf (d k)).2 = 0 := by rw [hs]
      have hH : isHorizEdge (d k) := Or.inl hd
      have hnV : ¬ isVertEdge (d k) := by rw [hd]; decide
      simp only [hH, hnV, true_and, false_and, or_false]
      omega
    · have hsx : (stepOf (d k)).1 = 0 := by rw [hs]
      have hsy : (stepOf (d k)).2 = 1 := by rw [hs]
      have hnH : ¬ isHorizEdge (d k) := by rw [hd]; decide
      have hV : isVertEdge (d k) := Or.inl hd
      simp only [hnH, hV, false_and, false_or, true_and]
      omega
    · have hsx : (stepOf (d k)).1 = -1 := by rw [hs]
      have hsy : (stepOf (d k)).2 = 0 := by rw [hs]
      have hH : isHorizEdge (d k) := Or.inr hd
      have hnV : ¬ isVertEdge (d k) := by rw [hd]; decide
      simp only [hH, hnV, true_and, false_and, or_false]
      omega
    · have hsx : (stepOf (d k)).1 = 0 := by rw [hs]
      have hsy : (stepOf (d k)).2 = -1 := by rw [hs]
      have hnH : ¬ isHorizEdge (d k) := by rw [hd]; decide
      have hV : isVertEdge (d k) := Or.inr hd
      simp only [hnH, hV, false_and, false_or, true_and]
      omega
  
  have hcardU : ((L ∪ R) ∪ straddleSet d a b).card
      = L.card + R.card + (straddleSet d a b).card := by
    rw [Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_union_left]; exact ⟨hdisjLS, hdisjRS⟩),
      Finset.card_union_of_disjoint hdisjLR]
  have hcardE : (Finset.univ.filter (fun k : Fin n =>
        (¬ Pin k ∧ Pin (k + 1)) ∨ (Pin k ∧ ¬ Pin (k + 1)))).card
      = 2 * (Finset.univ.filter (fun k : Fin n => ¬ Pin k ∧ Pin (k + 1))).card := by
    rw [Finset.filter_or, Finset.card_union_of_disjoint hdisjEE, ← hentexit]; ring
  have hLc : upCross d a b = L.card := rfl
  have hRc : upCross d (a + 1) b = R.card := rfl
  rw [hLc, hRc, ← hcardU, hunion, hcardE]



theorem rayParity_hstep_gen (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ) :
    rayParity d a b + rayParity d (a + 1) b = ((straddleSet d a b).card : ZMod 2) := by
  have hsum := upCross_hstep_gen d hclosed a b
  have hcast := congrArg (fun m : ℕ => (m : ZMod 2)) hsum
  push_cast at hcast
  have h20 : (2 : ZMod 2) = 0 := by decide
  
  have hz : (upCross d a b : ZMod 2) + (upCross d (a + 1) b : ZMod 2)
      + ((straddleSet d a b).card : ZMod 2) = 0 := by
    rw [hcast, h20]; ring
  rw [rayParity, rayParity, eq_neg_of_add_eq_zero_left hz]
  exact CharTwo.neg_eq _



theorem rayParity_hflip (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ)
    (hodd : (straddleSet d a b).card % 2 = 1) :
    rayParity d a b = rayParity d (a + 1) b + 1 := by
  have hstr : ((straddleSet d a b).card : ZMod 2) = 1 := by
    have h2 : (straddleSet d a b).card = 2 * ((straddleSet d a b).card / 2) + 1 := by omega
    rw [h2]; push_cast; rw [show (2 : ZMod 2) = 0 from by decide]; ring
  have hsum := rayParity_hstep_gen d hclosed a b
  rw [hstr] at hsum
  rw [eq_sub_of_add_eq hsum, sub_eq_add_neg, CharTwo.neg_eq, add_comm]

end StatMech.Onsager.RayFlipH
