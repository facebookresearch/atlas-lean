/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.GameTheory.PenultsOfTak

/-!
# The parity of Impartial Tic

After taking the center on an odd board, or from the empty even board, use a half-turn
reply unless a row or column can be completed immediately.
-/

namespace MetaMathlibExt

@[expose] public section

private abbrev Cell (n : ℕ) := Fin n × Fin n

private def halfTurn {n : ℕ} (p : Cell n) : Cell n := (p.1.rev, p.2.rev)

private theorem halfTurn_halfTurn {n : ℕ} (p : Cell n) : halfTurn (halfTurn p) = p := by
  simp [halfTurn]

private theorem rev_eq_self_iff {n : ℕ} (i : Fin n) : i.rev = i ↔ n = 2 * i.val + 1 := by
  have hi := i.isLt
  constructor
  · intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_rev] at hval
    omega
  · intro h
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

private theorem halfTurn_eq_self_iff {n : ℕ} (p : Cell n) :
    halfTurn p = p ↔ n = 2 * p.1.val + 1 ∧ n = 2 * p.2.val + 1 := by
  rcases p with ⟨r, c⟩
  simp only [halfTurn, Prod.mk.injEq, rev_eq_self_iff]

private theorem not_win_of_ended {n : ℕ} {S : Finset (Cell n)} (hS : ticEnded n S) :
    ¬ placementFirstPlayerWins (ticEnded n) S :=
  fun h => ((placementFirstPlayerWins_iff (ticEnded n) S).mp h).1 hS

private theorem safe_of_losing {n : ℕ} {S : Finset (Cell n)} (hS : ¬ ticEnded n S)
    (h : ¬ placementFirstPlayerWins (ticEnded n) S) (q : Cell n) :
    ¬ ticEnded n (insert q S) := by
  intro he
  by_cases hq : q ∈ S
  · exact hS (by simpa only [Finset.insert_eq_of_mem hq] using he)
  · exact h ((placementFirstPlayerWins_iff (ticEnded n) S).mpr
      ⟨hS, q, hq, not_win_of_ended he⟩)

-- A line is a fiber of either coordinate. If the reply makes a threat, it is either
-- reflected to an old threat or is on a fixed line whose last hole must be fixed.
private theorem no_new_threat {n : ℕ} (coord : Cell n → Fin n)
    (hcoord : ∀ x, coord (halfTurn x) = (coord x).rev) {U : Finset (Cell n)} {p : Cell n}
    (hclear : ∀ q i, ¬ ∀ x, coord x = i → x ∈ insert q U)
    (hsym : ∀ x ∈ insert (halfTurn p) U, halfTurn x ∈ insert (halfTurn p) U)
    (hfix : ∀ x, halfTurn x = x → x ∈ insert (halfTurn p) U) (q : Cell n) (i : Fin n) :
    ¬ ∀ x, coord x = i → x ∈ insert q (insert (halfTurn p) U) := by
  intro h
  by_cases hy : coord (halfTurn p) = i
  · by_cases hx : coord p = i
    · have hi : i.rev = i := by
        calc
          i.rev = (coord p).rev := congrArg Fin.rev hx.symm
          _ = coord (halfTurn p) := (hcoord p).symm
          _ = i := hy
      apply hclear (halfTurn p) i
      intro x hxi
      rcases Finset.mem_insert.mp (h x hxi) with he | hxT
      · subst x
        have hqr : coord (halfTurn q) = i := by rw [hcoord, hxi, hi]
        rcases Finset.mem_insert.mp (h (halfTurn q) hqr) with he | hm
        · exact hfix q he
        · simpa only [halfTurn_halfTurn] using hsym (halfTurn q) hm
      · exact hxT
    · have hother : coord (halfTurn p) ≠ i.rev := by
        intro he
        apply hx
        simpa only [hcoord, Fin.rev_rev] using congrArg Fin.rev he
      apply hclear (halfTurn q) i.rev
      intro x hxi
      have hrot : coord (halfTurn x) = i := by rw [hcoord, hxi, Fin.rev_rev]
      rcases Finset.mem_insert.mp (h (halfTurn x) hrot) with he | hm
      · apply Finset.mem_insert.mpr
        exact Or.inl (by simpa only [halfTurn_halfTurn] using congrArg halfTurn he)
      · have hxT : x ∈ insert (halfTurn p) U := by
          simpa only [halfTurn_halfTurn] using hsym (halfTurn x) hm
        rcases Finset.mem_insert.mp hxT with rfl | hxU
        · exact (hother hxi).elim
        · exact Finset.mem_insert_of_mem hxU
  · apply hclear q i
    intro x hxi
    rcases Finset.mem_insert.mp (h x hxi) with rfl | hm
    · exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp hm with rfl | hxU
      · exact (hy hxi).elim
      · exact Finset.mem_insert_of_mem hxU

private theorem safe_reply {n : ℕ} {U : Finset (Cell n)} {p : Cell n}
    (hclear : ∀ q, ¬ ticEnded n (insert q U))
    (hsym : ∀ x ∈ insert (halfTurn p) U, halfTurn x ∈ insert (halfTurn p) U)
    (hfix : ∀ x, halfTurn x = x → x ∈ insert (halfTurn p) U) (q : Cell n) :
    ¬ ticEnded n (insert q (insert (halfTurn p) U)) := by
  rintro (⟨i, hi⟩ | ⟨i, hi⟩)
  · apply no_new_threat Prod.fst (fun _ => rfl)
      (fun x r hr => hclear x (Or.inl ⟨r, fun c => hr (r, c) rfl⟩)) hsym hfix q i
    rintro ⟨r, c⟩ (rfl : r = i)
    exact hi c
  · apply no_new_threat Prod.snd (fun _ => rfl)
      (fun x c hc => hclear x (Or.inr ⟨c, fun r => hc (r, c) rfl⟩)) hsym hfix q i
    rintro ⟨r, c⟩ (rfl : c = i)
    exact hi r

private theorem symmetric_losing {n : ℕ} (S : Finset (Cell n))
    (hsym : ∀ x ∈ S, halfTurn x ∈ S) (hfix : ∀ x, halfTurn x = x → x ∈ S)
    (hsafe : ∀ p, ¬ ticEnded n (insert p S)) : ¬ placementFirstPlayerWins (ticEnded n) S := by
  intro h
  obtain ⟨_, p, hp, hl⟩ := (placementFirstPlayerWins_iff (ticEnded n) S).mp h
  have hpm : halfTurn p ∉ insert p S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun he => hp (hfix p he), fun hm => hp (halfTurn_halfTurn p ▸ hsym _ hm)⟩
  let T := insert (halfTurn p) (insert p S)
  have hsymT : ∀ x ∈ T, halfTurn x ∈ T := by
    intro x hx
    simp only [T, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | rfl | hx
    · exact Or.inr (Or.inl (halfTurn_halfTurn p))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hsym x hx))
  have hfixT : ∀ x, halfTurn x = x → x ∈ T := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfix x hx))
  have hclear := safe_of_losing (hsafe p) hl
  have hlose : ¬ placementFirstPlayerWins (ticEnded n) T :=
    symmetric_losing T hsymT hfixT (safe_reply hclear hsymT hfixT)
  exact hl ((placementFirstPlayerWins_iff (ticEnded n) (insert p S)).mpr
    ⟨hsafe p, halfTurn p, hpm, hlose⟩)
termination_by Fintype.card (Cell n) - S.card
decreasing_by
  have hc := Finset.card_insert_of_notMem hp
  have hc' := Finset.card_insert_of_notMem hpm
  have hlt := Finset.card_lt_univ_of_notMem hp
  simp only [Cell] at *
  omega

private theorem size_le_of_ended {n : ℕ} {S : Finset (Cell n)} (hS : ticEnded n S) :
    n ≤ S.card := by
  rcases hS with ⟨r, hr⟩ | ⟨c, hc⟩
  · let e : Fin n ↪ Cell n := ⟨fun c => (r, c), fun _ _ h => congrArg Prod.snd h⟩
    have hsub : Finset.univ.map e ⊆ S := by
      intro p hp
      obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hp
      exact hr c
    simpa using Finset.card_le_card hsub
  · let e : Fin n ↪ Cell n := ⟨fun r => (r, c), fun _ _ h => congrArg Prod.fst h⟩
    have hsub : Finset.univ.map e ⊆ S := by
      intro p hp
      obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hp
      exact hc r
    simpa using Finset.card_le_card hsub

/-- **The first player wins Impartial Tic exactly on odd boards.** For every natural number $n$,
under normal play the first player wins Impartial Tic on the $n \times n$ board, starting from the
empty board, if and only if $n$ is odd; for even $n$ the second player wins.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 1 (`integers-2025-G1-prop-1`). -/
public theorem impartialTic_firstPlayerWins_iff_odd (n : ℕ) :
    placementFirstPlayerWins (ticEnded n) ∅ ↔ Odd n := by
  constructor
  · intro h
    by_contra hodd
    obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
    apply symmetric_losing (n := n) ∅ (by simp) _ _ h
    · intro p hp
      have he := (halfTurn_eq_self_iff p).mp hp |>.1
      omega
    · intro p hp
      have hn := size_le_of_ended hp
      have hp' := p.1.isLt
      simp only [Finset.card_insert_of_notMem (Finset.notMem_empty _), Finset.card_empty] at hn
      omega
  · rintro ⟨k, hk⟩
    let c : Fin n := ⟨k, by omega⟩
    let center : Cell n := (c, c)
    refine (placementFirstPlayerWins_iff (ticEnded n) ∅).mpr
      ⟨not_ticEnded_empty (by omega), center, Finset.notMem_empty _, ?_⟩
    by_cases hn1 : n = 1
    · apply not_win_of_ended
      refine Or.inl ⟨c, fun j => ?_⟩
      have hj : j = c := by
        apply Fin.ext
        change j.val = k
        have hb := j.isLt
        omega
      rw [hj]
      exact Finset.mem_insert_self _ _
    · apply symmetric_losing (insert center ∅)
      · intro x hx
        have hc : c.rev = c := (rev_eq_self_iff c).mpr (by change n = 2 * k + 1; omega)
        have hx' : x = center := (Finset.mem_insert.mp hx).resolve_right (Finset.notMem_empty _)
        rw [hx']
        apply Finset.mem_insert.mpr
        exact Or.inl (by simp only [center, halfTurn, hc])
      · intro x hx
        obtain ⟨h1, h2⟩ := (halfTurn_eq_self_iff x).mp hx
        have he : x = center := Prod.ext (Fin.ext (by change x.1.val = k; omega))
          (Fin.ext (by change x.2.val = k; omega))
        exact Finset.mem_insert.mpr (Or.inl he)
      · intro q hq
        have hsize := size_le_of_ended hq
        have hcard := Finset.card_insert_le (a := q) (s := insert center ∅)
        simp only [Finset.card_insert_of_notMem (Finset.notMem_empty _), Finset.card_empty] at hcard
        omega

end

end MetaMathlibExt
