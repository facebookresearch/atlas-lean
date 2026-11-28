/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords

/-!
# The relative position function determines a binary word

`eq_iff_relativePosition_eq` shows that two binary words in which both letters occur infinitely
often are equal exactly when their relative position functions agree.
-/

namespace MetaMathlibExt

namespace eq_iff_relativePosition_eq

-- If two words agree before position m, and m is their first difference (a in the first word,
-- b in the second), then their relative position functions differ: compare them at the
-- occurrence after the counts of a and of b, whichever is smaller, before position m.
private theorem false_of_first_diff {w w' : ℕ → Bool} (hw : BothLettersInfinite w)
    (hw' : BothLettersInfinite w')
    (h : ∀ n, 1 ≤ n → relativePosition w n = relativePosition w' n) {m : ℕ}
    (hlt : ∀ i < m, w i = w' i) (ha : w m = true) (hb : w' m = false) : False := by
  have inf {v : ℕ → Bool} (hv : BothLettersInfinite v) (α : Bool) : {i | v i = α}.Infinite := by
    cases α
    · exact hv.2
    · exact hv.1
  -- Both words have the same number of each letter before every position `j ≤ m`.
  have count_eq (α : Bool) {j : ℕ} (hj : j ≤ m) :
      Nat.count (fun i => w' i = α) j = Nat.count (fun i => w i = α) j := by
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    refine Finset.filter_congr fun i hi => ?_
    rw [hlt i (by simp at hi; omega)]
  -- The occurrences of a letter before position `m` sit at the same positions in both words.
  have nth_eq (α : Bool) {k : ℕ} (hk : k < Nat.count (fun i => w i = α) m) :
      Nat.nth (fun i => w' i = α) k = Nat.nth (fun i => w i = α) k := by
    have him : Nat.nth (fun i => w i = α) k < m := Nat.nth_lt_of_lt_count hk
    have hwi : w (Nat.nth (fun i => w i = α) k) = α := Nat.nth_mem_of_infinite (inf hw α) k
    have hci := Nat.count_nth_of_infinite (inf hw α) k
    conv_lhs => rw [← hci, ← count_eq α him.le]
    exact Nat.nth_count ((hlt _ him).symm.trans hwi)
  -- The next occurrence of a letter other than the one at position `m` comes after `m`.
  have next_gt {v : ℕ → Bool} (hv : BothLettersInfinite v) {α : Bool} (hm : v m ≠ α) :
      m < Nat.nth (fun i => v i = α) (Nat.count (fun i => v i = α) m) := by
    refine lt_of_le_of_ne (Nat.le_nth_count (inf hv α) m) fun heq => hm ?_
    have := Nat.nth_mem_of_infinite (inf hv α) (Nat.count (fun i => v i = α) m)
    rwa [← heq] at this
  have pa : Nat.nth (fun i => w i = true) (Nat.count (fun i => w i = true) m) = m :=
    Nat.nth_count ha
  have pb' : Nat.nth (fun i => w' i = false) (Nat.count (fun i => w i = false) m) = m := by
    rw [← count_eq false le_rfl]
    exact Nat.nth_count hb
  have pb := next_gt hw (α := false) (by simp [ha])
  have pa' := next_gt hw' (α := true) (by simp [hb])
  rw [count_eq true le_rfl] at pa'
  have hr (k : ℕ) := h (k + 1) (by omega)
  simp only [relativePosition, letterPosition, Nat.add_sub_cancel] at hr
  rcases lt_trichotomy (Nat.count (fun i => w i = true) m)
      (Nat.count (fun i => w i = false) m) with hab | hab | hab
  · have := hr (Nat.count (fun i => w i = true) m)
    rw [nth_eq false hab, pa] at this
    omega
  · have := hr (Nat.count (fun i => w i = true) m)
    rw [pa] at this
    rw [hab] at this pa'
    rw [pb'] at this
    omega
  · have := hr (Nat.count (fun i => w i = false) m)
    rw [nth_eq true hab, pb'] at this
    omega

end eq_iff_relativePosition_eq

/-- **The relative position function determines the word.** Let $w$ and $w'$ be infinite words
over the letters $a$ and $b$ in each of which both letters occur infinitely often, and let $r_w$
and $r_{w'}$ be their relative position functions. Then $w = w'$ if and only if
$r_w(n) = r_{w'}(n)$ for every $n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 5
(`jis-2025-25.1.5-lem-5`). -/
public theorem eq_iff_relativePosition_eq {w w' : ℕ → Bool} (hw : BothLettersInfinite w)
    (hw' : BothLettersInfinite w') :
    w = w' ↔ ∀ n, 1 ≤ n → relativePosition w n = relativePosition w' n := by
  refine ⟨fun h _ _ => h ▸ rfl, fun h => funext fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases hwm : w m <;> cases hwm' : w' m
    · rfl
    · exact (eq_iff_relativePosition_eq.false_of_first_diff hw' hw (fun n hn => (h n hn).symm)
        (fun i hi => (ih i hi).symm) hwm' hwm).elim
    · exact (eq_iff_relativePosition_eq.false_of_first_diff hw hw' h ih hwm hwm').elim
    · rfl

end MetaMathlibExt
