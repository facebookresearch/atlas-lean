/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GijswijtProperPrefixes

/-!
# Curling number of a block word with a maximal exponent

We prove that a block word whose exponents are at most $m + 1$ and at least one of
which equals $m + 1$ has curling number exactly $m + 1$, following van de Pol's
Lemma 12.
-/

namespace MetaMathlibExt.curlingNumber_blockWord_of_max

/-- Copies of a string, as a flattened list of replicates. -/
private def copies (n : ℕ) (W : List ℕ) : List ℕ :=
  (List.replicate n W).flatten

private theorem copies_length (n : ℕ) (W : List ℕ) :
    (copies n W).length = n * W.length := by
  simp [copies, List.length_flatten]

private theorem copies_add (a b : ℕ) (W : List ℕ) :
    copies (a + b) W = copies a W ++ copies b W := by
  simp only [copies, List.replicate_add, List.flatten_append]

private theorem copies_succ (n : ℕ) (W : List ℕ) :
    copies (n + 1) W = W ++ copies n W := rfl

private theorem copies_tail (W : List ℕ) (n : ℕ) : W <:+ copies (n + 1) W := by
  rw [copies_add (b := 1), show copies 1 W = W by simp [copies]]
  exact List.suffix_append (copies n W) W

private theorem copies_rotate (n : ℕ) (U V : List ℕ) :
    copies n (U ++ V) ++ U = U ++ copies n (V ++ U) := by
  induction n with
  | zero => simp [copies]
  | succ n ih =>
    rw [copies_succ, copies_succ, List.append_assoc, ih]
    simp only [List.append_assoc]

private theorem le_curling_of_copies_suffix {k : ℕ} {Y W : List ℕ} (hk : 0 < k)
    (hY : Y ≠ []) (h : copies k Y <:+ W) : k ≤ curlingNumber W := by
  have hlen := h.length_le
  rw [copies_length] at hlen
  have hy : 0 < Y.length := List.length_pos_iff.mpr hY
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hlast : Y <:+ W := (copies_tail Y p).trans h
  have hk1 : p.succ ≤ p.succ * Y.length := Nat.le_mul_of_pos_right _ hy
  have hk2 : Y.length ≤ p.succ * Y.length := Nat.le_mul_of_pos_left _ (by omega)
  unfold curlingNumber
  refine le_trans (Finset.le_sup (f := id) ?_) le_sup_left
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, Y.length, by omega, hy, hlen, ?_⟩
  have hYdrop : W.drop (W.length - Y.length) = Y :=
    (List.suffix_iff_eq_drop.mp hlast).symm
  rw [hYdrop]
  have hdrop := (List.suffix_iff_eq_drop.mp h).symm
  rw [copies_length] at hdrop
  exact hdrop

private theorem blockWord_succ (q u : ℕ) (hu : 1 ≤ u) (a : ℕ → ℕ) :
    gijswijtBlockWord q (u + 1) a =
      copies (a u) (gijswijtBlock q u) ++ gijswijtBlockWord q u a := by
  have h : u = (u - 1).succ := by omega
  unfold gijswijtBlockWord
  rw [Nat.add_sub_cancel, h, List.range_succ, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.map_cons, List.flatten_cons, Nat.succ_eq_add_one, copies]
  rw [show u - 1 + 1 = u by omega]

private theorem blockWord_split {q i : ℕ} (a : ℕ → ℕ) {u : ℕ} (hiu : i < u) :
    ∃ H, gijswijtBlockWord q u a =
      H ++ copies (a i) (gijswijtBlock q i) ++ gijswijtBlockWord q i a := by
  induction u with
  | zero => omega
  | succ u ih =>
    by_cases hiu : i = u
    · subst hiu
      by_cases hi0 : i = 0
      · subst hi0
        refine ⟨[], ?_⟩
        rw [show gijswijtBlock q 0 = [] from rfl]
        simp [gijswijtBlockWord, copies]
      · exact ⟨[], by simpa using blockWord_succ q i (by omega) a⟩
    · obtain ⟨H, hH⟩ := ih (by omega)
      exact ⟨copies (a u) (gijswijtBlock q u) ++ H, by
        rw [blockWord_succ q u (by omega) a, hH]
        simp only [List.append_assoc]⟩

end MetaMathlibExt.curlingNumber_blockWord_of_max

namespace MetaMathlibExt

/-- **Curling number of block words with a maximal exponent.** Let $m \ge 1$ and $u \ge 1$, and
let $a_1, \dots, a_{u-1} \in \{0, \dots, m+1\}$ with $a_i = m + 1$ for some $1 \le i \le u - 1$.
Writing $B_t = B_t^{(m+1)}$ for the blocks of the $(m+1)$th order Gijswijt sequence $A^{(m+1)}$,
the string $P = B_{u-1}^{a_{u-1}} \cdots B_2^{a_2} B_1^{a_1}$ has curling number
$\mathcal{C}(P) = m + 1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 12 (`jis-2025-25.4.6-lem-12`). -/
public theorem curlingNumber_blockWord_of_max {m u : ℕ} (hm : 1 ≤ m) (hu : 1 ≤ u)
    (a : ℕ → ℕ) (ha : ∀ i, 1 ≤ i → i < u → a i ≤ m + 1)
    (hmax : ∃ i, 1 ≤ i ∧ i < u ∧ a i = m + 1) :
    curlingNumber (gijswijtBlockWord (m + 1) u a) = m + 1 := by
  obtain ⟨i, hi1, hiu, hai⟩ := hmax
  have hupper : curlingNumber (gijswijtBlockWord (m + 1) u a) ≤ m + 1 := by
    have h := (gijswijtProperPrefix_curling_iff hm hu _).mpr ⟨a, ha, rfl⟩
    exact h.2.2
  have hlower : m + 1 ≤ curlingNumber (gijswijtBlockWord (m + 1) u a) := by
    let Q := gijswijtBlockWord (m + 1) i a
    have hQ := (gijswijtProperPrefix_curling_iff hm hi1 Q).mpr
      ⟨a, fun j hj1 hji => ha j hj1 (by omega), rfl⟩
    obtain ⟨R, hR⟩ := hQ.1
    obtain ⟨H, hsplit⟩ :=
      curlingNumber_blockWord_of_max.blockWord_split (q := m + 1) (i := i) a hiu
    have hRne : R ≠ [] := by
      intro hRnil
      have hlen := hQ.2.1
      rw [← hR, hRnil] at hlen
      simp at hlen
    have hYne : R ++ Q ≠ [] := by
      simp [hRne]
    have hsuffix :
        curlingNumber_blockWord_of_max.copies (m + 1) (R ++ Q) <:+
          gijswijtBlockWord (m + 1) u a := by
      have hmid :
          curlingNumber_blockWord_of_max.copies (a i) (gijswijtBlock (m + 1) i) ++ Q <:+
            gijswijtBlockWord (m + 1) u a := by
        refine ⟨H, ?_⟩
        rw [hsplit, List.append_assoc]
      rw [hai] at hmid
      have hrot :
          curlingNumber_blockWord_of_max.copies (m + 1) (gijswijtBlock (m + 1) i) ++ Q =
            Q ++ curlingNumber_blockWord_of_max.copies (m + 1) (R ++ Q) := by
        rw [← hR]
        exact curlingNumber_blockWord_of_max.copies_rotate _ Q R
      rw [hrot] at hmid
      exact (List.suffix_append Q _).trans hmid
    exact curlingNumber_blockWord_of_max.le_curling_of_copies_suffix (by omega) hYne hsuffix
  exact le_antisymm hupper hlower

end MetaMathlibExt
