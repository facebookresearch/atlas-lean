/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GijswijtSequence
import Mathlib.Data.List.Infix
import Mathlib.Data.List.TakeDrop

/-!
# Proper prefixes of Gijswijt blocks

We characterize the proper prefixes of a Gijswijt block whose curling number is
at most the order of the sequence. The proof derives the finite block recursion
at orders at least two from the curling-number recurrence, using the terminal
glue gap as in van de Bult et al., *A Slow-Growing Sequence Defined by an
Unusual Recurrence*, Section 3 (arXiv:math/0602498). The characterization then
follows by induction on the block index, as in van de Pol's Lemma 11.
-/

namespace MetaMathlibExt.gijswijtProperPrefix_curling_iff

private def copies (n : ℕ) (W : List ℕ) : List ℕ :=
  (List.replicate n W).flatten

private theorem copies_zero (W : List ℕ) : copies 0 W = [] := rfl

private theorem copies_succ (n : ℕ) (W : List ℕ) :
    copies (n + 1) W = W ++ copies n W := rfl

private theorem copies_add (a b : ℕ) (W : List ℕ) :
    copies (a + b) W = copies a W ++ copies b W := by
  simp only [copies, List.replicate_add, List.flatten_append]

private theorem copies_length (n : ℕ) (W : List ℕ) :
    (copies n W).length = n * W.length := by
  induction n with
  | zero => simp [copies_zero]
  | succ n ih => rw [copies_succ, List.length_append, ih, Nat.succ_mul, Nat.add_comm]

private theorem copies_get {n i : ℕ} {W : List ℕ} (hi : i < n * W.length) :
    (copies n W)[i]? = W[i % W.length]? := by
  induction n generalizing i with
  | zero => simp at hi
  | succ n ih =>
    rw [copies_succ]
    by_cases h : i < W.length
    · rw [List.getElem?_append_left h, Nat.mod_eq_of_lt h]
    · have hsplit : i = W.length + (i - W.length) := by omega
      rw [List.getElem?_append_right (by omega), ih, ← Nat.add_mod_left, ← hsplit]
      rw [Nat.succ_mul] at hi
      omega

private theorem copies_tail (W : List ℕ) (n : ℕ) : W <:+ copies (n + 1) W := by
  rw [copies_add (b := 1)]
  simpa only [copies_succ 0, copies_zero, List.append_nil] using List.suffix_append (copies n W) W

private theorem prefix_length (q n : ℕ) : (gijswijtPrefix q n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gijswijtPrefix, ih]

private theorem prefix_mono (q : ℕ) {n l : ℕ} (h : n ≤ l) :
    gijswijtPrefix q n <+: gijswijtPrefix q l := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | step _ ih => exact ih.trans (List.prefix_append _ _)

private theorem prefix_take (q : ℕ) {n l : ℕ} (h : n ≤ l) :
    (gijswijtPrefix q l).take n = gijswijtPrefix q n := by
  simpa only [prefix_length] using (List.prefix_iff_eq_take.mp (prefix_mono q h)).symm

private theorem eq_prefix {q n : ℕ} {W : List ℕ} (h : W <+: gijswijtPrefix q n) :
    W = gijswijtPrefix q W.length := by
  have hlen := h.length_le
  rw [prefix_length] at hlen
  rw [List.prefix_iff_eq_take.mp h, prefix_take q hlen, prefix_length]

private theorem get_of_prefix {U W : List ℕ} (h : U <+: W) {i : ℕ} (hi : i < U.length) :
    U[i]? = W[i]? := by
  obtain ⟨T, rfl⟩ := h
  exact (List.getElem?_append_left hi).symm

private theorem prefix_get (q : ℕ) {n i : ℕ} (hi : i < n) :
    (gijswijtPrefix q n)[i]? = some (max q (curlingNumber (gijswijtPrefix q i))) := by
  rw [← get_of_prefix (prefix_mono q (n := i + 1) (by omega)) (by simp [prefix_length])]
  simp [gijswijtPrefix, prefix_length]

private theorem next_eq_order {q n : ℕ} :
    gijswijtTerm q (n + 1) = q ↔ curlingNumber (gijswijtPrefix q n) ≤ q := by
  simp [gijswijtTerm, gijswijtPrefix]

private theorem mem_copies {n q : ℕ} {W : List ℕ} (h : q ∈ copies n W) : q ∈ W := by
  obtain ⟨V, hV, hq⟩ := List.mem_flatten.mp h
  exact (List.eq_of_mem_replicate hV) ▸ hq

private theorem le_curling_of_suffix {n : ℕ} {W Y : List ℕ} (hn : 0 < n) (hY : Y ≠ [])
    (h : copies n Y <:+ W) : n ≤ curlingNumber W := by
  have hlen := h.length_le
  rw [copies_length] at hlen
  have hy : 0 < Y.length := List.length_pos_iff.mpr hY
  have hle : Y.length ≤ n * Y.length := by
    simpa using Nat.mul_le_mul_right Y.length (show 1 ≤ n by omega)
  have hnk : n ≤ n * Y.length := by
    simpa using Nat.mul_le_mul_left n (show 1 ≤ Y.length by omega)
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hlast : Y <:+ W := (copies_tail Y p).trans h
  unfold curlingNumber
  refine le_trans (Finset.le_sup (f := id) ?_) le_sup_left
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, Y.length, by omega, hy, hlen, ?_⟩
  rw [← List.suffix_iff_eq_drop.mp hlast, ← copies, ← copies_length]
  exact (List.suffix_iff_eq_drop.mp h).symm

private theorem exists_copies_suffix {W : List ℕ} {b : ℕ} (hb : 1 ≤ b)
    (h : b < curlingNumber W) :
    ∃ n Y, b < n ∧ Y ≠ [] ∧ copies n Y <:+ W := by
  unfold curlingNumber at h
  have hsup := lt_of_not_ge (fun hle => h.not_ge (sup_le hle hb))
  obtain ⟨n, hn, hbn⟩ : ∃ n ∈ _, b < id n := by
    by_contra! hbound
    exact hsup.not_ge (Finset.sup_le hbound)
  change b < n at hbn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨_, d, _, hd, hnd, hdrop⟩ := hn
  refine ⟨n, W.drop (W.length - d), hbn, ?_, ?_⟩
  · have hdn : d ≤ n * d := by
      simpa using Nat.mul_le_mul_right d (show 1 ≤ n by omega)
    rw [← List.length_pos_iff, List.length_drop]
    omega
  · rw [copies, ← hdrop]
    exact List.drop_suffix _ _

private theorem can_rotate (n : ℕ) (U V : List ℕ) :
    copies n (U ++ V) ++ U = U ++ copies n (V ++ U) := by
  induction n with
  | zero => simp [copies_zero]
  | succ n ih =>
    rw [copies_succ, copies_succ, List.append_assoc, ih]
    simp only [List.append_assoc]

-- A repetition containing the minimum symbol cannot have exponent above the order plus one.
private theorem exponent_le {q n k : ℕ} {W Y : List ℕ}
    (hW : W <+: gijswijtPrefix q n) (h : copies k Y <:+ W) (hy : q ∈ Y) :
    k ≤ q + 1 := by
  by_contra! hbig
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨U, V, rfl⟩ := List.append_of_mem hy
  obtain ⟨X, rfl⟩ := h
  rw [copies_add (b := 1), copies_succ 0, copies_zero, List.append_nil] at hW
  simp only [← List.append_assoc] at hW
  let P := X ++ copies k (U ++ q :: V) ++ U
  have hp : P ++ q :: V <+: gijswijtPrefix q n := by simpa only [P] using hW
  have hi : P.length < n := by
    have := hp.length_le
    simp only [prefix_length, List.length_append, List.length_cons] at this
    omega
  have hP : P <+: gijswijtPrefix q n := (List.prefix_append _ _).trans hp
  have hq : q = max q (curlingNumber P) := by
    have hh := get_of_prefix hp (i := P.length) (by simp)
    rw [List.getElem?_append_right (by rfl), Nat.sub_self, List.getElem?_cons_zero,
      prefix_get q hi, ← eq_prefix hP] at hh
    exact Option.some.inj hh
  have hrep : copies k ((q :: V) ++ U) <:+ P := by
    dsimp only [P]
    rw [List.append_assoc, can_rotate k U (q :: V), ← List.append_assoc]
    exact List.suffix_append _ _
  have := le_curling_of_suffix (by omega : 0 < k) (by simp) hrep
  omega

private theorem copies_period {X Y : List ℕ} {k i : ℕ}
    (hl : X.length ≤ i) (hr : i + Y.length < (X ++ copies k Y).length) :
    (X ++ copies k Y)[i]? = (X ++ copies k Y)[i + Y.length]? := by
  rw [List.length_append, copies_length] at hr
  rw [List.getElem?_append_right hl, List.getElem?_append_right (by omega),
    copies_get (by omega), copies_get (by omega)]
  rw [show i + Y.length - X.length = (i - X.length) + Y.length by omega, Nat.add_mod_right]

private theorem copies_cut {B : List ℕ} {n i : ℕ} (hi : i < n * B.length) :
    (copies n B).take i = copies (i / B.length) B ++ B.take (i % B.length) := by
  let a := i / B.length
  let r := i % B.length
  have hpos : 0 < B.length := by
    by_contra! h
    simp [show B.length = 0 by omega] at hi
  have ha : a < n := (Nat.div_lt_iff_lt_mul hpos).2 hi
  have hr : r < B.length := Nat.mod_lt _ hpos
  have hir : a * B.length + r = i := by
    simpa only [a, r, Nat.mul_comm a, Nat.add_comm] using Nat.mod_add_div i B.length
  have hn : n = a + (1 + (n - (a + 1))) := by omega
  change (copies n B).take i = copies a B ++ B.take r
  have hli : i = (copies a B).length + r := by rw [copies_length, hir]
  rw [hn, copies_add, Nat.add_comm 1, copies_succ, hli, List.take_append,
    Nat.add_sub_cancel_left, List.take_of_length_le (by omega),
    List.take_append_of_le_length hr.le]

private structure Block (q : ℕ) (B : List ℕ) (H : ℕ) : Prop where
  prefix_eq : B = gijswijtPrefix q B.length
  curling_le : curlingNumber B ≤ q
  gap_lt : H < B.length
  head_eq : B[0]? = some q
  last_eq : B[B.length - H - 1]? = some q
  tail_ne : ∀ j, B.length - H - 1 < j → B[j]? ≠ some q
  earlier : ∀ i, i < B.length - H - 1 → B[i]? = some q →
    ∃ j, i < j ∧ j ≤ i + H ∧ B[j]? = some q

private theorem block_one {q : ℕ} (hq : 1 ≤ q) : Block q (gijswijtBlock q 1) 0 := by
  rw [gijswijtBlock_one hq]
  refine ⟨?_, ?_, by simp, rfl, rfl, ?_, by simp⟩
  · simp [gijswijtPrefix, curlingNumber_nil, hq]
  · have : curlingNumber [q] = 1 := by
      unfold curlingNumber
      apply le_antisymm ?_ le_sup_right
      refine sup_le (Finset.sup_le ?_) le_rfl
      intro i hi
      have hh := (Finset.mem_filter.mp hi).1
      have := Finset.mem_range.mp hh
      simp only [id_eq, List.length_cons, List.length_nil] at *
      omega
    omega
  · intro j hj
    rw [List.getElem?_eq_none (by change 1 ≤ j; omega)]
    simp

private theorem get_copies_append {B T : List ℕ} {n i : ℕ}
    (h : i < n * B.length) :
    (copies n B ++ T)[i]? = B[i % B.length]? := by
  rw [List.getElem?_append_left (by simpa only [copies_length] using h), copies_get h]

-- Any occurrence of the minimum symbol followed by a full terminal gap is at the
-- last minimum symbol of its copy, even when the last copy is only a prefix.
private theorem gap_position {q n H i : ℕ} {B T : List ℕ} (hB : Block q B H)
    (hi : i + H < n * B.length) (h : (copies n B ++ T)[i]? = some q)
    (hg : ∀ j, i < j → j ≤ i + H → (copies n B ++ T)[j]? ≠ some q) :
    i % B.length = B.length - H - 1 := by
  rw [get_copies_append (by omega)] at h
  have := hB.gap_lt
  have hrem := Nat.mod_lt i (by omega : 0 < B.length)
  apply le_antisymm
  · by_contra! hgt
    exact hB.tail_ne _ hgt h
  · by_contra! hlt
    obtain ⟨j, hj, hjH, hjq⟩ := hB.earlier _ hlt h
    have hjl := (List.getElem?_eq_some_iff.mp hjq).1
    let j' := i + (j - i % B.length)
    have hj' : j' % B.length = j := by
      have he : j' = B.length * (i / B.length) + j := by
        have := Nat.mod_add_div i B.length
        omega
      rw [he, Nat.mul_add_mod, Nat.mod_eq_of_lt hjl]
    exact hg j' (by omega) (by omega) (by rwa [get_copies_append (by omega), hj'])


private theorem period_index {W Y : List ℕ} {n i : ℕ}
    (h : copies n Y <:+ W) (hl : W.length - n * Y.length ≤ i) (hr : i + Y.length < W.length) :
    W[i]? = W[i + Y.length]? := by
  obtain ⟨X, rfl⟩ := h
  simpa [copies_length] using copies_period (show X.length ≤ i by
    simpa [copies_length] using hl) hr

private theorem suffix_of_suffix_of_length {U V W : List ℕ} (hu : U <:+ W) (hv : V <:+ W)
    (h : U.length ≤ V.length) : U <:+ V := by
  rw [List.suffix_iff_eq_drop.mp hu, List.suffix_iff_eq_drop.mp hv,
    show W.length - U.length = W.length - V.length + (V.length - U.length) by
      have := hv.length_le
      omega, ← List.drop_drop]
  exact List.drop_suffix _ _

private theorem copies_last_get {q n H : ℕ} {B T : List ℕ} (hB : Block q B H) (hn : 0 < n) :
    (copies n B ++ T)[n * B.length - H - 1]? = some q := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hg := hB.gap_lt
  rw [Nat.succ_mul]
  have hi : a * B.length + B.length - H - 1 = a * B.length + (B.length - H - 1) := by
    omega
  rw [get_copies_append (by rw [Nat.succ_mul]; omega), hi, Nat.mul_comm a,
    Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  exact hB.last_eq

private theorem copies_tail_get {q n H i : ℕ} {B T : List ℕ} (hB : Block q B H)
    (hl : n * B.length - H - 1 < i) (hu : i < n * B.length) :
    (copies n B ++ T)[i]? ≠ some q := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hu)
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Nat.succ_mul] at hl hu
  have hg := hB.gap_lt
  rw [get_copies_append (by rwa [Nat.succ_mul])]
  have hi : i = a * B.length + (i - a * B.length) := by omega
  rw [hi, mul_comm a B.length, Nat.mul_add_mod, Nat.mod_eq_of_lt (by
    rw [mul_comm B.length a]; omega)]
  rw [mul_comm B.length a]
  exact hB.tail_ne _ (by omega)

private theorem last_gap_period {q H k n : ℕ} {B S Y : List ℕ} (hB : Block q B H)
    (hn : 0 < n) (hS : q ∉ S) (hk : 2 ≤ k)
    (h : copies k Y <:+ copies n B ++ S) (hY : q ∈ Y) :
    let W := copies n B ++ S
    let i := n * B.length - H - 1
    Y.length ≤ i ∧ (i - Y.length) % B.length = B.length - H - 1 ∧
      ∀ j, i ≤ j → j < W.length → W[j - Y.length]? = W[j]? := by
  dsimp only
  let W := copies n B ++ S
  let p := n * B.length
  let i := p - H - 1
  change Y.length ≤ i ∧ (i - Y.length) % B.length = B.length - H - 1 ∧ _
  have hg := hB.gap_lt
  have hp : B.length ≤ p := by
    simpa [p] using Nat.mul_le_mul_right B.length (show 1 ≤ n by omega)
  have hw : W.length = p + S.length := by simp [W, p, copies_length]
  have hq_iff : ∀ j, i < j → W[j]? ≠ some q := by
    intro j hj
    by_cases hjp : j < p
    · exact copies_tail_get hB hj hjp
    · change (copies n B ++ S)[j]? ≠ some q
      rw [List.getElem?_append_right (by simpa [p, copies_length] using not_lt.mp hjp)]
      exact fun hqj => hS (List.mem_of_getElem? hqj)
  have hlast : W[i]? = some q := copies_last_get hB hn
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hy : Y <:+ W := (copies_tail Y a).trans h
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hY
  have hqv : W[W.length - Y.length + v]? = some q := by
    rw [← List.getElem?_drop, ← List.suffix_iff_eq_drop.mp hy, hv]
  have hid : W.length - Y.length ≤ i := by
    by_contra! hc
    exact hq_iff _ (by omega) hqv
  have hmul : 2 * Y.length ≤ a.succ * Y.length := Nat.mul_le_mul_right _ (by omega)
  have htotal : a.succ * Y.length ≤ W.length := by
    simpa only [copies_length] using h.length_le
  have hshift (j : ℕ) (hl : i ≤ j) (hr : j < W.length) :
      W[j - Y.length]? = W[j]? := by
    have he : j - Y.length + Y.length = j := by omega
    have hper := period_index (W := W) h (i := j - Y.length) (by omega) (by rwa [he])
    simpa only [he] using hper
  refine ⟨by omega, gap_position hB (n := n) (by omega)
    ((hshift _ le_rfl (by omega)).trans hlast) ?_, hshift⟩
  intro j hj hj'
  have hxx := hshift (j + Y.length) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hxx
  exact fun hgq => hq_iff (j + Y.length) (by omega) (hxx.symm.trans hgq)

private theorem glue_no_q {q H : ℕ} {B S Y : List ℕ} (hB : Block q B H)
    (hS : q ∉ S) (hne : S ≠ []) {n : ℕ} (hn : 2 ≤ n)
    (h : copies n Y <:+ copies (q + 1) B ++ S) : q ∉ Y := by
  intro hq
  let W := copies (q + 1) B ++ S
  let p := (q + 1) * B.length
  let i := p - H - 1
  obtain ⟨hd, heq, hshift⟩ :
      Y.length ≤ i ∧ (i - Y.length) % B.length = B.length - H - 1 ∧
        ∀ j, i ≤ j → j < W.length → W[j - Y.length]? = W[j]? :=
    last_gap_period hB (by omega) hS hn h hq
  have hYlen := (List.getElem?_eq_some_iff.mp (List.mem_iff_getElem?.mp hq).choose_spec).1
  have hg := hB.gap_lt
  have hp : B.length ≤ p := by
    simpa [p] using Nat.mul_le_mul_right B.length (show 1 ≤ q + 1 by omega)
  have hw : W.length = p + S.length := by simp [W, p, copies_length]
  have hs : 0 < S.length := List.length_pos_iff.mpr hne
  have hnext : i - Y.length + (H + 1) < p := by omega
  have hh := Nat.mod_add_div (i - Y.length) B.length
  have hnew : (i - Y.length + (H + 1)) % B.length = 0 := by
    rw [show i - Y.length + (H + 1) = B.length * ((i - Y.length) / B.length) + B.length
      by omega, Nat.mul_add_mod, Nat.mod_self]
  have hbad : W[i - Y.length + (H + 1)]? = some q := by
    rw [get_copies_append hnext, hnew, hB.head_eq]
  have hper := hshift (i + (H + 1)) (by omega) (by omega)
  rw [show i + (H + 1) - Y.length = i - Y.length + (H + 1) by omega] at hper
  have hend : i + (H + 1) = p := by omega
  rw [hend] at hper
  have hstart : W[p]? = S[0]? := by
    change (copies (q + 1) B ++ S)[p]? = S[0]?
    rw [List.getElem?_append_right (by simp [copies_length, p]), copies_length]
    simp [p]
  exact hS (List.mem_of_getElem? (hstart.symm.trans (hper.symm.trans hbad)))

private theorem rep_in_tail {q k i : ℕ} {Y W : List ℕ} (h : copies k Y <:+ W)
    (hY : q ∉ Y) (hi : W[i]? = some q) : copies k Y <:+ W.drop (i + 1) := by
  obtain ⟨X, rfl⟩ := h
  have hi' : i < X.length := by
    by_contra! hle
    rw [List.getElem?_append_right hle] at hi
    exact hY (mem_copies (List.mem_of_getElem? hi))
  rw [List.drop_append_of_le_length (by omega)]
  exact List.suffix_append _ _

private theorem drop_copies_tail {B S : List ℕ} {n H : ℕ} (hn : 0 < n)
    (hH : H < B.length) :
    (copies n B ++ S).drop (n * B.length - H) = B.drop (B.length - H) ++ S := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [copies_add (b := 1), copies_succ 0, copies_zero, List.append_nil,
    Nat.succ_mul, Nat.add_sub_assoc hH.le, ← copies_length, List.append_assoc,
    List.drop_length_add_append, List.drop_append_of_le_length (by omega)]

-- Equal remainders at two distinct positions force their separation to be at least a block.
private theorem length_le_of_mod_eq {L i j : ℕ} (hlt : i < j) (h : i % L = j % L) :
    L ≤ j - i := by
  have ha := Nat.mod_add_div i L
  have hb := Nat.mod_add_div j L
  have hdiv : i / L < j / L := by
    have := Nat.div_le_div_right (c := L) hlt.le
    by_contra! h'
    rw [show i / L = j / L by omega] at ha
    omega
  have hm := Nat.mul_le_mul_left L (show i / L + 1 ≤ j / L by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

private theorem curling_copies_le {q n H : ℕ} {B : List ℕ} (hB : Block q B H)
    (hq : 1 ≤ q) (hn : 0 < n) : curlingNumber (copies n B) ≤ max q n := by
  by_contra! h
  obtain ⟨k, Y, hk, hY, hs⟩ := exists_copies_suffix (hq.trans (le_max_left _ _)) h
  let i := n * B.length - H - 1
  have hg := hB.gap_lt
  have hp : B.length ≤ n * B.length := by
    simpa using Nat.mul_le_mul_right B.length (show 1 ≤ n by omega)
  have hlast : (copies n B)[i]? = some q := by simpa only [List.append_nil] using
    (copies_last_get (T := []) hB hn)
  by_cases hyq : q ∈ Y
  · have hs' : copies k Y <:+ copies n B ++ [] := by simpa only [List.append_nil] using hs
    obtain ⟨hid, heq, _⟩ :
        Y.length ≤ i ∧ (i - Y.length) % B.length = B.length - H - 1 ∧ _ :=
      last_gap_period hB hn (S := []) (by simp) (by omega) hs' hyq
    have himod : i % B.length = B.length - H - 1 := by
      obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      simp only [i, Nat.succ_mul]
      rw [show a * B.length + B.length - H - 1 =
        B.length * a + (B.length - H - 1) by rw [Nat.mul_comm a]; omega,
        Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hpos : 0 < Y.length := List.length_pos_iff.mpr hY
    have hd := length_le_of_mod_eq (by omega) (heq.trans himod.symm)
    have hklen := Nat.mul_le_mul_left k (show B.length ≤ Y.length by omega)
    have hlt := Nat.mul_lt_mul_of_pos_right (show n < k by omega) (by omega : 0 < B.length)
    have htotal := hs.length_le
    rw [copies_length, copies_length] at htotal
    omega
  · have hsub := rep_in_tail hs hyq hlast
    have hsub' : copies k Y <:+ B.drop (B.length - H) := by
      have heq : i + 1 = n * B.length - H := by omega
      rw [heq] at hsub
      have he := drop_copies_tail (S := []) hn hg
      simp only [List.append_nil] at he
      rwa [he] at hsub
    have hlow := le_curling_of_suffix (by omega) hY (hsub'.trans (List.drop_suffix _ _))
    have := hB.curling_le
    omega


private theorem take_block_eq {q H r : ℕ} {B : List ℕ} (hB : Block q B H)
    (hr : r ≤ B.length) : B.take r = gijswijtPrefix q r :=
  (congrArg (List.take r) hB.prefix_eq).trans (prefix_take q hr)

-- In a later copy, the only new repeated suffixes with exponent above the order
-- must cross a full terminal gap, or start partway through that gap.
private theorem curling_partial_le {q a H r : ℕ} {B : List ℕ} (hq : 2 ≤ q)
    (hB : Block q B H) (ha : a ≤ q) (hr0 : 0 < r) (hr : r < B.length)
    (hw : copies a B ++ B.take r <+: gijswijtPrefix q (a * B.length + r)) :
    curlingNumber (copies a B ++ B.take r) ≤ max q (curlingNumber (B.take r)) := by
  let L := B.take r
  let W := copies a B ++ L
  let p := a * B.length
  have hL : L.length = r := by simp [L, hr.le]
  have hW : W.length = p + r := by simp [W, p, copies_length, hL]
  by_contra! h
  obtain ⟨k, Y, hk, hY, hs⟩ := exists_copies_suffix (W := W)
    (show 1 ≤ max q (curlingNumber L) from (by omega : 1 ≤ q).trans (le_max_left _ _)) h
  let d := Y.length
  let s := W.length - k * d
  have hd : 0 < d := List.length_pos_iff.mpr hY
  have hkq : q + 1 ≤ k := (le_max_left q (curlingNumber L)).trans_lt hk
  have htotal : k * d ≤ W.length := by simpa only [copies_length] using hs.length_le
  have h3 : 3 * d ≤ k * d := Nat.mul_le_mul_right _ (by omega)
  have hsmall : d < B.length := by
    by_contra! hbig
    have h1 := Nat.mul_le_mul_left k hbig
    have h2 := Nat.mul_le_mul_right B.length hkq
    have h3' := Nat.mul_le_mul_right B.length (show a + 1 ≤ q + 1 by omega)
    rw [Nat.add_mul, one_mul] at h3'
    omega
  have hshort : r < k * d := by
    by_contra! hlong
    have hsub : copies k Y <:+ L := suffix_of_suffix_of_length hs (List.suffix_append _ _)
      (by rwa [copies_length, hL])
    have hlo := le_curling_of_suffix (by omega) hY hsub
    omega
  have hpos : a > 0 := Nat.pos_of_ne_zero (by
    rintro rfl
    simp [p] at hW
    omega)
  have hp : B.length ≤ p := by
    simpa [p] using Nat.mul_le_mul_right B.length (show 1 ≤ a by omega)
  let i := p - H - 1
  have hg := hB.gap_lt
  have hlast : W[i]? = some q := copies_last_get hB hpos
  have hgap (j : ℕ) (hj : i < j) (hjp : j < p) : W[j]? ≠ some q :=
    copies_tail_get (n := a) hB hj hjp
  have hboundary : W[p]? = some q := by
    change (copies a B ++ L)[p]? = some q
    rw [List.getElem?_append_right (by simp [copies_length, p]), copies_length]
    simpa [p, L, List.getElem?_take_of_lt hr0] using hB.head_eq
  have hper (j : ℕ) (hl : s ≤ j) (hr : j + d < W.length) :
      W[j]? = W[j + d]? := period_index hs hl hr
  have hnot_before (hleft : s ≤ p - d) (hpd : d ≤ p) : H < d := by
    by_contra! hle
    have hh := hper (p - d) hleft (by omega)
    rw [show p - d + d = p by omega, hboundary] at hh
    exact hgap _ (by omega) (by omega) hh
  have hgap_mod (j : ℕ) (hj : j + H < W.length) (hjq : W[j]? = some q)
      (hjH : ∀ x, j < x → x ≤ j + H → W[x]? ≠ some q) :
      j % B.length = B.length - H - 1 := by
    let C := copies (a + 1) B ++ []
    have hpre : W <+: C := by
      dsimp only [W, C]
      rw [List.append_nil, copies_add (b := 1), copies_succ 0, copies_zero, List.append_nil]
      obtain ⟨T, hT⟩ := List.take_prefix r B
      exact ⟨T, by rw [List.append_assoc, show L ++ T = B from hT]⟩
    apply gap_position (T := []) hB (n := a + 1) (by rw [Nat.add_mul, one_mul]; omega)
    · rwa [← get_of_prefix hpre (by omega)]
    · intro x hx hx'
      rw [← get_of_prefix hpre (by omega)]
      exact hjH x hx hx'
  by_cases hsi : s ≤ i
  · have hi := hgap_mod i (by omega) hlast (fun j hj h' => hgap j hj (by omega))
    by_cases hdr : d < r
    · have hj := hgap_mod (i + d) (by omega) ((hper i hsi (by omega)).symm.trans hlast) (by
        intro j hj hj'
        have he := hper (j - d) (by omega) (by omega)
        rw [show j - d + d = j by omega] at he
        exact fun Hq => hgap (j - d) (by omega) (by omega) (he.trans Hq))
      have hh := length_le_of_mod_eq (by omega) (hi.trans hj.symm)
      omega
    · have hHd := hnot_before (by omega) (by omega)
      have hshift (j : ℕ) (hj : i ≤ j) (hj' : j ≤ i + H) : W[j - d]? = W[j]? := by
        have hh := hper (j - d) (by omega) (by omega)
        rwa [show j - d + d = j by omega] at hh
      have hj := hgap_mod (i - d) (by omega) ((hshift i le_rfl (by omega)).trans hlast) (by
        intro j hj hj'
        have he := hshift (j + d) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at he
        exact fun Hq => hgap (j + d) (by omega) (by omega) (he.symm.trans Hq))
      have hh := length_le_of_mod_eq (by omega) (hj.trans hi.symm)
      omega
  · have hjp : p < s + d := by
      by_contra! hc
      exact hgap (p - d) (by omega) (by omega) (by
        have hh := hper (p - d) (by omega) (by omega)
        rwa [show p - d + d = p by omega, hboundary] at hh)
    have hdr : d < r := by
      by_contra! hc
      have hs' : s ≤ p - d := by omega
      have hh := hper (p - d) hs' (by omega)
      rw [show p - d + d = p by omega, hboundary] at hh
      exact hgap _ (by omega) (by omega) hh
    have hj : s + d < W.length := by omega
    let t := max q (curlingNumber (gijswijtPrefix q s))
    have ht : W[s]? = some t := by
      have hh : s < (copies a B ++ B.take r).length := by change s < W.length; omega
      exact (get_of_prefix hw hh).trans (prefix_get q (by omega))
    have htq : q < t := by
      have hne := hgap s (by omega) (by omega)
      have hle : q ≤ t := le_max_left _ _
      rw [ht] at hne
      exact lt_of_le_of_ne hle (fun ht => hne (by rw [← ht]))
    let v := s + d - p
    have hv : v < r := by omega
    have hvget : W[s + d]? = B[v]? := by
      change (copies a B ++ L)[s + d]? = B[v]?
      rw [List.getElem?_append_right (by simpa [copies_length, p] using hjp.le)]
      simpa [v, L, copies_length, p] using List.getElem?_take_of_lt (l := B) hv
    have ht' : B[v]? = some t := hvget.symm.trans ((hper s le_rfl hj).symm.trans ht)
    have hv' : B[v]? = some (max q (curlingNumber (B.take v))) := by
      rw [take_block_eq hB (by omega)]
      exact (congrArg (fun l : List ℕ => l[v]?) hB.prefix_eq).trans (prefix_get q (by omega))
    have hvhigh : q < curlingNumber (B.take v) := by
      have h := Option.some.inj (ht'.symm.trans hv')
      omega
    have hYq : q ∈ Y := by
      have hsub : (W.drop s)[p - s]? = some q := by
        rw [List.getElem?_drop, show s + (p - s) = p by omega, hboundary]
      have hEq : W.drop s = copies k Y := by
        simpa only [copies_length, s, d] using (List.suffix_iff_eq_drop.mp hs).symm
      rw [hEq] at hsub
      exact mem_copies (List.mem_of_getElem? hsub)
    have hkcap := exponent_le hw hs hYq
    have hlocal : B.take v <:+ Y := by
      obtain ⟨X, hx⟩ := hs
      have hX : X.length = s := by
        have hh := congrArg List.length hx
        simp only [List.length_append, copies_length] at hh
        dsimp only [s, d]
        omega
      have htaken : W.take (s + d) = X ++ Y := by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        rw [← hx, copies_succ, ← List.append_assoc, ← hX]
        simpa only [List.length_append, d] using
          (List.take_append_length (l₁ := X ++ Y) (l₂ := copies n Y))
      have hdrop : (W.take (s + d)).drop p = B.take v := by
        change ((copies a B ++ L).take (s + d)).drop p = _
        have hp' : (copies a B).length = p := copies_length _ _
        rw [List.take_append, List.take_of_length_le (by omega), hp', ← hp', List.drop_left,
          hp', List.take_take]
        exact congrArg (fun n => B.take n) (min_eq_left hv.le)
      rw [htaken] at hdrop
      have hp' : p = X.length + (p - X.length) := by omega
      rw [hp', List.drop_length_add_append] at hdrop
      rw [← hdrop]
      exact List.drop_suffix _ _
    have hYsuffix : Y <:+ W := by
      obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact (copies_tail Y a).trans hs
    have hYlocal : Y <:+ L := suffix_of_suffix_of_length hYsuffix (List.suffix_append _ _)
      (by rw [hL]; omega)
    have hlow := curlingNumber_le_of_suffix (hlocal.trans hYlocal)
    omega


private theorem copies_prefix_eq {q H : ℕ} {B : List ℕ} (hq : 2 ≤ q)
    (hB : Block q B H) : copies (q + 1) B = gijswijtPrefix q ((q + 1) * B.length) := by
  let W := copies (q + 1) B
  have hlen : W.length = (q + 1) * B.length := copies_length _ _
  have hpos : 0 < B.length := Nat.zero_lt_of_lt hB.gap_lt
  suffices ∀ i ≤ W.length, W.take i = gijswijtPrefix q i by
    rw [← hlen]
    simpa only [List.take_length] using this W.length le_rfl
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    let a := i / B.length
    let r := i % B.length
    have hi' : i < (q + 1) * B.length := by omega
    have ha : a ≤ q := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpos).mpr hi')
    have hr : r < B.length := Nat.mod_lt _ hpos
    have hir : a * B.length + r = i := by
      simpa [a, r, Nat.mul_comm a, Nat.add_comm] using Nat.mod_add_div i B.length
    have htaken := (copies_cut hi').symm.trans (ih (by omega))
    change copies a B ++ B.take r = gijswijtPrefix q i at htaken
    have hrEq := take_block_eq hB hr.le
    have hlocal : B[r]? = some (max q (curlingNumber (B.take r))) := by
      rw [hrEq]
      exact (congrArg (fun l : List ℕ => l[r]?) hB.prefix_eq).trans (prefix_get q hr)
    have hmax : max q (curlingNumber (gijswijtPrefix q i)) =
        max q (curlingNumber (B.take r)) := by
      rw [← htaken]
      apply le_antisymm
      · apply max_le (le_max_left _ _)
        by_cases hzero : r = 0
        · have hlow : curlingNumber (copies a B) ≤ q := by
            by_cases ha0 : a = 0
            · simp [ha0, copies_zero, curlingNumber_nil, show 1 ≤ q by omega]
            · exact (curling_copies_le hB (by omega) (Nat.pos_of_ne_zero ha0)).trans
                (max_le le_rfl ha)
          simpa only [hzero, List.take_zero, List.append_nil] using
            hlow.trans (le_max_left q (curlingNumber []))
        · have hp : copies a B ++ B.take r <+: gijswijtPrefix q (a * B.length + r) := by
            rw [hir, htaken]
          exact curling_partial_le hq hB ha (by omega) hr hp
      · exact max_le_max_left _ (curlingNumber_le_of_suffix (List.suffix_append _ _))
    rw [List.take_add_one, copies_get hi', ih (by omega), gijswijtPrefix]
    change gijswijtPrefix q i ++ (B[r]?).toList = _
    rw [hlocal, ← hmax]
    rfl

private theorem glue_curling {q H : ℕ} {B S : List ℕ} (hq : 1 ≤ q) (hB : Block q B H)
    (hS : q ∉ S) (hne : S ≠ []) :
    max q (curlingNumber (copies (q + 1) B ++ S)) =
      max q (curlingNumber (B.drop (B.length - H) ++ S)) := by
  let W := copies (q + 1) B ++ S
  let T := B.drop (B.length - H) ++ S
  let i := (q + 1) * B.length - H - 1
  have hg := hB.gap_lt
  have hp : B.length ≤ (q + 1) * B.length := by
    simpa using Nat.mul_le_mul_right B.length (show 1 ≤ q + 1 by omega)
  have hdrop : W.drop (i + 1) = T := by
    have hindex : i + 1 = (q + 1) * B.length - H := by omega
    rw [hindex]
    exact drop_copies_tail (by omega) hg
  change max q (curlingNumber W) = max q (curlingNumber T)
  apply le_antisymm
  · apply max_le (le_max_left _ _)
    by_contra! h
    obtain ⟨k, Y, hk, hY, hs⟩ := exists_copies_suffix (hq.trans (le_max_left _ _)) h
    have hqY := glue_no_q hB hS hne (by omega) hs
    have hsub := rep_in_tail hs hqY (copies_last_get hB (by omega))
    change copies k Y <:+ W.drop (i + 1) at hsub
    rw [hdrop] at hsub
    have := le_curling_of_suffix (by omega) hY hsub
    omega
  · rw [← hdrop]
    exact max_le_max_left _ (curlingNumber_le_of_suffix (List.drop_suffix _ _))

private theorem copies_next {q H : ℕ} {B : List ℕ} (hq : 1 ≤ q) (hB : Block q B H) :
    curlingNumber (copies (q + 1) B) = q + 1 := by
  have hne : B ≠ [] := List.length_pos_iff.mp (Nat.zero_lt_of_lt hB.gap_lt)
  exact le_antisymm ((curling_copies_le hB hq (by omega)).trans (max_le (by omega) le_rfl))
    (le_curling_of_suffix (by omega) hne ⟨[], by simp⟩)

private theorem block_extend {q H : ℕ} {B S : List ℕ}
    (hB : Block q B H) (hS : q ∉ S) (hne : S ≠ [])
    (hW : copies (q + 1) B ++ S =
      gijswijtPrefix q ((copies (q + 1) B ++ S).length))
    (hcurl : curlingNumber (copies (q + 1) B ++ S) ≤ q) :
    Block q (copies (q + 1) B ++ S) (H + S.length) := by
  let W := copies (q + 1) B ++ S
  let p := (q + 1) * B.length
  have hlen : W.length = p + S.length := by simp [W, p, copies_length]
  have hSpos : 0 < S.length := List.length_pos_iff.mpr hne
  have hp : B.length ≤ p := by
    simpa [p] using Nat.mul_le_mul_right B.length (show 1 ≤ q + 1 by omega)
  have hg := hB.gap_lt
  have hi : W.length - (H + S.length) - 1 = p - H - 1 := by omega
  change Block q W (H + S.length)
  refine ⟨hW, hcurl, by omega, ?_, ?_, ?_, ?_⟩
  · rw [get_copies_append (by omega), Nat.zero_mod, hB.head_eq]
  · rw [hi]
    exact copies_last_get hB (by omega)
  · rw [hi]
    intro j hj
    by_cases hj' : j < p
    · exact copies_tail_get hB hj hj'
    · change (copies (q + 1) B ++ S)[j]? ≠ some q
      rw [List.getElem?_append_right (by simpa [copies_length, p] using not_lt.mp hj')]
      exact fun hqj => hS (List.mem_of_getElem? hqj)
  · rw [hi]
    intro j hj hjq
    rw [get_copies_append (by omega)] at hjq
    let r := j % B.length
    have hr : r < B.length := Nat.mod_lt _ (by omega)
    have hdiv := Nat.mod_add_div j B.length
    change r + B.length * (j / B.length) = j at hdiv
    change B[r]? = some q at hjq
    have hrec (v : ℕ) (hv : r < v) (hvp : j + (v - r) < p)
        (hvH : v ≤ r + (H + S.length)) (hvB : v < B.length) (hvq : B[v]? = some q) :
        ∃ k, j < k ∧ k ≤ j + (H + S.length) ∧ W[k]? = some q := by
      refine ⟨j + (v - r), by omega, by omega, ?_⟩
      have hshift : j + (v - r) = B.length * (j / B.length) + v := by omega
      rw [get_copies_append hvp, hshift, Nat.mul_add_mod, Nat.mod_eq_of_lt hvB, hvq]
    rcases lt_trichotomy r (B.length - H - 1) with hlt | heq | hgt
    · obtain ⟨v, hv, hvH, hvq⟩ := hB.earlier r hlt hjq
      have hvB := (List.getElem?_eq_some_iff.mp hvq).1
      have hbound : j / B.length < q + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr
        (by omega)
      have hprod := Nat.mul_le_mul_left B.length (show j / B.length + 1 ≤ q + 1 by omega)
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm B.length (q + 1)] at hprod
      exact hrec v hv (by omega) (by omega) hvB hvq
    · refine ⟨j + (H + 1), by omega, by omega, ?_⟩
      have hmod : (j + (H + 1)) % B.length = 0 := by
        rw [show j + (H + 1) = B.length * (j / B.length) + B.length by omega,
          Nat.mul_add_mod, Nat.mod_self]
      rw [get_copies_append (by omega), hmod, hB.head_eq]
    · exact (hB.tail_ne _ hgt hjq).elim


-- As the current glue grows, its concatenation with the previous terminal gap
-- follows the next-order recurrence. At a return to q, begin the next block.
private structure Stage (q n : ℕ) where
  block : List ℕ
  gap : ℕ
  glue : List ℕ
  good : Block q block gap
  glue_avoids : q ∉ glue
  current : copies (q + 1) block ++ glue =
    gijswijtPrefix q ((copies (q + 1) block ++ glue).length)
  higher : block.drop (block.length - gap) ++ glue = gijswijtPrefix (q + 1) n

private theorem stage_advance {q n : ℕ} (hq : 2 ≤ q) (A : Stage q n)
    (h : q < max q (curlingNumber (copies (q + 1) A.block ++ A.glue))) :
    Nonempty (Stage q (n + 1)) := by
  let W := copies (q + 1) A.block ++ A.glue
  let x := max q (curlingNumber W)
  have hnext : x = max (q + 1) (curlingNumber (gijswijtPrefix (q + 1) n)) := by
    rw [← A.higher]
    by_cases hglue : A.glue = []
    · have hW : curlingNumber W = q + 1 := by
        simpa [W, hglue] using copies_next (by omega) A.good
      have hT : curlingNumber (A.block.drop (A.block.length - A.gap) ++ A.glue) ≤ q := by
        rw [hglue, List.append_nil]
        exact (curlingNumber_le_of_suffix (List.drop_suffix _ _)).trans A.good.curling_le
      dsimp only [x]
      omega
    · have hcurl := glue_curling (by omega : 1 ≤ q) A.good A.glue_avoids hglue
      change x = _ at hcurl
      change q < x at h
      omega
  refine ⟨⟨A.block, A.gap, A.glue ++ [x], A.good, ?_, ?_, ?_⟩⟩
  · change q < x at h
    simp [A.glue_avoids, ne_of_lt h]
  · rw [← List.append_assoc]
    change W ++ [x] = gijswijtPrefix q (W ++ [x]).length
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, gijswijtPrefix]
    change W ++ [max q (curlingNumber W)] =
      gijswijtPrefix q W.length ++ [max q (curlingNumber (gijswijtPrefix q W.length))]
    exact congrArg (fun P => P ++ [max q (curlingNumber P)]) A.current
  · rw [← List.append_assoc, A.higher, hnext, gijswijtPrefix]

private theorem stages {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : Nonempty (Stage q n) := by
  induction n with
  | zero =>
    let B := gijswijtBlock q 1
    have hB := block_one (q := q) (by omega)
    refine ⟨⟨B, 0, [], hB, by simp, ?_, by simp [gijswijtPrefix]⟩⟩
    simpa only [List.append_nil, copies_length] using copies_prefix_eq hq hB
  | succ n ih =>
    obtain ⟨A⟩ := ih
    let W := copies (q + 1) A.block ++ A.glue
    by_cases hc : curlingNumber W ≤ q
    · have hne : A.glue ≠ [] := by
        intro he
        have h := copies_next (by omega : 1 ≤ q) A.good
        simp [W, he, h] at hc
        omega
      have hB := block_extend A.good A.glue_avoids hne A.current hc
      let H := A.gap + A.glue.length
      have hg := A.good.gap_lt
      have hdrop : W.drop (W.length - H) = gijswijtPrefix (q + 1) n := by
        have he : W.length - H = (q + 1) * A.block.length - A.gap := by
          simp only [W, H, List.length_append, copies_length, Nat.add_sub_add_right]
        rw [he, drop_copies_tail (by omega) hg, A.higher]
      let A' : Stage q n := ⟨W, H, [], hB, by simp,
        by simpa only [List.append_nil, copies_length] using copies_prefix_eq hq hB,
        by simpa only [List.append_nil] using hdrop⟩
      apply stage_advance hq A'
      have h := copies_next (by omega : 1 ≤ q) hB
      change q < max q (curlingNumber (copies (q + 1) W ++ []))
      change curlingNumber (copies (q + 1) W) = q + 1 at h
      simp [h]
    · apply stage_advance hq A
      change q < max q (curlingNumber W)
      omega

private theorem stage_suffix {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    ∃ l, gijswijtPrefix (q + 1) n <:+ gijswijtPrefix q l := by
  obtain ⟨A⟩ := stages hq n
  let W := copies (q + 1) A.block ++ A.glue
  refine ⟨W.length, ?_⟩
  have hd := drop_copies_tail (S := A.glue) (by omega : 0 < q + 1) A.good.gap_lt
  rw [← A.current, ← A.higher, ← hd]
  exact List.drop_suffix _ _

private theorem exists_large_term (d : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    ∃ l, q + d ∈ gijswijtPrefix q l := by
  induction d generalizing q with
  | zero =>
    refine ⟨1, ?_⟩
    simp [gijswijtPrefix, curlingNumber_nil, show 1 ≤ q by omega]
  | succ d ih =>
    obtain ⟨n, hn⟩ := ih (q := q + 1) (by omega)
    obtain ⟨l, hl⟩ := stage_suffix hq n
    exact ⟨l, hl.subset (by simpa only [Nat.add_right_comm q 1 d, Nat.add_assoc] using hn)⟩

private theorem order_after_first {q n x : ℕ} (hq : 1 ≤ q)
    (hprev : x ∉ gijswijtPrefix q n) (hx : x ∈ gijswijtPrefix q (n + 1)) :
    gijswijtTerm q (n + 2) = q := by
  rw [show n + 2 = (n + 1) + 1 by omega, next_eq_order]
  by_contra! h
  obtain ⟨k, Y, hk, hne, X, hX⟩ := exists_copies_suffix hq h
  have hlast : (gijswijtPrefix q (n + 1))[n]? = some x := by
    simp only [gijswijtPrefix, List.mem_append, List.mem_singleton] at hx
    simpa [hx.resolve_left hprev] using prefix_get q (show n < n + 1 by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [copies_add (b := 1), copies_succ 0, copies_zero, List.append_nil,
    ← List.append_assoc] at hX
  let P := X ++ copies k Y
  change P ++ Y = gijswijtPrefix q (n + 1) at hX
  have hlen := congrArg List.length hX
  simp only [List.length_append, prefix_length] at hlen
  have hYpos := List.length_pos_iff.mpr hne
  have hp : P.length ≤ n := by omega
  have hmem : x ∈ Y := by
    rw [← hX, List.getElem?_append_right hp] at hlast
    exact List.mem_of_getElem? hlast
  have hP : P <+: gijswijtPrefix q (n + 1) := hX ▸ List.prefix_append _ _
  have hmem' : x ∈ P := by
    apply List.mem_append_right
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact (copies_tail Y a).subset hmem
  exact hprev ((prefix_mono q hp).subset (eq_prefix hP ▸ hmem'))

private theorem exists_return {q : ℕ} (hq : 2 ≤ q) (p : ℕ) :
    ∃ l, p < l ∧ gijswijtTerm q (l + 1) = q := by
  let x := q + (gijswijtPrefix q p).sum + 1
  have hx : ∃ l, x ∈ gijswijtPrefix q l := by
    simpa only [x, Nat.add_assoc] using exists_large_term ((gijswijtPrefix q p).sum + 1) hq
  classical
  let l := Nat.find hx
  have hl : x ∈ gijswijtPrefix q l := Nat.find_spec hx
  have hp : p < l := by
    by_contra! h
    have hxmem := (prefix_mono q h).subset hl
    obtain ⟨L, R, he⟩ := List.append_of_mem hxmem
    have hsum : x ≤ (gijswijtPrefix q p).sum := by rw [he, List.sum_append]; simp; omega
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show l ≠ 0 by omega)
  have hprev : x ∉ gijswijtPrefix q n := fun h => by
    have hh : l ≤ n := Nat.find_min' hx h
    omega
  exact ⟨l, hp, by rw [hn]; exact order_after_first (by omega) hprev (by rwa [hn] at hl)⟩


-- The least-position definition now gives a finite glue string and agrees with the
-- recursive copying rule.
private theorem block_step {q u H : ℕ} (hq : 2 ≤ q) (hu : 1 ≤ u)
    (hB : Block q (gijswijtBlock q u) H) :
    ∃ S, q ∉ S ∧ S ≠ [] ∧
      gijswijtBlock q (u + 1) = copies (q + 1) (gijswijtBlock q u) ++ S ∧
      Block q (gijswijtBlock q (u + 1)) (H + S.length) := by
  let B := gijswijtBlock q u
  let b := gijswijtBlockLength q u
  let p := (q + 1) * b
  let l := gijswijtBlockLength q (u + 1)
  let S := (gijswijtPrefix q l).drop p
  have hb : B.length = b := prefix_length _ _
  have hrec : l = sInf {k | p < k ∧ gijswijtTerm q (k + 1) = q} := by
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    rfl
  have hnon : {k | p < k ∧ gijswijtTerm q (k + 1) = q}.Nonempty := exists_return hq p
  have hl : p < l ∧ gijswijtTerm q (l + 1) = q := hrec.symm ▸ Nat.sInf_mem hnon
  have hcopy : copies (q + 1) B = gijswijtPrefix q p := by
    change copies (q + 1) B = gijswijtPrefix q ((q + 1) * b)
    rw [← hb]
    exact copies_prefix_eq hq hB
  have heq : gijswijtBlock q (u + 1) = copies (q + 1) B ++ S := by
    change gijswijtPrefix q l = _
    rw [hcopy, ← prefix_take q hl.1.le]
    exact (List.take_append_drop _ _).symm
  have hs : q ∉ S := by
    intro hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
    change ((gijswijtPrefix q l).drop p)[j]? = some q at hj
    rw [List.getElem?_drop] at hj
    have hjl := (List.getElem?_eq_some_iff.mp hj).1
    rw [prefix_length] at hjl
    rw [prefix_get q hjl] at hj
    have hc : max q (curlingNumber (gijswijtPrefix q (p + j))) = q := Option.some.inj hj
    have ht : gijswijtTerm q (p + j + 1) = q := next_eq_order.mpr (by omega)
    by_cases hj0 : j = 0
    · rw [hj0, Nat.add_zero, ← hcopy, copies_next (by omega) hB] at hc
      omega
    · have hm' : p + j ∈ {k | p < k ∧ gijswijtTerm q (k + 1) = q} := ⟨by omega, ht⟩
      have hle : l ≤ p + j := hrec.symm ▸ Nat.sInf_le hm'
      omega
  have hne : S ≠ [] := by
    rw [← List.length_pos_iff, show S.length = l - p by simp [S, prefix_length]]
    omega
  refine ⟨S, hs, hne, heq, ?_⟩
  have hlen : (gijswijtBlock q (u + 1)).length = l := prefix_length _ _
  have hW : gijswijtBlock q (u + 1) =
      gijswijtPrefix q (gijswijtBlock q (u + 1)).length := by rw [hlen]; rfl
  have hc : curlingNumber (gijswijtBlock q (u + 1)) ≤ q := next_eq_order.mp hl.2
  rw [heq] at hW hc ⊢
  exact block_extend hB hs hne hW hc

private theorem block_good {q u : ℕ} (hq : 2 ≤ q) (hu : 1 ≤ u) :
    ∃ H, Block q (gijswijtBlock q u) H := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  induction u with
  | zero => exact ⟨0, block_one (by omega)⟩
  | succ u ih =>
    obtain ⟨H, hH⟩ := ih (by omega)
    obtain ⟨S, _, _, _, h⟩ := block_step hq (by omega : 1 ≤ u + 1) hH
    exact ⟨H + S.length, h⟩

private def followedBy (q : ℕ) (B P : List ℕ) : Prop :=
  ∃ T, P ++ q :: T = B

private theorem followedBy_iff {q : ℕ} {B P : List ℕ} :
    followedBy q B P ↔ P <+: B ∧ B[P.length]? = some q := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨List.prefix_append _ _, by simp⟩
  · rintro ⟨⟨T, rfl⟩, h⟩
    cases T with
    | nil => simp at h
    | cons a T =>
      rw [List.getElem?_append_right (by rfl), Nat.sub_self, List.getElem?_cons_zero] at h
      exact ⟨T, by rw [Option.some.inj h]⟩

private theorem followedBy_iff_curling {q : ℕ} {B P : List ℕ}
    (hB : B = gijswijtPrefix q B.length) :
    followedBy q B P ↔ P <+: B ∧ P.length < B.length ∧ curlingNumber P ≤ q := by
  rw [followedBy_iff]
  constructor
  · rintro ⟨hP, h⟩
    have hl := (List.getElem?_eq_some_iff.mp h).1
    have hEq := eq_prefix (hB ▸ hP)
    rw [show B[P.length]? = (gijswijtPrefix q B.length)[P.length]? from
      congrArg (fun l : List ℕ => l[P.length]?) hB, prefix_get q hl] at h
    have hc := Option.some.inj h
    exact ⟨hP, hl, by rw [hEq]; omega⟩
  · rintro ⟨hP, hl, hc⟩
    refine ⟨hP, ?_⟩
    have hEq := eq_prefix (hB ▸ hP)
    rw [show B[P.length]? = (gijswijtPrefix q B.length)[P.length]? from
      congrArg (fun l : List ℕ => l[P.length]?) hB, prefix_get q hl, ← hEq, max_eq_left hc]

private theorem followedBy_copies {q : ℕ} {B S P : List ℕ}
    (hB : 0 < B.length) (hS : q ∉ S) :
    followedBy q (copies (q + 1) B ++ S) P ↔
      ∃ a ≤ q, ∃ L, followedBy q B L ∧ P = copies a B ++ L := by
  constructor
  · rw [followedBy_iff]
    rintro ⟨hpre, hq⟩
    have hi : P.length < (q + 1) * B.length := by
      by_contra! hc
      rw [List.getElem?_append_right (by simpa [copies_length] using hc)] at hq
      exact hS (List.mem_of_getElem? hq)
    let a := P.length / B.length
    let r := P.length % B.length
    have hr : r < B.length := Nat.mod_lt _ hB
    have ha : a ≤ q := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hB).mpr hi)
    rw [get_copies_append hi] at hq
    refine ⟨a, ha, B.take r, followedBy_iff.mpr ⟨List.take_prefix _ _, ?_⟩, ?_⟩
    · simpa [List.length_take, hr.le, r] using hq
    · calc
        P = (copies (q + 1) B ++ S).take P.length := List.prefix_iff_eq_take.mp hpre
        _ = copies a B ++ B.take r := by
          rw [List.take_append_of_le_length (by rw [copies_length]; exact hi.le), copies_cut hi]
  · rintro ⟨a, ha, L, ⟨T, hT⟩, rfl⟩
    have he : q + 1 = a + ((q - a) + 1) := by omega
    rw [he, copies_add, copies_succ]
    exact ⟨T ++ copies (q - a) B ++ S, by simp [← hT, List.append_assoc]⟩

private theorem blockWord_succ (q u : ℕ) (hu : 1 ≤ u) (a : ℕ → ℕ) :
    gijswijtBlockWord q (u + 1) a =
      copies (a u) (gijswijtBlock q u) ++ gijswijtBlockWord q u a := by
  have h : u = (u - 1).succ := by omega
  unfold gijswijtBlockWord
  rw [Nat.add_sub_cancel, h, List.range_succ, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.map_cons, List.flatten_cons, Nat.succ_eq_add_one, copies]
  rw [show u - 1 + 1 = u by omega]

private theorem blockWord_congr {q u : ℕ} {a b : ℕ → ℕ}
    (h : ∀ i, 1 ≤ i → i < u → a i = b i) :
    gijswijtBlockWord q u a = gijswijtBlockWord q u b := by
  unfold gijswijtBlockWord
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_reverse, List.mem_range] at hi
  rw [h (i + 1) (by omega) (by omega)]

private theorem followedBy_blockWord {q u : ℕ} (hq : 2 ≤ q) (hu : 1 ≤ u)
    (P : List ℕ) :
    followedBy q (gijswijtBlock q u) P ↔
      ∃ a : ℕ → ℕ, (∀ i, 1 ≤ i → i < u → a i ≤ q) ∧ P = gijswijtBlockWord q u a := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  induction u generalizing P with
  | zero =>
    rw [gijswijtBlock_one (by omega : 1 ≤ q)]
    constructor
    · rintro ⟨T, hT⟩
      have hh := congrArg List.length hT
      simp only [List.length_append, List.length_cons, List.length_nil] at hh
      have hnil : P = [] := List.length_eq_zero_iff.mp (by omega)
      exact ⟨fun _ => 0, by simp, by rw [gijswijtBlockWord_one, hnil]⟩
    · rintro ⟨a, _, ha⟩
      rw [gijswijtBlockWord_one] at ha
      exact ⟨[], by simp [ha]⟩
  | succ u ih =>
    have hu' : 1 ≤ u + 1 := by omega
    obtain ⟨H, hH⟩ := block_good hq hu'
    obtain ⟨S, hS, _, hEq, _⟩ := block_step hq hu' hH
    rw [hEq, followedBy_copies (Nat.zero_lt_of_lt hH.gap_lt) hS]
    constructor
    · rintro ⟨c, hc, L, hL, hP⟩
      obtain ⟨a, ha, rfl⟩ := (ih L (by omega)).mp hL
      let b := fun i => if i = u + 1 then c else a i
      refine ⟨b, ?_, ?_⟩
      · intro i hi hi'
        by_cases he : i = u + 1
        · simpa [b, he] using hc
        · simpa [b, he] using ha i hi (by omega)
      · rw [hP, blockWord_succ q (u + 1) hu', show b (u + 1) = c by simp [b]]
        rw [blockWord_congr (a := b) (b := a) (fun i _ hi => by
          simp [b, show i ≠ u + 1 by omega])]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a (u + 1), ha _ hu' (by omega), gijswijtBlockWord q (u + 1) a, ?_, ?_⟩
      · exact (ih (gijswijtBlockWord q (u + 1) a) (by omega)).mpr
          ⟨a, fun i hi hi' => ha i hi (by omega), rfl⟩
      · exact blockWord_succ q (u + 1) hu' a

end MetaMathlibExt.gijswijtProperPrefix_curling_iff

namespace MetaMathlibExt

/-- **Proper prefixes of a block with curling number at most $m + 1$.** Let $m \ge 1$ and
$u \ge 1$, and write $B_t$ for the block $B_t^{(m+1)}$ of the $(m+1)$th order Gijswijt sequence.
A string $P$ is a proper prefix of $B_u$ (a prefix strictly shorter than $B_u$) with curling
number $\mathcal{C}(P) \le m + 1$ if and only if $P = B_{u-1}^{a_{u-1}} \cdots B_2^{a_2} B_1^{a_1}$
for some natural numbers $a_1, \dots, a_{u-1} \le m + 1$, where $B_t^{a}$ denotes $a$ copies of
$B_t$ concatenated.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 11 (`jis-2025-25.4.6-lem-11`). -/
public theorem gijswijtProperPrefix_curling_iff {m u : ℕ} (hm : 1 ≤ m) (hu : 1 ≤ u)
    (P : List ℕ) :
    (P <+: gijswijtBlock (m + 1) u ∧ P.length < (gijswijtBlock (m + 1) u).length ∧
        curlingNumber P ≤ m + 1) ↔
      ∃ a : ℕ → ℕ, (∀ i, 1 ≤ i → i < u → a i ≤ m + 1) ∧ P = gijswijtBlockWord (m + 1) u a := by
  have hq : 2 ≤ m + 1 := by omega
  obtain ⟨H, hH⟩ := gijswijtProperPrefix_curling_iff.block_good hq hu
  rw [← gijswijtProperPrefix_curling_iff.followedBy_iff_curling hH.prefix_eq]
  exact gijswijtProperPrefix_curling_iff.followedBy_blockWord hq hu P

end MetaMathlibExt
