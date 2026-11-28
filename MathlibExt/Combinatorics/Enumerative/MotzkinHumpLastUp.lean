/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MotzkinHumpsYoungTableaux

/-!
# Marked humps and last-up Motzkin prefixes

Around a marked hump write the word as `A U Fʳ D B`. Its image is `A U B* U Fʳ`,
where `B*` reverses the steps of `B` and interchanges up and down. The inverse reads
`r` from the trailing flats and locates the first cut at the last vertex of height `k - 1`.
We implement the cuts in terms of vertex heights, so `B*` traverses the same heights
in reverse order, translated up by `k`.

## References

* Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*,
  Journal of Integer Sequences 28 (2025), Article 25.8.1, pp. 1–11, Lemma 3 (p. 4).
-/

namespace MetaMathlibExt
namespace motzkinHumpFamily_equiv_lastUpEvenFamily

private abbrev Word (n : ℕ) := Fin n → Fin 3
private abbrev Heights := ℕ → ℤ

private structure Walk (n : ℕ) (h : ℤ) (H : Heights) : Prop where
  start : H 0 = 0
  finish : H n = h
  nonneg : ∀ m ≤ n, 0 ≤ H m
  step : ∀ m < n, -1 ≤ H (m + 1) - H m ∧ H (m + 1) - H m ≤ 1

private theorem walk_height {n : ℕ} {h : ℤ} {p : Word n} (hp : IsMotzkinPrefix n h p) :
    Walk n h (motzkinPrefixHeight p) where
  start := motzkinPrefixHeight_zero p
  finish := (motzkinPrefixHeight_total p).symm.trans ((isMotzkinPrefix_iff n h p).mp hp).2
  nonneg m hm := motzkinPrefixHeight_prefix_sum p hm ▸ ((isMotzkinPrefix_iff n h p).mp hp).1 m hm
  step m hm := by
    rw [motzkinPrefixHeight_step p ⟨m, hm⟩, motzkinStep_eq_sub_one]
    have hb := (p ⟨m, hm⟩).isLt
    omega

private def wordOf {n : ℕ} {h : ℤ} {H : Heights} (w : Walk n h H) : Word n :=
  fun i => ⟨(H (i.val + 1) - H i.val + 1).toNat, by
    have := w.step i.val i.isLt
    omega⟩

private theorem step_wordOf {n : ℕ} {h : ℤ} {H : Heights} (w : Walk n h H) (i : Fin n) :
    motzkinStep (wordOf w i) = H (i.val + 1) - H i.val := by
  have := w.step i.val i.isLt
  rw [motzkinStep_eq_sub_one]
  change (↑(H (i.val + 1) - H i.val + 1).toNat : ℤ) - 1 = _
  omega

private theorem height_wordOf {n : ℕ} {h : ℤ} {H : Heights} (w : Walk n h H) (m : ℕ)
    (hm : m ≤ n) : motzkinPrefixHeight (wordOf w) m = H m := by
  induction m with
  | zero => simpa only [motzkinPrefixHeight_zero] using w.start.symm
  | succ m ih =>
    have e := motzkinPrefixHeight_step (wordOf w) (⟨m, by omega⟩ : Fin n)
    rw [step_wordOf] at e
    change motzkinPrefixHeight (wordOf w) (m + 1) - motzkinPrefixHeight (wordOf w) m =
      H (m + 1) - H m at e
    have := ih (by omega)
    omega

private theorem prefix_wordOf {n : ℕ} {h : ℤ} {H : Heights} (w : Walk n h H) :
    IsMotzkinPrefix n h (wordOf w) := by
  apply (isMotzkinPrefix_iff n h (wordOf w)).mpr
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [motzkinPrefixHeight_prefix_sum _ hm, height_wordOf w m hm]
    exact w.nonneg m hm
  · rw [motzkinPrefixHeight_total, height_wordOf w n le_rfl, w.finish]

private theorem word_ext {n : ℕ} {p q : Word n}
    (e : ∀ m ≤ n, motzkinPrefixHeight p m = motzkinPrefixHeight q m) : p = q := by
  funext i
  apply Fin.ext
  have h := motzkinPrefixHeight_step p i
  rw [e _ (by omega), e _ i.isLt.le, motzkinPrefixHeight_step] at h
  simp only [motzkinStep_eq_sub_one] at h
  omega

private theorem eq_of_flat {H : Heights} {a b : ℕ} (hab : a ≤ b)
    (hs : ∀ m, a ≤ m → m < b → H (m + 1) = H m) : H b = H a := by
  induction b with
  | zero => rw [show a = 0 by omega]
  | succ b ih =>
    by_cases h : a = b + 1
    · rw [h]
    · exact (hs b (by omega) (by omega)).trans (ih (by omega) fun m ha hm => hs m ha (by omega))

private structure Hump (n : ℕ) (k : ℤ) (H : Heights) (i j : ℕ) : Prop where
  lt : i < j
  bound : j < n
  before : H i = k - 1
  middle : ∀ m, i < m → m ≤ j → H m = k
  after : H (j + 1) = k - 1

private theorem hump_iff {n k : ℕ} {p : Word n} {i j : Fin n} :
    IsMotzkinHump n k p i j ↔ Hump n k (motzkinPrefixHeight p) i.val j.val := by
  rw [isMotzkinHump_iff]
  constructor
  · rintro ⟨hij, hu, hd, hf, hk⟩
    rw [motzkinPrefixHeight_inclusive_sum] at hk
    have hi := motzkinPrefixHeight_step p i
    have hj := motzkinPrefixHeight_step p j
    have mid (m : ℕ) (him : i.val < m) (hmj : m ≤ j.val) : motzkinPrefixHeight p m = (k : ℤ) := by
      rw [← hk]
      apply eq_of_flat (by omega)
      intro l hil hlm
      let x : Fin n := ⟨l, by omega⟩
      have e := (motzkinPrefixHeight_step p x).trans (hf x (by exact hil) (by dsimp [x]; omega))
      exact sub_eq_zero.mp e
    refine ⟨hij, j.isLt, by omega, mid, ?_⟩
    have := mid j.val hij le_rfl
    omega
  · intro h
    have hki := h.middle (i.val + 1) (by omega) h.lt
    refine ⟨h.lt, ?_, ?_, ?_, (motzkinPrefixHeight_inclusive_sum p i).trans hki⟩
    · rw [← motzkinPrefixHeight_step, h.before, hki]
      omega
    · rw [← motzkinPrefixHeight_step, h.after, h.middle _ h.lt le_rfl]
      omega
    · intro r hir hrj
      rw [← motzkinPrefixHeight_step, h.middle _ hir hrj.le,
        h.middle _ (by omega) (by omega), sub_self]

private structure Last (n : ℕ) (k : ℤ) (H : Heights) (t : ℕ) : Prop where
  bound : t < n
  before : H t = 2 * k - 1
  after : ∀ m, t < m → m ≤ n → H m = 2 * k

private theorem last_of_word {n : ℕ} {k : ℤ} {p : Word n} (hp : IsMotzkinPrefix n (2 * k) p)
    (hl : LastNonflatStepUp n p) : ∃ t, Last n k (motzkinPrefixHeight p) t := by
  obtain ⟨t, hu, hf⟩ := (lastNonflatStepUp_iff n p).mp hl
  have after (m : ℕ) (htm : t.val < m) (hm : m ≤ n) : motzkinPrefixHeight p m = 2 * k := by
    rw [← (walk_height hp).finish]
    symm
    apply eq_of_flat hm
    intro l hml hl
    let x : Fin n := ⟨l, hl⟩
    have e := motzkinPrefixHeight_step p x
    rw [hf x (show t.val < l by omega), motzkinStep_values.2.1] at e
    exact sub_eq_zero.mp e
  have e := motzkinPrefixHeight_step p t
  rw [hu, motzkinStep_values.2.2] at e
  have := after (t.val + 1) (by omega) (by omega)
  exact ⟨t.val, t.isLt, by omega, after⟩

private theorem last_marker {n : ℕ} {k : ℤ} {p : Word n} {t : ℕ}
    (h : Last n k (motzkinPrefixHeight p) t) :
    p ⟨t, h.bound⟩ = 2 ∧ ∀ i : Fin n, t < i.val → p i = 1 := by
  constructor
  · apply (motzkinStep_eq_one_iff _).mp
    rw [← motzkinPrefixHeight_step]
    change motzkinPrefixHeight p (t + 1) - motzkinPrefixHeight p t = 1
    rw [h.before, h.after _ (Nat.lt_succ_self t) h.bound]
    omega
  · intro i hi
    apply (motzkinStep_eq_zero_iff _).mp
    rw [← motzkinPrefixHeight_step, h.after _ (by omega) (by omega),
      h.after _ hi i.isLt.le, sub_self]

private theorem Last.isLast {n : ℕ} {k : ℤ} {p : Word n} {t : ℕ}
    (h : Last n k (motzkinPrefixHeight p) t) : LastNonflatStepUp n p :=
  (lastNonflatStepUp_iff n p).mpr ⟨⟨t, h.bound⟩, (last_marker h).1, (last_marker h).2⟩

private theorem Last.ends_iff {n : ℕ} {k : ℤ} {p : Word n} {t : ℕ}
    (h : Last n k (motzkinPrefixHeight p) t) : EndsWithUp n p ↔ t + 1 = n := by
  rw [endsWithUp_iff]
  obtain ⟨hu, hf⟩ := last_marker h
  have ht := h.bound
  constructor
  · rintro ⟨j, hj, hj'⟩
    by_contra hne
    have e := hf j (by omega)
    rw [hj'] at e
    contradiction
  · intro ht
    exact ⟨⟨t, h.bound⟩, ht, hu⟩

private structure Cut (n : ℕ) (k : ℤ) (H : Heights) (i t : ℕ) : Prop where
  last : Last n k H t
  lt : i < t
  before : H i = k - 1
  middle : ∀ m, i < m → m ≤ t → k ≤ H m

private theorem Cut.unique {n : ℕ} {k : ℤ} {H : Heights} {i t i' t' : ℕ}
    (c : Cut n k H i t) (c' : Cut n k H i' t') : i = i' ∧ t = t' := by
  have et : t = t' := by
    rcases lt_trichotomy t t' with h | h | h
    · have := c.last.after t' h c'.last.bound.le
      have := c'.last.before
      omega
    · exact h
    · have := c'.last.after t h c.last.bound.le
      have := c.last.before
      omega
  refine ⟨?_, et⟩
  rcases lt_trichotomy i i' with h | h | h
  · have := c.middle i' h (et.symm ▸ c'.lt.le)
    have := c'.before
    omega
  · exact h
  · have := c'.middle i h (et ▸ c.lt.le)
    have := c.before
    omega

private theorem cut_exists {n : ℕ} {k : ℤ} {H : Heights} {t : ℕ} (hk : 1 ≤ k)
    (w : Walk n (2 * k) H) (l : Last n k H t) : ∃ i, Cut n k H i t := by
  classical
  let s := (Finset.range (t + 1)).filter fun m => H m ≤ k - 1
  have hs : s.Nonempty := ⟨0, by simp [s, w.start]; omega⟩
  let i := s.max' hs
  have hi := Finset.mem_filter.mp (Finset.max'_mem s hs)
  rw [Finset.mem_range] at hi
  change i < t + 1 ∧ H i ≤ k - 1 at hi
  have ht := l.before
  have hit : i < t := by
    by_contra h
    have e : i = t := by omega
    have hi' := hi.2
    rw [e, ht] at hi'
    omega
  have mid (m : ℕ) (him : i < m) (hmt : m ≤ t) : k ≤ H m := by
    by_contra h
    have hm : m ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
    exact (Nat.not_le_of_gt him) (Finset.le_max' s m hm)
  have := mid (i + 1) (by omega) hit
  have := w.step i (by have := l.bound; omega)
  exact ⟨i, l, hit, by omega, mid⟩

-- The indices satisfy `j - i = n - t`: the hump's flat run and the
-- prefix's trailing flat run have the same length.
private def forward (H : Heights) (n : ℕ) (k : ℤ) (i t : ℕ) : Heights :=
  fun m => if m ≤ i then H m else if m ≤ t then k + H (n - (m - (i + 1))) else 2 * k

private def backward (H : Heights) (n : ℕ) (k : ℤ) (i j : ℕ) : Heights :=
  fun m => if m ≤ i then H m else if m ≤ j then k else H (i + 1 + (n - m)) - k

private theorem forward_walk {n i j t : ℕ} {k : ℤ} {H : Heights} (hk : 1 ≤ k)
    (w : Walk n 0 H) (h : Hump n k H i j) (ht : j = i + (n - t)) (htn : t < n) :
    Walk n (2 * k) (forward H n k i t) := by
  have hij := h.lt
  have hjn := h.bound
  have hit : i < t := by omega
  constructor
  · simp [forward, w.start]
  · rw [forward, ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro m hm
    unfold forward
    split_ifs with hmi hmt
    · exact w.nonneg m hm
    · have := w.nonneg (n - (m - (i + 1))) (by omega)
      omega
    · omega
  · intro m hm
    by_cases hl : m < i
    · simpa only [forward, ite_eq_left (show m + 1 ≤ i by omega), ite_eq_left hl.le]
        using w.step m hm
    by_cases he : m = i
    · subst m
      rw [forward, ite_eq_right (by omega), ite_eq_left (by omega),
        show n - (i + 1 - (i + 1)) = n by omega, w.finish,
        forward, ite_eq_left le_rfl, h.before]
      omega
    by_cases hc : m < t
    · have e : n - (m - (i + 1)) = (n - (m + 1 - (i + 1))) + 1 := by omega
      have hs := w.step (n - (m + 1 - (i + 1))) (by omega)
      rw [← e] at hs
      simp only [forward, ite_eq_right (show ¬ m + 1 ≤ i by omega),
        ite_eq_right (show ¬ m ≤ i by omega), ite_eq_left hc.le]
      omega
    by_cases he : m = t
    · subst m
      simp only [forward, ite_eq_right (show ¬ t + 1 ≤ i by omega),
        ite_eq_right (show ¬ t ≤ i by omega), ite_eq_right (show ¬ t + 1 ≤ t by omega),
        ite_eq_left le_rfl]
      rw [show n - (t - (i + 1)) = j + 1 by omega, h.after]
      omega
    · simp only [forward, ite_eq_right (show ¬ m + 1 ≤ i by omega),
        ite_eq_right (show ¬ m ≤ i by omega), ite_eq_right (show ¬ m + 1 ≤ t by omega),
        ite_eq_right (show ¬ m ≤ t by omega), sub_self]
      omega

private theorem forward_cut {n i j t : ℕ} {k : ℤ} {H : Heights}
    (w : Walk n 0 H) (h : Hump n k H i j) (ht : j = i + (n - t)) (htn : t < n) :
    Cut n k (forward H n k i t) i t := by
  have hij := h.lt
  have hjn := h.bound
  have hit : i < t := by omega
  refine ⟨⟨htn, ?_, ?_⟩, hit, ?_, ?_⟩
  · rw [forward, ite_eq_right (by omega), ite_eq_left le_rfl,
      show n - (t - (i + 1)) = j + 1 by omega, h.after]
    omega
  · intro m hm _
    rw [forward, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [forward, ite_eq_left le_rfl, h.before]
  · intro m him hmt
    rw [forward, ite_eq_right (by omega), ite_eq_left hmt]
    have := w.nonneg (n - (m - (i + 1))) (by omega)
    omega

private theorem Cut.next {n i t : ℕ} {k : ℤ} {H : Heights}
    (w : Walk n (2 * k) H) (c : Cut n k H i t) : H (i + 1) = k := by
  have := c.middle (i + 1) (by omega) c.lt
  have := w.step i (c.lt.trans c.last.bound)
  have := c.before
  omega

private theorem backward_walk {n i j t : ℕ} {k : ℤ} {H : Heights} (hk : 1 ≤ k)
    (w : Walk n (2 * k) H) (c : Cut n k H i t) (hj : j = i + (n - t)) :
    Walk n 0 (backward H n k i j) := by
  have hit := c.lt
  have htn := c.last.bound
  have hij : i < j := by omega
  have hjn : j < n := by omega
  constructor
  · simp [backward, w.start]
  · rw [backward, ite_eq_right (by omega), ite_eq_right (by omega), Nat.sub_self, add_zero,
      c.next w, sub_self]
  · intro m hm
    unfold backward
    split_ifs with hmi hmj
    · exact w.nonneg m hm
    · omega
    · have := c.middle (i + 1 + (n - m)) (by omega) (by omega)
      omega
  · intro m hm
    by_cases hl : m < i
    · simpa only [backward, ite_eq_left (show m + 1 ≤ i by omega), ite_eq_left hl.le]
        using w.step m hm
    by_cases he : m = i
    · subst m
      rw [backward, ite_eq_right (by omega), ite_eq_left (show i + 1 ≤ j by omega),
        backward, ite_eq_left le_rfl, c.before]
      omega
    by_cases hc : m < j
    · simp only [backward, ite_eq_right (show ¬ m + 1 ≤ i by omega),
        ite_eq_right (show ¬ m ≤ i by omega), ite_eq_left hc.le]
      omega
    by_cases he : m = j
    · subst m
      rw [backward, ite_eq_right (by omega), ite_eq_right (by omega),
        show i + 1 + (n - (j + 1)) = t by omega, c.last.before,
        backward, ite_eq_right (by omega), ite_eq_left le_rfl]
      omega
    · have e : i + 1 + (n - m) = (i + 1 + (n - (m + 1))) + 1 := by omega
      have hs := w.step (i + 1 + (n - (m + 1))) (by omega)
      rw [← e] at hs
      simp only [backward, ite_eq_right (show ¬ m + 1 ≤ i by omega),
        ite_eq_right (show ¬ m ≤ i by omega), ite_eq_right (show ¬ m + 1 ≤ j by omega),
        ite_eq_right (show ¬ m ≤ j by omega)]
      omega

private theorem backward_hump {n i j t : ℕ} {k : ℤ} {H : Heights}
    (c : Cut n k H i t) (hj : j = i + (n - t)) : Hump n k (backward H n k i j) i j := by
  have hit := c.lt
  have htn := c.last.bound
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · rw [backward, ite_eq_left le_rfl, c.before]
  · intro m him hmj
    rw [backward, ite_eq_right (by omega), ite_eq_left hmj]
  · rw [backward, ite_eq_right (by omega), ite_eq_right (by omega),
      show i + 1 + (n - (j + 1)) = t by omega, c.last.before]
    omega

private theorem backward_forward {n i j t : ℕ} {k : ℤ} {H : Heights}
    (h : Hump n k H i j) (ht : j = i + (n - t)) (htn : t < n) {m : ℕ} (hm : m ≤ n) :
    backward (forward H n k i t) n k i j m = H m := by
  have hij := h.lt
  by_cases hmi : m ≤ i
  · simp [backward, forward, hmi]
  by_cases hmj : m ≤ j
  · simpa [backward, hmi, hmj] using (h.middle m (by omega) hmj).symm
  · simp only [backward, ite_eq_right hmi, ite_eq_right hmj, forward,
      ite_eq_right (show ¬ i + 1 + (n - m) ≤ i by omega),
      ite_eq_left (show i + 1 + (n - m) ≤ t by omega),
      show n - (i + 1 + (n - m) - (i + 1)) = m by omega]
    omega

private theorem forward_backward {n i j t : ℕ} {k : ℤ} {H : Heights}
    (c : Cut n k H i t) (hj : j = i + (n - t)) {m : ℕ} (hm : m ≤ n) :
    forward (backward H n k i j) n k i t m = H m := by
  have htn := c.last.bound
  have hit := c.lt
  by_cases hmi : m ≤ i
  · simp [forward, backward, hmi]
  by_cases hmt : m ≤ t
  · simp only [forward, ite_eq_right hmi, ite_eq_left hmt, backward,
      ite_eq_right (show ¬ n - (m - (i + 1)) ≤ i by omega),
      ite_eq_right (show ¬ n - (m - (i + 1)) ≤ j by omega),
      show i + 1 + (n - (n - (m - (i + 1)))) = m by omega]
    omega
  · simpa [forward, hmi, hmt] using (c.last.after m (by omega) hm).symm

private theorem Cut.of_heights {n : ℕ} {k : ℤ} {H G : Heights} {i t : ℕ}
    (c : Cut n k H i t) (e : ∀ m ≤ n, G m = H m) : Cut n k G i t := by
  have hi := c.lt.trans c.last.bound
  exact ⟨⟨c.last.bound, (e t c.last.bound.le).trans c.last.before,
    fun m htm hm => (e m hm).trans (c.last.after m htm hm)⟩, c.lt,
    (e i hi.le).trans c.before,
    fun m him hmt => (e m (hmt.trans c.last.bound.le)).symm ▸ c.middle m him hmt⟩

private theorem Hump.of_heights {n : ℕ} {k : ℤ} {H G : Heights} {i j : ℕ}
    (c : Hump n k H i j) (e : ∀ m ≤ n, G m = H m) : Hump n k G i j := by
  exact ⟨c.lt, c.bound, (e i (c.lt.trans c.bound).le).trans c.before,
    fun m him hmj => (e m (hmj.trans c.bound.le)).trans (c.middle m him hmj),
    (e (j + 1) c.bound).trans c.after⟩

private abbrev cutTime (n i j : ℕ) : ℕ := n - (j - i)

private theorem cutTime_spec {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    j = i + (n - cutTime n i j) ∧ cutTime n i j < n := by
  dsimp [cutTime]
  omega

private theorem imageWalk {n k : ℕ} {p : Word n} {i j : Fin n} (hk : 1 ≤ k)
    (hp : IsMotzkinPrefix n 0 p) (hh : IsMotzkinHump n k p i j) :
    Walk n (2 * (k : ℤ)) (forward (motzkinPrefixHeight p) n k i.val (cutTime n i.val j.val)) := by
  have h := hump_iff.mp hh
  have ht := cutTime_spec h.lt h.bound
  exact forward_walk (by exact_mod_cast hk) (walk_height hp) h ht.1 ht.2

private def image {n k : ℕ} {p : Word n} {i j : Fin n} (hk : 1 ≤ k)
    (hp : IsMotzkinPrefix n 0 p) (hh : IsMotzkinHump n k p i j) : Word n :=
  wordOf (imageWalk hk hp hh)

private theorem image_height {n k : ℕ} {p : Word n} {i j : Fin n} (hk : 1 ≤ k)
    (hp : IsMotzkinPrefix n 0 p) (hh : IsMotzkinHump n k p i j) (m : ℕ) (hm : m ≤ n) :
    motzkinPrefixHeight (image hk hp hh) m =
      forward (motzkinPrefixHeight p) n k i.val (cutTime n i.val j.val) m :=
  height_wordOf (imageWalk hk hp hh) m hm

private theorem image_cut {n k : ℕ} {p : Word n} {i j : Fin n} (hk : 1 ≤ k)
    (hp : IsMotzkinPrefix n 0 p) (hh : IsMotzkinHump n k p i j) :
    Cut n k (motzkinPrefixHeight (image hk hp hh)) i.val (cutTime n i.val j.val) := by
  have h := hump_iff.mp hh
  have ht := cutTime_spec h.lt h.bound
  exact (forward_cut (walk_height hp) h ht.1 ht.2).of_heights (image_height hk hp hh)

private theorem recover_height {n k : ℕ} {p : Word n} {i j : Fin n} (hk : 1 ≤ k)
    (hp : IsMotzkinPrefix n 0 p) (hh : IsMotzkinHump n k p i j) (m : ℕ) (hm : m ≤ n) :
    backward (motzkinPrefixHeight (image hk hp hh)) n k i.val j.val m =
      motzkinPrefixHeight p m := by
  have h := hump_iff.mp hh
  have ht := cutTime_spec h.lt h.bound
  have e := backward_forward h ht.1 ht.2 hm
  have hi := (image_cut hk hp hh).lt
  unfold backward at e ⊢
  split_ifs with hmi hmj
  · rw [image_height hk hp hh _ hm]
    simpa only [ite_eq_left hmi] using e
  · simpa only [ite_eq_right hmi, ite_eq_left hmj] using e
  · rw [image_height hk hp hh _ (by have := j.isLt; omega)]
    simpa only [ite_eq_right hmi, ite_eq_right hmj] using e

private def toLast (n : ℕ) (q : MotzkinHumpFamily n) : MotzkinLastUpEvenFamily n := by
  rcases q with ⟨⟨k, p, i, j⟩, hk, hkn, hp, hh⟩
  exact ⟨⟨k, image hk hp hh⟩, hk, hkn, prefix_wordOf (imageWalk hk hp hh),
    (image_cut hk hp hh).last.isLast⟩

private theorem toLast_injective (n : ℕ) : Function.Injective (toLast n) := by
  rintro ⟨⟨k, p, i, j⟩, hk, hkn, hp, hh⟩ ⟨⟨k', p', i', j'⟩, hk', hkn', hp', hh'⟩ e
  have ek : k = k' := congrArg (fun q : MotzkinLastUpEvenFamily n => q.val.1) e
  subst k'
  have ep : image hk hp hh = image hk' hp' hh' :=
    congrArg (fun q : MotzkinLastUpEvenFamily n => q.val.2) e
  have c := image_cut hk hp hh
  have c' := image_cut hk' hp' hh'
  rw [← ep] at c'
  obtain ⟨ei, et⟩ := c.unique c'
  have hij : i.val < j.val := (hump_iff.mp hh).lt
  have hi'j' : i'.val < j'.val := (hump_iff.mp hh').lt
  have eiVal : i.val = i'.val := ei
  have etVal : n - (j.val - i.val) = n - (j'.val - i'.val) := et
  have ej : j.val = j'.val := by
    have := j.isLt
    have := j'.isLt
    omega
  have ei' : i = i' := Fin.ext eiVal
  have ej' : j = j' := Fin.ext ej
  subst i'
  subst j'
  have hw : p = p' := by
    apply word_ext
    intro m hm
    rw [← recover_height hk hp hh m hm, ← recover_height hk' hp' hh' m hm, ep]
  subst p'
  rfl

private theorem toLast_surjective (n : ℕ) : Function.Surjective (toLast n) := by
  rintro ⟨⟨k, p⟩, hk, hkn, hp, hl⟩
  obtain ⟨t, l⟩ := last_of_word hp hl
  obtain ⟨i, c⟩ := cut_exists (by exact_mod_cast hk) (walk_height hp) l
  let j := i + (n - t)
  have h := backward_hump c (j := j) rfl
  let w := backward_walk (by exact_mod_cast hk) (walk_height hp) c (j := j) rfl
  let i' : Fin n := ⟨i, h.lt.trans h.bound⟩
  let j' : Fin n := ⟨j, h.bound⟩
  have hh : IsMotzkinHump n k (wordOf w) i' j' :=
    hump_iff.mpr (h.of_heights (height_wordOf w))
  refine ⟨⟨⟨k, wordOf w, i', j'⟩, hk, hkn, prefix_wordOf w, hh⟩, Subtype.ext (Prod.ext rfl ?_)⟩
  change image hk (prefix_wordOf w) hh = p
  apply word_ext
  intro m hm
  rw [image_height hk (prefix_wordOf w) hh m hm]
  change forward (motzkinPrefixHeight (wordOf w)) n (k : ℤ) i (cutTime n i j) m = _
  have htn := l.bound
  have et : cutTime n i j = t := by dsimp [cutTime, j]; omega
  rw [et]
  have e := forward_backward c (j := j) rfl hm
  unfold forward at e ⊢
  split_ifs with hmi hmt
  · rw [height_wordOf w m hm]
    simpa only [ite_eq_left hmi] using e
  · rw [height_wordOf w _ (by omega)]
    simpa only [ite_eq_right hmi, ite_eq_left hmt] using e
  · simpa only [ite_eq_right hmi, ite_eq_right hmt] using e

end motzkinHumpFamily_equiv_lastUpEvenFamily

open motzkinHumpFamily_equiv_lastUpEvenFamily

/-- **Humps correspond to last-up prefixes of twice the height.** Use the steps $U = (1,1)$,
$F = (1,0)$ and $D = (1,-1)$. A Motzkin prefix of length $n$ ending at height $h$ is a word of
$n$ steps that never goes below height $0$ and ends at height $h$; a Motzkin path is a Motzkin
prefix ending at height $0$. A hump of height $k$ in a path is a pair of an up step and a later
down step with only flat steps between them, where the up step ends at height $k$; the hump is
a peak when the down step immediately follows the up step. For every natural number $n$ there
is a bijection from the set of triples $(k, P, h)$ with $1 \le k \le \lfloor n/2 \rfloor$, $P$
a Motzkin path of length $n$ and $h$ a hump of height $k$ in $P$, to the set of pairs $(k, p)$
with $1 \le k \le \lfloor n/2 \rfloor$ and $p$ a Motzkin prefix of length $n$ ending at height
$2k$ that contains a $U$ after which every step is $F$. This bijection keeps the index $k$, and
the hump $h$ is a peak exactly when the image path $p$ ends with an up step.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public theorem motzkinHumpFamily_equiv_lastUpEvenFamily (n : ℕ) :
    ∃ e : MotzkinHumpFamily n ≃ MotzkinLastUpEvenFamily n,
      (∀ q, (e q).val.1 = q.val.1) ∧
        ∀ q, IsMotzkinPeak n q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 ↔
          EndsWithUp n (e q).val.2 := by
  let e := Equiv.ofBijective (toLast n) ⟨toLast_injective n, toLast_surjective n⟩
  refine ⟨e, ?_, ?_⟩
  · rintro ⟨⟨k, p, i, j⟩, hk, hkn, hp, hh⟩
    rfl
  · rintro ⟨⟨k, p, i, j⟩, hk, hkn, hp, hh⟩
    change IsMotzkinPeak n k p i j ↔ EndsWithUp n (image hk hp hh)
    rw [isMotzkinPeak_iff, and_iff_right hh, (image_cut hk hp hh).last.ends_iff]
    have hij := (hump_iff.mp hh).lt
    have hjn := j.isLt
    dsimp [cutTime]
    omega

end MetaMathlibExt
