/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Sequences.ThrowbackSequences
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Ring

/-!
# Frequencies of leaders in throwback sequences

Every value in an injective sequence of positive integers has a nonzero limiting frequency
among the leaders. For a fixed value, we show that its leader times are eventually periodic.
-/

namespace MetaMathlibExt

namespace throwbackSequence_limiting_frequency_ne_zero

open Filter

private abbrev row (X : ℕ → ℕ) (t : ℕ) : ℕ → ℕ := (throwback id)^[t] X

private theorem step (X : ℕ → ℕ) (t i : ℕ) :
    row X (t + 1) i =
      if i < row X t 0 then row X t (i + 1) else if i = row X t 0 then row X t 0 else
        row X t i := by
  simp only [row, Function.iterate_succ_apply', throwback, id_eq]

private theorem row_injective {X : ℕ → ℕ} (hinj : Function.Injective X) (t : ℕ) :
    Function.Injective (row X t) := by
  induction t with
  | zero => exact hinj
  | succ t ih =>
    intro i j h
    simp only [step] at h
    split_ifs at h <;> have := ih h <;> omega

private theorem row_pos {X : ℕ → ℕ} (hX : ∀ i, 0 < X i) (t i : ℕ) : 0 < row X t i := by
  induction t generalizing i with
  | zero => exact hX i
  | succ t ih => rw [step]; split_ifs <;> apply ih

/-- Among the first `p` distinct positive entries, at least one has value at least `p`. -/
private theorem large_entry {s : ℕ → ℕ} (hs : ∀ i, 0 < s i) (hinj : Function.Injective s)
    (p : ℕ) (hp : 0 < p) : ∃ i < p, p ≤ s i := by
  by_contra! h
  let f (i : Fin p) : Fin (p - 1) := ⟨s i - 1, by
    have := h i i.isLt
    have := hs i
    omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hv : s i - 1 = s j - 1 := congrArg Fin.val hij
    have := hs i
    have := hs j
    exact Fin.ext (hinj (by omega))
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at this
  omega

/-- Every entry reaches the front when enough throwbacks have been performed. -/
private theorem reaches {X : ℕ → ℕ} (hX : ∀ i, 0 < X i) (hinj : Function.Injective X)
    (p t : ℕ) : ∃ k ≥ t, row X k 0 = row X t p := by
  classical
  induction p using Nat.strong_induction_on generalizing t with
  | ind p ih =>
    rcases p with _ | p
    · exact ⟨t, le_rfl, rfl⟩
    obtain ⟨i, hi, hv⟩ := large_entry (row_pos hX t) (row_injective hinj t) (p + 1) (by omega)
    obtain ⟨k, hk, he⟩ := ih i hi t
    have hex : ∃ d, p + 1 ≤ row X (t + d) 0 := ⟨k - t, by rwa [Nat.add_sub_of_le hk, he]⟩
    -- Until the first leader of value at least `p + 1`, the entry at that position stays put.
    let d := Nat.find hex
    have fixed (e : ℕ) (hle : e ≤ d) : row X (t + e) (p + 1) = row X t (p + 1) := by
      induction e with
      | zero => rfl
      | succ e he =>
        have hsmall : ¬ p + 1 ≤ row X (t + e) 0 := Nat.find_min hex (by omega : e < d)
        rw [← Nat.add_assoc, step, ite_eq_right (by omega), ite_eq_right (by omega)]
        exact he (by omega)
    have hlarge : p + 1 ≤ row X (t + d) 0 := Nat.find_spec hex
    obtain ⟨l, hl, heq⟩ := ih p (by omega) (t + d + 1)
    exact ⟨l, by omega, heq.trans (by rw [step, ite_eq_left (by omega), fixed d le_rfl])⟩

/-- Once a value at most `b` is within the first `b + 1` positions, it stays there. -/
private theorem stays {X : ℕ → ℕ} {v b t : ℕ} (hv : v ≤ b)
    (h : ∃ i ≤ b, row X t i = v) (k : ℕ) (hk : t ≤ k) : ∃ i ≤ b, row X k i = v := by
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k hk ih =>
    obtain ⟨i, hi, he⟩ := ih
    cases i with
    | zero => exact ⟨v, hv, by simp [step, he]⟩
    | succ i =>
      by_cases hl : i < row X k 0
      · exact ⟨i, by omega, by rwa [step, ite_eq_left hl]⟩
      · exact ⟨i + 1, hi, by rwa [step, ite_eq_right (by omega), ite_eq_right (by omega)]⟩

/-- On a tail, every entry of value at most `b` is among the first `b + 1` positions. -/
private theorem clean_tail {X : ℕ → ℕ} (hX : ∀ i, 0 < X i) (hinj : Function.Injective X)
    (b : ℕ) : ∀ᶠ t in atTop, ∀ i, b < i → b < row X t i := by
  classical
  have clean (v : Fin (b + 1)) : ∀ᶠ t in atTop, ∀ i, row X t i = v → i ≤ b := by
    by_cases h : ∃ t i, row X t i = v
    · obtain ⟨t, i, hit⟩ := h
      obtain ⟨k, _, hk⟩ := reaches hX hinj i t
      filter_upwards [eventually_ge_atTop k] with l hl
      obtain ⟨q, hq, he⟩ := stays (Nat.le_of_lt_succ v.isLt)
        ⟨0, Nat.zero_le _, hk.trans hit⟩ l hl
      intro j hj
      rwa [row_injective hinj l (hj.trans he.symm)]
    · exact Eventually.of_forall fun t i hi => (h ⟨t, i, hi⟩).elim
  filter_upwards [eventually_all.mpr clean] with t ht i hi
  by_contra! h
  exact hi.not_ge (ht ⟨row X t i, by omega⟩ i rfl)

/-- After the small values have entered the prefix, its entries with all larger values
identified form a finite deterministic system. -/
private theorem periodic_hits {X : ℕ → ℕ} (hX : ∀ i, 0 < X i) (hinj : Function.Injective X)
    (j : ℕ) : ∃ a d, 0 < d ∧ row X a 0 = X j ∧
      ∀ n ≥ a, row X (n + d) 0 = X j ↔ row X n 0 = X j := by
  let b := X j
  obtain ⟨K, hK⟩ := eventually_atTop.mp (clean_tail hX hinj b)
  let clip (t i : ℕ) := min (row X t i) (b + 1)
  let state (t : ℕ) (i : Fin (b + 1)) : Fin (b + 2) :=
    ⟨clip t i, by dsimp [clip]; omega⟩
  have next {t u : ℕ} (ht : K ≤ t) (hu : K ≤ u) (he : state t = state u) :
      state (t + 1) = state (u + 1) := by
    have eqv (i : ℕ) : clip t i = clip u i := by
      by_cases hi : i ≤ b
      · exact congrArg Fin.val (congrFun he ⟨i, by omega⟩)
      · have := hK t ht i (by omega)
        have := hK u hu i (by omega)
        dsimp [clip]
        omega
    have head := eqv 0
    dsimp [clip] at head
    funext i
    apply Fin.ext
    change min (row X (t + 1) i) (b + 1) = min (row X (u + 1) i) (b + 1)
    rw [step, step]
    have hi := i.isLt
    by_cases h : (i : ℕ) < row X t 0
    · rw [ite_eq_left h, ite_eq_left (by omega)]
      exact eqv (i + 1 : ℕ)
    · rw [ite_eq_right h, ite_eq_right (by omega : ¬ (i : ℕ) < row X u 0)]
      by_cases h' : (i : ℕ) = row X t 0
      · rw [ite_eq_left h', ite_eq_left (by omega)]
        exact head
      · rw [ite_eq_right h', ite_eq_right (by omega)]
        exact eqv i
  obtain ⟨k, _, hk⟩ := reaches hX hinj j 0
  obtain ⟨t, ht, u, _, htu, heq⟩ := (Set.Ici_infinite (max K k)).exists_lt_map_eq_of_mapsTo
    (f := state) (fun _ _ => Set.mem_univ _) Set.finite_univ
  change max K k ≤ t at ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu.le
  have repeats (n : ℕ) (hn : t ≤ n) : state n = state (n + d) := by
    induction n, hn using Nat.le_induction with
    | base => exact heq
    | succ n hn ih =>
      rw [Nat.add_right_comm n 1 d]
      exact next (by omega) (by omega) ih
  obtain ⟨q, _, hq⟩ := stays (le_refl b) ⟨0, Nat.zero_le _, hk⟩ t (by omega)
  obtain ⟨a, ha, hit⟩ := reaches hX hinj q t
  refine ⟨a, d, by omega, hit.trans hq, fun n hn => ?_⟩
  have eqhead : clip n 0 = clip (n + d) 0 :=
    congrArg Fin.val (congrFun (repeats n (by omega)) ⟨0, by omega⟩)
  change row X (n + d) 0 = b ↔ row X n 0 = b
  dsimp [clip] at eqhead
  omega

/-- Subtracting the mean count per period leaves a bounded error in every prefix count. -/
private theorem frequency_of_period {P : ℕ → Prop} [DecidablePred P] {a d : ℕ}
    (hd : 0 < d) (ha : P a) (period : ∀ n ≥ a, P (n + d) ↔ P n) :
    ∃ c : ℝ, c ≠ 0 ∧ Tendsto (fun n : ℕ => (Nat.count P n : ℝ) / n) atTop (nhds c) := by
  let hits := Nat.count P (a + d) - Nat.count P a
  have hlt := Nat.count_strict_mono ha (by omega : a < a + d)
  have hpos : 0 < hits := Nat.sub_pos_of_lt hlt
  have block (n : ℕ) (hn : a ≤ n) : Nat.count P (n + d) = Nat.count P n + hits := by
    induction n, hn using Nat.le_induction with
    | base => dsimp [hits]; omega
    | succ n hn ih =>
      rw [Nat.add_right_comm n 1 d, Nat.count_succ, ih, Nat.count_succ P n]
      simp only [period n hn, Nat.add_right_comm]
  let c : ℝ := hits / (d : ℝ)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmean : c * d = hits := div_mul_cancel₀ _ hd'
  let err (n : ℕ) : ℝ := Nat.count P n - c * n
  have rep (n : ℕ) (hn : a ≤ n) : err (n + d) = err n := by
    simp only [err, block n hn, Nat.cast_add, mul_add, hmean]
    ring
  have finite_err : (Set.range err).Finite := by
    apply ((Finset.range (a + d)).finite_toSet.image err).subset
    rintro _ ⟨n, rfl⟩
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hn : n < a + d
      · exact ⟨n, Finset.mem_range.mpr hn, rfl⟩
      · have he := rep (n - d) (by omega)
        rw [Nat.sub_add_cancel (by omega : d ≤ n)] at he
        rw [he]
        exact ih (n - d) (by omega)
  obtain ⟨lo, hlo⟩ := finite_err.bddBelow
  obtain ⟨hi, hhi⟩ := finite_err.bddAbove
  have hzero : Tendsto (fun n : ℕ => err n / n) atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero (.of_forall fun n => hlo (Set.mem_range_self n))
      (.of_forall fun n => hhi (Set.mem_range_self n)) tendsto_natCast_atTop_atTop
  refine ⟨c, div_ne_zero (by exact_mod_cast hpos.ne') hd', ?_⟩
  apply (show Tendsto (fun n : ℕ => err n / n + c) atTop (nhds c) by
    simpa using hzero.add_const c).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [err, sub_div, mul_div_cancel_right₀ _ hn']

end throwbackSequence_limiting_frequency_ne_zero

open throwbackSequence_limiting_frequency_ne_zero in
/-- **Every term has a nonzero limiting frequency.** Let $X = (x_0, x_1, \dots)$ be a sequence of
pairwise distinct positive integers, and let $T(X) = (t_0, t_1, \dots)$ be its throwback
sequence. Then for every $j$, the proportion $\#\{k < N : t_k = x_j\} / N$ of terms equal to
$x_j$ among the first $N$ terms of $T(X)$ converges, as $N \to \infty$, to a nonzero real number.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Corollary 5
(`jis-2025-25.5.1-cor-5`). -/
public theorem throwbackSequence_limiting_frequency_ne_zero (X : ℕ → ℕ)
    (hX : ∀ n, 0 < X n) (hinj : Function.Injective X) (j : ℕ) :
    ∃ c : ℝ, c ≠ 0 ∧ Filter.Tendsto
      (fun N : ℕ =>
        ((((Finset.range N).filter fun k => throwbackSequence X k = X j).card : ℕ) : ℝ) / N)
      Filter.atTop (nhds c) := by
  obtain ⟨a, d, hd, ha, period⟩ := periodic_hits hX hinj j
  simpa only [Nat.count_eq_card_filter_range] using
    frequency_of_period (P := fun k => throwbackSequence X k = X j) hd ha period

end MetaMathlibExt
