/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Fintype.Pi
public import MathlibExt.Combinatorics.Enumerative.CatalanWordsCapacity
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Maximum capacity of restricted smooth words

The degree of the capacity distribution is the largest amount of water a word can hold.
We bound the number of columns at each water depth, then attain the bound with two walls
enclosing a valley whose floor alternates between one and two.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Smooth words.** For $n \ge 0$, the set $\mathcal{R}_n$ of smooth words of length $n$ consists
of the words $w = w_1 \cdots w_n$ of positive integers with $w_1 = 1$ (when $n \ge 1$) and
$|w_{i+1} - w_i| \le 1$ for $1 \le i < n$.

The letters of a smooth word of length $n$ are at most $n$, so $\mathcal{R}_n$ is finite.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of smooth words. -/
public def smoothWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun w =>
    (∀ i : Fin n, i.val = 0 → w i = 1) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1 ∧ w i ≤ w j + 1

/-- **Characterization of smooth words.** For a natural number $n$, let $\mathcal{R}_n$ be the
set of smooth words of length $n$, defined as the words $w = w_1 \cdots w_n$ with letters in
$\{1, \dots, n\}$ such that $w_1 = 1$ when $n \ge 1$, and $w_{k+1} \le w_k + 1$ and
$w_k \le w_{k+1} + 1$ for $1 \le k < n$. A word $w = w_1 \cdots w_n$ of natural numbers belongs
to $\mathcal{R}_n$ if and only if $w_k \ge 1$ for every $k$, $w_1 = 1$ when $n \ge 1$, and
$w_{k+1} \le w_k + 1$ and $w_k \le w_{k+1} + 1$ for $1 \le k < n$. In particular, the bound
$w_k \le n$ on the letters is automatic.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of smooth words. -/
public theorem mem_smoothWords_iff {n : ℕ} (w : Fin n → ℕ) :
    w ∈ smoothWords n ↔ (∀ i, 1 ≤ w i) ∧ (∀ i : Fin n, i.val = 0 → w i = 1) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1 ∧ w i ≤ w j + 1 := by
  simp only [smoothWords, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hb, h0, hg⟩
    exact ⟨fun i => (hb i).1, h0, hg⟩
  · rintro ⟨h1, h0, hg⟩
    have key : ∀ k (hk : k < n), w ⟨k, hk⟩ ≤ k + 1 := by
      intro k
      induction k with
      | zero => intro hk; rw [h0 ⟨0, hk⟩ rfl]
      | succ k ih =>
        intro hk
        have h₁ := (hg ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl).1
        have h₂ := ih (by omega)
        omega
    refine ⟨fun i => ⟨h1 i, ?_⟩, h0, hg⟩
    have := key i.val i.isLt
    rw [Fin.eta] at this
    omega

/-- **Restricted smooth words.** For $n \ge 0$, the set $\mathcal{R}^{\ast}_n$ of restricted smooth
words of length $n$ consists of the smooth words of length $n$ in which no two adjacent letters
are both equal to $1$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of restricted smooth words. -/
public def restrictedSmoothWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (smoothWords n).filter fun w => ∀ i j : Fin n, j.val = i.val + 1 → ¬(w i = 1 ∧ w j = 1)

end

namespace restrictedSmoothWords_capacity_natDegree

open Finset Polynomial

private def depth {n : ℕ} (w : Fin n → ℕ) (i : Fin n) : ℕ :=
  min ((univ.filter (· < i)).sup w) ((univ.filter (i < ·)).sup w) - w i

private theorem lt_depth {n : ℕ} {w : Fin n → ℕ} {i : Fin n} {k : ℕ} :
    k < depth w i ↔ (∃ a < i, w i + k < w a) ∧ (∃ b > i, w i + k < w b) := by
  simp only [depth, Nat.lt_sub_iff_add_lt, Nat.add_comm k, lt_min_iff, Finset.lt_sup_iff,
    mem_filter, mem_univ, true_and]

private def UnitSteps {n : ℕ} (f : Fin n → ℕ) : Prop :=
  ∀ i j, j.val = i.val + 1 → f j ≤ f i + 1 ∧ f i ≤ f j + 1

private theorem depth_steps {n : ℕ} {w : Fin n → ℕ} (h : UnitSteps w) : UnitSteps (depth w) := by
  intro i j hij
  obtain ⟨hu, hd⟩ := h i j hij
  have hlt : i < j := show i.val < j.val by omega
  constructor
  · by_contra! hf
    obtain ⟨⟨a, ha, hva⟩, ⟨b, hb, hvb⟩⟩ := lt_depth.mp hf
    have hai : a < i := by
      by_contra! hia
      have : a = i := Fin.ext (by change a.val < j.val at ha; omega)
      subst a
      omega
    exact (lt_irrefl (depth w i)) (lt_depth.mpr
      ⟨⟨a, hai, by omega⟩, ⟨b, hlt.trans hb, by omega⟩⟩)
  · by_contra! hf
    obtain ⟨⟨a, ha, hva⟩, ⟨b, hb, hvb⟩⟩ := lt_depth.mp hf
    have hjb : j < b := by
      by_contra! hbj
      have : b = j := Fin.ext (by change i.val < b.val at hb; omega)
      subst b
      omega
    exact (lt_irrefl (depth w j)) (lt_depth.mpr
      ⟨⟨a, ha.trans hlt, by omega⟩, ⟨b, hjb, by omega⟩⟩)

private theorem steps_dist {n : ℕ} {f : Fin n → ℕ} (h : UnitSteps f) (i j : Fin n)
    (hij : i ≤ j) : f j + i.val ≤ f i + j.val ∧ f i + i.val ≤ f j + j.val := by
  obtain ⟨d, he⟩ := Nat.exists_eq_add_of_le (show i.val ≤ j.val from hij)
  induction d generalizing j with
  | zero =>
    have := Fin.ext (show j.val = i.val by omega)
    subst j
    simp
  | succ d ih =>
    let k : Fin n := ⟨i.val + d, by omega⟩
    have hk : k.val = i.val + d := rfl
    obtain ⟨h₁, h₂⟩ := ih k (show i.val ≤ k.val by omega) hk
    obtain ⟨h₃, h₄⟩ := h k j (by omega)
    omega

-- First crossing of a predicate on an interval of indices.
private theorem crossing {n : ℕ} (P : Fin n → Prop) {a b : Fin n}
    (hab : a ≤ b) (ha : ¬ P a) (hb : P b) :
    ∃ i j : Fin n, a ≤ i ∧ j ≤ b ∧ j.val = i.val + 1 ∧ ¬ P i ∧ P j ∧
      (∀ k, a ≤ k → k < j → ¬ P k) := by
  classical
  let s := (Icc a b).filter P
  have hbs : b ∈ s := mem_filter.mpr ⟨mem_Icc.mpr ⟨hab, le_rfl⟩, hb⟩
  let j := s.min' ⟨b, hbs⟩
  obtain ⟨⟨haj, hjb⟩, hj⟩ := (mem_filter.mp (min'_mem s ⟨b, hbs⟩)).imp_left mem_Icc.mp
  have hlt : a < j := lt_of_le_of_ne haj (fun he => ha (he.symm ▸ hj))
  have hl (k) (hk : a ≤ k) (hkj : k < j) : ¬ P k := fun hp =>
    (not_le.mpr hkj) (min'_le _ _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hk, hkj.le.trans hjb⟩, hp⟩))
  let i : Fin n := ⟨j.val - 1, by omega⟩
  have hi : i.val = j.val - 1 := rfl
  change a.val < j.val at hlt
  have hai : a ≤ i := show a.val ≤ i.val by omega
  exact ⟨i, j, hai, hjb, by omega, hl i hai (show i.val < j.val by omega), hj, hl⟩

private theorem depth_ends {n : ℕ} (w : Fin (n + 1) → ℕ) :
    depth w 0 = 0 ∧ depth w (Fin.last n) = 0 := by
  constructor <;> apply Nat.eq_zero_of_not_pos <;> rw [lt_depth]
  · simp
  · rintro ⟨_, b, hb, _⟩
    exact (Fin.le_last b).not_gt hb

-- Each new height has a dry first occurrence. A wet column is also followed by a dry
-- column which repeats an earlier height or lies below it.
private theorem dry_count {n : ℕ} {w : Fin (n + 1) → ℕ} (hs : UnitSteps w) (h₀ : w 0 = 1)
    {x b : Fin (n + 1)} (hx : 0 < depth w x) {H : ℕ} (hH : H ≤ w b) :
    H + 1 ≤ (univ.filter (fun i => depth w i = 0)).card := by
  let dry := univ.filter (fun i => depth w i = 0)
  obtain ⟨i, j, _, _, hij, hi, hj, _⟩ := crossing (fun i => depth w i = 0)
    (Fin.le_last x) (by omega) (depth_ends w).2
  obtain ⟨⟨a, ha, hva⟩, _⟩ := lt_depth.mp (Nat.pos_of_ne_zero hi)
  have haj : a < j := show a.val < j.val by change a.val < i.val at ha; omega
  have hwaj : w j ≤ w a := by have := (hs i j hij).1; omega
  have first (k : ℕ) (hk : k ∈ range H) :
      ∃ t : Fin (n + 1), w t = k + 1 ∧ ∀ u < t, w u < w t := by
    rw [mem_range] at hk
    by_cases he : k = 0
    · exact ⟨0, by omega, by simp⟩
    obtain ⟨l, t, _, _, hlt, hl, ht, hfirst⟩ := crossing (fun i => k + 1 ≤ w i)
      (Fin.zero_le b) (by omega) (by omega)
    have := (hs l t hlt).1
    exact ⟨t, by omega, fun u hu => by have := hfirst u (Fin.zero_le _) hu; omega⟩
  classical
  choose f hf using first
  let g (k : ℕ) := if hk : k ∈ range H then f k hk else 0
  have hg (k) (hk : k ∈ range H) : w (g k) = k + 1 ∧ ∀ u < g k, w u < w (g k) := by
    simpa only [g, dite_eq_left hk] using hf k hk
  have bound : (range H).card ≤ (dry.erase j).card := by
    apply card_le_card_of_injOn g
    · intro k hk
      obtain ⟨_, hrec⟩ := hg k hk
      apply mem_erase.mpr
      constructor
      · rintro he
        rw [he] at hrec
        exact (hrec a haj).not_ge hwaj
      · refine mem_filter.mpr ⟨mem_univ _, Nat.eq_zero_of_not_pos ?_⟩
        rintro hp
        obtain ⟨⟨u, hu, hwu⟩, _⟩ := lt_depth.mp hp
        have := hrec u hu
        omega
    · intro k hk l hl he
      have := (hg k hk).1
      have := (hg l hl).1
      rw [he] at *
      omega
  have hjd : j ∈ dry := mem_filter.mpr ⟨mem_univ _, hj⟩
  rw [card_range, card_erase_of_mem hjd] at bound
  have := card_pos.mpr ⟨j, hjd⟩
  change H + 1 ≤ dry.card
  omega

private theorem twice_at_level {n : ℕ} {w : Fin (n + 1) → ℕ} (hs : UnitSteps w)
    {x : Fin (n + 1)} {k : ℕ} (hk : 0 < k) (hkx : k < depth w x) :
    2 ≤ (univ.filter (fun i => depth w i = k)).card := by
  obtain ⟨hz, he⟩ := depth_ends w
  obtain ⟨a, b, _, hbx, hab, ha, hb, _⟩ := crossing (fun i => k ≤ depth w i)
    (Fin.zero_le x) (by omega) (by omega)
  obtain ⟨c, d, hxc, _, hcd, hc, hd, _⟩ := crossing (fun i => depth w i ≤ k)
    (Fin.le_last x) (by omega) (by omega)
  have := (depth_steps hs a b hab).1
  have := (depth_steps hs c d hcd).2
  refine one_lt_card.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, by omega⟩, d,
    mem_filter.mpr ⟨mem_univ _, by omega⟩, ?_⟩
  exact ne_of_lt (lt_of_le_of_lt (hbx.trans hxc) (show c.val < d.val by omega))

private def wet {n : ℕ} (w : Fin n → ℕ) (k : ℕ) : ℕ :=
  (univ.filter (fun i => k < depth w i)).card

private theorem layer_bounds {n B : ℕ} {w : Fin (n + 1) → ℕ} (hs : UnitSteps w)
    {x : Fin (n + 1)} (hB : B ≤ (univ.filter (fun i => depth w i = 0)).card)
    (k : ℕ) (hk : k < depth w x) : wet w k + B + 2 * k ≤ n + 1 := by
  induction k with
  | zero =>
    have h := univ.card_filter_add_card_filter_not (fun i => 0 < depth w i)
    simp only [not_lt, Nat.le_zero, card_univ, Fintype.card_fin] at h
    unfold wet
    omega
  | succ k ih =>
    have h := (univ.filter (fun i => k < depth w i)).card_filter_add_card_filter_not
      (fun i => k + 1 < depth w i)
    have h₁ (i : Fin (n + 1)) : (k < depth w i ∧ k + 1 < depth w i) ↔ k + 1 < depth w i := by omega
    have h₂ (i : Fin (n + 1)) : (k < depth w i ∧ ¬ k + 1 < depth w i) ↔ depth w i = k + 1 := by
      omega
    simp only [filter_filter, h₁, h₂] at h
    have := twice_at_level hs (k := k + 1) (by omega) hk
    specialize ih (by omega)
    unfold wet at *
    omega

private theorem sum_layers {n : ℕ} (w : Fin n → ℕ) (D : ℕ) :
    ∑ k ∈ range D, wet w k = ∑ i, min D (depth w i) := by
  simp only [wet, card_filter, sum_comm (s := range D)]
  apply sum_congr rfl
  intro i _
  rw [← card_filter]
  have : (range D).filter (fun k => k < depth w i) = range (min D (depth w i)) := by
    ext k
    simp
  rw [this, card_range]

private theorem sum_layer_bounds {n B : ℕ} {w : Fin (n + 1) → ℕ} (hs : UnitSteps w)
    {x : Fin (n + 1)} (hB : B ≤ (univ.filter (fun i => depth w i = 0)).card)
    (k : ℕ) (hk : k ≤ depth w x) :
    (∑ l ∈ range k, wet w l) + k * B + k * k ≤ k * (n + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := ih (by omega)
    have := layer_bounds hs hB k (by omega : k < depth w x)
    rw [sum_range_succ]
    nlinarith

-- A column of depth D needs a left wall, a descent and a subsequent ascent.
private theorem deep_position {n : ℕ} {w : Fin (n + 1) → ℕ} (hs : UnitSteps w) (h₀ : w 0 = 1)
    (hp : ∀ i, 1 ≤ w i) {i : Fin (n + 1)} {D : ℕ} (hi : D + 1 ≤ depth w i) :
    2 * (D + 1) ≤ i.val ∧ i.val + (D + 1) ≤ n := by
  obtain ⟨⟨a, ha, hva⟩, ⟨b, hb, hvb⟩⟩ := lt_depth.mp (show D < depth w i by omega)
  have := (steps_dist hs 0 a (Fin.zero_le _)).1
  have := (steps_dist hs a i ha.le).2
  have := (steps_dist hs i b hb.le).1
  have := hp i
  simp only [Fin.val_zero] at *
  omega

-- Pair the available positions. Each pair contains at most one isolated column.
private theorem isolated_layer {n D : ℕ} {w : Fin (n + 1) → ℕ} (hs : UnitSteps w)
    (h₀ : w 0 = 1) (hp : ∀ i, 1 ≤ w i) (hx : ∃ x, D < depth w x)
    (hsep : ∀ i j, D < depth w i → D < depth w j → j.val ≠ i.val + 1) :
    2 * wet w D + 3 * (D + 1) ≤ n + 2 := by
  obtain ⟨x, hx⟩ := hx
  have := deep_position hs h₀ hp hx
  let f (i : Fin (n + 1)) := (i.val - 2 * (D + 1)) / 2
  have h : wet w D ≤ (range ((n - 3 * (D + 1)) / 2 + 1)).card := by
    apply card_le_card_of_injOn f
    · intro i hi
      obtain ⟨hl, hr⟩ := deep_position hs h₀ hp (mem_filter.mp hi).2
      rw [mem_coe, mem_range]
      dsimp [f]
      omega
    · intro i hi j hj he
      have hi := (mem_filter.mp hi).2
      have hj := (mem_filter.mp hj).2
      have := deep_position hs h₀ hp hi
      have := deep_position hs h₀ hp hj
      have := hsep i j hi hj
      have := hsep j i hj hi
      apply Fin.ext
      dsimp [f] at he
      omega
  rw [card_range] at h
  omega

private theorem capacity_bound {n : ℕ} {w : Fin (n + 1) → ℕ}
    (hw : w ∈ restrictedSmoothWords (n + 1)) :
    wordCapacity w = 0 ∨ ∃ d : ℕ,
      wordCapacity w + 2 * d * d + 2 * d ≤ (n + 1) * d ∨
      2 * wordCapacity w + 4 * d * d + (n + 1) ≤ (2 * (n + 1) + 1) * d + 1 := by
  obtain ⟨hsmooth, hrest⟩ := mem_filter.mp hw
  obtain ⟨hp, hstart, hs⟩ := (mem_smoothWords_iff w).mp hsmooth
  have h₀ := hstart 0 rfl
  obtain ⟨x, _, hmax⟩ := univ.exists_max_image (depth w) univ_nonempty
  have hsum : ∑ k ∈ range (depth w x), wet w k = wordCapacity w := by
    rw [sum_layers]
    exact sum_congr rfl fun i hi => min_eq_right (hmax i hi)
  cases he : depth w x with
  | zero => left; simpa [he] using hsum.symm
  | succ k =>
    right
    refine ⟨k + 1, ?_⟩
    have wall {i} (hi : k < depth w i) : ∃ b, w i + k < w b := by
      obtain ⟨⟨b, _, hb⟩, _⟩ := lt_depth.mp hi
      exact ⟨b, hb⟩
    -- At depth k + 1, isolated columns occupy at most half the available interval.
    -- Adjacent columns at that depth require a taller wall, since one letter exceeds 1.
    by_cases hsep : ∀ i j, k < depth w i → k < depth w j → j.val ≠ i.val + 1
    · right
      obtain ⟨b, hb⟩ := wall (i := x) (by omega)
      have := hp x
      have hd := dry_count hs h₀ (x := x) (by omega) (H := k + 2) (b := b) (by omega)
      have hl := sum_layer_bounds hs hd k (by omega : k ≤ depth w x)
      have ht := isolated_layer hs h₀ hp ⟨x, by omega⟩ hsep
      rw [he, sum_range_succ] at hsum
      nlinarith
    · left
      push Not at hsep
      obtain ⟨i, j, hi, hj, hij⟩ := hsep
      have h := hrest i j hij
      obtain ⟨b, hb⟩ : ∃ b, k + 3 ≤ w b := by
        by_cases hh : w i = 1
        · obtain ⟨b, hb⟩ := wall hj
          have := hp j
          exact ⟨b, by omega⟩
        · obtain ⟨b, hb⟩ := wall hi
          have := hp i
          exact ⟨b, by omega⟩
      have hd := dry_count hs h₀ (x := x) (by omega) hb
      have hl := sum_layer_bounds hs hd (depth w x) le_rfl
      rw [hsum, he] at hl
      nlinarith

private def target (m p : ℕ) : ℤ :=
  8 * (m : ℤ) ^ 2 + (2 * (p : ℤ) - 3) * m +
    if p ≤ 3 then 0 else if p = 4 then 1 else 2 ^ (p - 5)

private theorem arithmetic_upper {n m p C : ℕ} (he : n = 8 * m + p) (hp : p ≤ 7)
    (h : C = 0 ∨ ∃ d : ℕ, C + 2 * d * d + 2 * d ≤ n * d ∨
      2 * C + 4 * d * d + n ≤ (2 * n + 1) * d + 1) : (C : ℤ) ≤ target m p := by
  have hn : (n : ℤ) = 8 * m + p := by exact_mod_cast he
  have hbound : 32 * (C : ℤ) ≤ 4 * (n : ℤ) ^ 2 - 12 * n + 17 ∨
      8 * (C : ℤ) ≤ ((n : ℤ) - 2) ^ 2 := by
    rcases h with rfl | ⟨d, h | h⟩
    · right; simpa using sq_nonneg ((n : ℤ) - 2)
    · right
      have hd : (C : ℤ) + 2 * d * d + 2 * d ≤ n * d := by exact_mod_cast h
      nlinarith [sq_nonneg (4 * (d : ℤ) - n + 2)]
    · left
      have hd : 2 * (C : ℤ) + 4 * d * d + n ≤ (2 * n + 1 : ℤ) * d + 1 := by exact_mod_cast h
      nlinarith [sq_nonneg (8 * (d : ℤ) - 2 * n - 1)]
  rw [hn] at hbound
  interval_cases p <;> norm_num [target] at * <;> rcases hbound with h | h <;>
    ring_nf at * <;> omega

-- Two walls of height d + 1 enclose a descent, an alternating floor and an ascent.
private def valley (d r i : ℕ) : ℕ :=
  if i ≤ d then i + 1 else if i ≤ 2 * d then 2 * d + 1 - i
  else if i ≤ 2 * d + r then 1 + (i - 2 * d) % 2 else i - (2 * d + r) + 1

private theorem valley_mem (d r : ℕ) (hd : 0 < d) :
    (fun i : Fin (3 * d + 1 + r) => valley d r i.val) ∈ restrictedSmoothWords _ := by
  apply mem_filter.mpr
  refine ⟨(mem_smoothWords_iff _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    dsimp [valley]
    split_ifs <;> omega
  · intro i hi
    simp [valley, hi]
  · intro i j hj
    dsimp [valley]
    split_ifs <;> omega
  · intro i j hj
    dsimp [valley]
    split_ifs <;> omega

private theorem valley_depth (d r : ℕ) (hd : 0 < d) (i : Fin (3 * d + 1 + r)) :
    (if i.val ≤ d then 0 else d + 1 - valley d r i.val) ≤
      depth (fun j : Fin (3 * d + 1 + r) => valley d r j.val) i := by
  let a : Fin (3 * d + 1 + r) := ⟨d, by omega⟩
  let b : Fin (3 * d + 1 + r) := ⟨3 * d + r, by omega⟩
  have ha : valley d r a.val = d + 1 := by simp [a, valley]
  have hb : valley d r b.val = d + 1 := by dsimp [b, valley]; split_ifs <;> omega
  split_ifs with h
  · omega
  by_cases he : i = b
  · simp [he, hb]
  by_contra! hl
  have hlt : depth (fun j : Fin (3 * d + 1 + r) => valley d r j.val) i <
      depth (fun j : Fin (3 * d + 1 + r) => valley d r j.val) i := by
    apply lt_depth.mpr
    refine ⟨⟨a, show d < i.val by omega, ?_⟩, ⟨b, ?_, ?_⟩⟩
    · omega
    · change i.val < 3 * d + r
      have hne : i.val ≠ 3 * d + r := fun h => he (Fin.ext h)
      omega
    · omega
  omega

private theorem valley_area (d r : ℕ) (hd : 0 < d) :
    d * d + d * r ≤
      wordCapacity (fun i : Fin (3 * d + 1 + r) => valley d r i.val) + (r + 1) / 2 := by
  let f (i : ℕ) := if i ≤ d then 0 else d + 1 - valley d r i
  have h : (∑ i ∈ range (3 * d + 1 + r), f i) ≤
      wordCapacity (fun i : Fin (3 * d + 1 + r) => valley d r i.val) := by
    rw [← Fin.sum_univ_eq_sum_range f]
    exact sum_le_sum fun i _ => valley_depth d r hd i
  conv_lhs at h =>
    rw [show 3 * d + 1 + r = (d + 1 + d + r) + d by omega, sum_range_add,
      sum_range_add f (d + 1 + d) r, sum_range_add f (d + 1) d]
  have hprefix : ∑ i ∈ range (d + 1), f i = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [f, show i ≤ d by simpa using hi]
  have descent (i) (hi : i ∈ range d) : f (d + 1 + i) = i + 1 := by
    rw [mem_range] at hi
    dsimp [f, valley]
    split_ifs <;> omega
  have floor_sum (s) (hs : s ≤ r) :
      (∑ i ∈ range s, f (d + 1 + d + i)) + (s + 1) / 2 = d * s := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [sum_range_succ, Nat.mul_succ]
      have he : f (d + 1 + d + s) = d - (s + 1) % 2 := by
        dsimp [f, valley]
        split_ifs <;> omega
      rw [he]
      specialize ih (by omega)
      omega
  have ramps : (∑ i ∈ range d, f (d + 1 + i)) + (∑ i ∈ range d, f (d + 1 + d + r + i)) = d * d := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _i ∈ range d, d := by
        apply sum_congr rfl
        intro i hi
        rw [descent i hi]
        rw [mem_range] at hi
        dsimp [f, valley]
        split_ifs <;> omega
      _ = _ := by simp
  rw [hprefix] at h
  have := floor_sum r le_rfl
  omega

private theorem degree_of_member {n : ℕ} {S : Finset (Fin n → ℕ)} {w : Fin n → ℕ}
    (hw : w ∈ S) : wordCapacity w ≤ (capacityDist S).natDegree := by
  apply le_natDegree_of_ne_zero
  rw [capacityDist, finsetSum_coeff]
  simp_rw [coeff_X_pow]
  apply ne_of_gt
  apply Finset.sum_pos'
  · intro i _
    split <;> decide
  · exact ⟨w, hw, by simp⟩

private theorem attained_bound (d r : ℕ) (hd : 0 < d) :
    d * d + d * r ≤
      (capacityDist (restrictedSmoothWords (3 * d + 1 + r))).natDegree + (r + 1) / 2 := by
  have := degree_of_member (valley_mem d r hd)
  have := valley_area d r hd
  omega

private theorem degree_lower (m p : ℕ) (hp : p ≤ 7) :
    target m p ≤ ((capacityDist (restrictedSmoothWords (8 * m + p))).natDegree : ℤ) := by
  by_cases hsmall : 8 * m + p < 4
  · have hm : m = 0 := by omega
    simp [target, hm, show p ≤ 3 by omega]
  have attain (d : ℕ) (hd : 0 < d) (hfit : 3 * d + 1 ≤ 8 * m + p)
      (harea : 2 * target m p + ((8 * m + p : ℤ) - 3 * d - 1) ≤
        2 * ((d : ℤ) * d + d * ((8 * m + p : ℤ) - 3 * d - 1))) :
      target m p ≤ ((capacityDist (restrictedSmoothWords (8 * m + p))).natDegree : ℤ) := by
    let r := 8 * m + p - (3 * d + 1)
    have hr : 3 * d + 1 + r = 8 * m + p := by dsimp [r]; omega
    have hr' : (r : ℤ) = (8 * m + p : ℤ) - 3 * d - 1 := by omega
    have h := attained_bound d r hd
    rw [hr] at h
    rw [← hr'] at harea
    have h' : (d : ℤ) * d + d * r ≤
        (capacityDist (restrictedSmoothWords (8 * m + p))).natDegree + (((r + 1) / 2 : ℕ) : ℤ) := by
      exact_mod_cast h
    omega
  -- Choose a wall of height d + 1 according to the length modulo eight.
  let d := 2 * m + (if p ≤ 1 then 0 else if p ≤ 6 then 1 else 2)
  apply attain d
  · dsimp [d]
    split_ifs <;> omega
  · dsimp [d]
    split_ifs <;> omega
  · dsimp only [d]
    interval_cases p <;> norm_num [target] <;> ring_nf <;> omega

private theorem degree_upper (m p : ℕ) (hp : p ≤ 7) (hn : 1 ≤ 8 * m + p) :
    ((capacityDist (restrictedSmoothWords (8 * m + p))).natDegree : ℤ) ≤ target m p := by
  have hnonneg : 0 ≤ target m p := arithmetic_upper (C := 0) rfl hp (Or.inl rfl)
  suffices h : (capacityDist (restrictedSmoothWords (8 * m + p))).natDegree ≤ (target m p).toNat by
    omega
  generalize he : 8 * m + p = n
  cases n with
  | zero => omega
  | succ n =>
    apply natDegree_sum_le_of_forall_le
    intro w hw
    rw [natDegree_X_pow]
    have := arithmetic_upper he.symm hp (capacity_bound hw)
    omega

end restrictedSmoothWords_capacity_natDegree

open restrictedSmoothWords_capacity_natDegree in
/-- **Maximum capacity of restricted smooth words.** Let $m \ge 0$ and $0 \le p \le 7$ with
$n = 8m + p \ge 1$. The degree of the capacity distribution of the restricted smooth words of
length $n$, that is, the largest capacity of a restricted smooth word of length $n$, equals
$8m^2 + (2p - 3)m + e_p$, where $e_p = 0$ for $p \le 3$, $e_4 = 1$ and $e_p = 2^{p-5}$ for
$5 \le p \le 7$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 9 (`integers-2025-A5-thm-9`). -/
public theorem restrictedSmoothWords_capacity_natDegree (m p : ℕ) (hp : p ≤ 7)
    (hn : 1 ≤ 8 * m + p) :
    ((capacityDist (restrictedSmoothWords (8 * m + p))).natDegree : ℤ) =
      8 * (m : ℤ) ^ 2 + (2 * (p : ℤ) - 3) * m +
        if p ≤ 3 then 0 else if p = 4 then 1 else 2 ^ (p - 5) := by
  exact le_antisymm (degree_upper m p hp hn) (degree_lower m p hp)

end MetaMathlibExt
