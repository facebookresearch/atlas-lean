/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Short monochromatic arithmetic progressions

We prove Erdős Problem 984 by bounding monochromatic progressions starting at `a ≥ 1`
by an exponential in `√(log a)`. In each block `[B, 16B)`, where `B = 16^t`, we choose
the colours on `[B, 4B)` by finite counting. They are constant on cells of width
`2w`, with `w = 2^(⌊√t⌋)`. The interval `[4B, 16B)` uses a fourfold enlargement
with the colours exchanged.

For large differences `d`, take a block with `4d ≤ B ≤ 64d`. A short initial segment
of the progression contains points `a + z` and `a + 4z` in the two halves. If `4a ≤ w`,
we can choose `z` so that `z + a` and `z + ⌊a/4⌋` lie in the same cell, forcing opposite
colours. This uses the fact that doubling a cell boundary takes it to a cell centre.

For the remaining differences, counting ensures that a monochromatic progression with
spacing at least `8w` must leave its interval within `12(t + 1)` terms. Taking a regularly
spaced subsequence handles smaller differences. The resulting estimate depends on the
number of intervals visited and the subsampling step, both controlled in terms of `a`.

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/ShortMonochromaticProgressionsErdosProblem984Wanted.lean`:

Source: T. F. Bloom, Erdős Problems, Problem #984, https://www.erdosproblems.com/984 (status
PROVED). UnsolvedMath record UM-30007110 (`EP-984`), dataset ulamai/UnsolvedMath v1.8.0.

`ℕ` is the positive integers: progressions start at `a ≥ 1` (for `a = 0` the one-term progression
`{0}` would violate `1 ≤ C · 0^ε`) and have difference `d ≥ 1` (`d = 0` would allow arbitrarily long
constant progressions). A colouring is a function `ℕ → Fin 2` (its value at `0` is irrelevant), and
`k ≪_ε a^ε` is a constant `C_ε` with `k ≤ C_ε a^ε`. formal-conjectures has no statement of this
problem.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ShortMonochromaticProgressionsErdosProblem984Wanted

/-- **Statement of Erdős Problem 984 on short monochromatic progressions.** The proposition that
there is a colouring of the positive integers with two colours such that for every real
$\varepsilon > 0$ there is a real constant $C_\varepsilon$ with the following property: whenever
$a \ge 1$, $d \ge 1$ and $k \ge 0$ are integers and $a, a + d, \dots, a + (k - 1)d$ all have the
same colour, $k \le C_\varepsilon a^\varepsilon$. -/
def twoColouringShortProgressions : Prop :=
  ∃ c : ℕ → Fin 2, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a d k : ℕ, 1 ≤ a → 1 ≤ d →
    (∀ i < k, c (a + i * d) = c a) → (k : ℝ) ≤ C * (a : ℝ) ^ ε

open Finset

/-- The colour of each cell is free. For a fixed set of cells, at most twice the number
of assignments on its complement make it monochromatic. -/
private lemma split_sets (U : Finset ℕ) {ι : Type*} (I : Finset ι) (E : ι → Finset ℕ)
    (s : ℕ) (hE : ∀ i ∈ I, E i ⊆ U) (hsize : 2 * I.card < 2 ^ s) :
    ∃ R : Finset ℕ, ∀ i ∈ I, s ≤ (E i).card → ¬ (E i ⊆ R ∨ Disjoint (E i) R) := by
  classical
  by_cases hs : s ≤ U.card
  · let bad (i : ι) := if s ≤ (E i).card then
        (U \ E i).powerset ∪ ((U \ E i).powerset.image (· ∪ E i)) else ∅
    have hcard (i) (hi : i ∈ I) : (bad i).card ≤ 2 * 2 ^ (U.card - s) := by
      dsimp [bad]
      split_ifs with h
      · apply (card_union_le ..).trans
        have hc := card_image_le (s := (U \ E i).powerset) (f := (· ∪ E i))
        rw [card_powerset, card_sdiff_of_subset (hE i hi)] at hc ⊢
        have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le_sub_left h U.card)
        omega
      · simp
    have hlt : (I.biUnion bad).card < U.powerset.card := by
      apply (card_biUnion_le_card_mul I bad _ hcard).trans_lt
      rw [card_powerset, show I.card * (2 * 2 ^ (U.card - s)) =
        (2 * I.card) * 2 ^ (U.card - s) by ring]
      simpa [← pow_add, Nat.add_sub_of_le hs] using
        Nat.mul_lt_mul_of_pos_right hsize (by positivity : 0 < 2 ^ (U.card - s))
    obtain ⟨R, hR, hgood⟩ := exists_mem_notMem_of_card_lt_card hlt
    refine ⟨R, fun i hi he h ↦ hgood (mem_biUnion.mpr ⟨i, hi, ?_⟩)⟩
    have hRU := mem_powerset.mp hR
    simp only [bad, ite_eq_left he, mem_union, mem_powerset, mem_image]
    rcases h with h | h
    · right
      exact ⟨R \ E i, sdiff_subset_sdiff_left _ hRU, sdiff_union_of_subset h⟩
    · exact Or.inl (subset_sdiff.mpr ⟨hRU, h.symm⟩)
  · exact ⟨∅, fun i hi he ↦ (hs (he.trans (card_le_card (hE i hi)))).elim⟩

private def width (t : ℕ) := 2 ^ t.sqrt
private def base (t : ℕ) := 16 ^ t
private def span (t : ℕ) := 12 * (t + 1)
private def cell (w x : ℕ) := (x + w) / (2 * w)

-- The two halves of a block use the same cells, at scales 1 and 4.
private def label (t b x : ℕ) := cell (width t) (x / (if b = 0 then 1 else 4))

private lemma label_lt {t b x N : ℕ} (hx : x < N) (hN : 1 < N) : label t b x < N := by
  have hw : 0 < width t := by dsimp [width]; positivity
  have hdiv := Nat.div_le_self x (if b = 0 then 1 else 4)
  unfold label cell
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  nlinarith

private lemma label_strict {t b x y : ℕ} (hxy : x + 8 * width t ≤ y) :
    label t b x < label t b y := by
  have hw : 0 < width t := by dsimp [width]; positivity
  have hd : x / (if b = 0 then 1 else 4) + 2 * width t ≤ y / (if b = 0 then 1 else 4) := by
    split <;> omega
  unfold label cell
  apply Nat.lt_of_succ_le
  rw [Nat.succ_eq_add_one]
  rw [← Nat.add_div_right _ (by omega : 0 < 2 * width t)]
  exact Nat.div_le_div_right (by omega)

private lemma block_choice (t : ℕ) :
    ∃ R : Finset ℕ, ∀ b < 2, ∀ a d : ℕ, 8 * width t ≤ d →
      a + (span t - 1) * d < base (t + 1) →
      ¬ (∀ i < span t, label t b (a + i * d) ∈ R) ∧
      ¬ (∀ i < span t, label t b (a + i * d) ∉ R) := by
  classical
  let N := base (t + 1)
  let I := range 2 ×ˢ (range N ×ˢ range N)
  let E (p : ℕ × ℕ × ℕ) := ((range (span t)).image
    (fun i ↦ label t p.1 (p.2.1 + i * p.2.2))) ∩ range N
  have hN : 1 < N := by dsimp [N, base]; exact one_lt_pow₀ (by decide) (by omega)
  have hc : 2 * I.card < 2 ^ span t := by
    simp only [I, card_product, card_range, N, base, span]
    rw [show 16 = 2 ^ 4 by decide, ← pow_mul]
    calc
      2 * (2 * (2 ^ (4 * (t + 1)) * 2 ^ (4 * (t + 1)))) =
          2 ^ (2 + (4 * (t + 1) + 4 * (t + 1))) := by simp [pow_add]; ring
      _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨R, hR⟩ := split_sets (range N) I E (span t) (fun _ _ ↦ inter_subset_right) hc
  refine ⟨R, fun b hb a d hd hlast ↦ ?_⟩
  have hs : 2 ≤ span t := by unfold span; omega
  have hlt (i) (hi : i < span t) : a + i * d < N :=
    lt_of_le_of_lt (by gcongr; omega) hlast
  have had : (b, a, d) ∈ I := by
    have := hlt 0 (by omega)
    have := hlt 1 (by omega)
    simpa [I] using And.intro hb (And.intro (by omega : a < N) (by omega : d < N))
  let f := fun i ↦ label t b (a + i * d)
  have hi : StrictMono f := strictMono_nat_of_lt_succ fun i ↦
    label_strict (by simpa [Nat.succ_mul, Nat.add_assoc] using
      Nat.add_le_add_left hd (a + i * d))
  have hE : E (b, a, d) = (range (span t)).image f := by
    apply inter_eq_left.mpr
    simpa [image_subset_iff, f] using fun i (h : i < span t) ↦ label_lt (b := b) (hlt i h) hN
  have hh := hR _ had (by rw [hE, card_image_of_injective _ hi.injective, card_range])
  rw [hE] at hh
  simpa [image_subset_iff, disjoint_left, f, not_or, forall_mem_image] using hh

private noncomputable def reds (t : ℕ) := (block_choice t).choose

private noncomputable def paint (j x : ℕ) : Bool :=
  xor (decide (label (j / 2) (j % 2) x ∈ reds (j / 2))) (decide (j % 2 = 1))

private noncomputable def colour (x : ℕ) := paint (Nat.log 4 x) x

private lemma base_eq (t : ℕ) : base t = 4 ^ (2 * t) := by
  rw [base, pow_mul]; rfl

private lemma colour_low {t x : ℕ} (hl : base t ≤ x) (hu : x < 4 * base t) :
    colour x = decide (cell (width t) x ∈ reds t) := by
  have h : Nat.log 4 x = 2 * t := Nat.log_eq_of_pow_le_of_lt_pow
    (by simpa [← base_eq] using hl) (by rw [pow_succ, ← base_eq]; omega)
  simp [colour, h, paint, label]

private lemma colour_high {t x : ℕ} (hl : 4 * base t ≤ x) (hu : x < 16 * base t) :
    colour x = !(decide (cell (width t) (x / 4) ∈ reds t)) := by
  have h : Nat.log 4 x = 2 * t + 1 := Nat.log_eq_of_pow_le_of_lt_pow
    (by rw [pow_succ, ← base_eq]; omega)
    (by rw [pow_succ, pow_succ, ← base_eq]; omega)
  simp [colour, h, paint, label, Nat.add_div, Nat.add_mod]

private lemma cell_period {w : ℕ} (hw : 0 < w) (m x : ℕ) :
    cell w (m * (2 * w) + x) = m + cell w x := by
  simp only [cell, Nat.add_assoc]
  rw [Nat.add_comm (m * _), Nat.add_mul_div_right _ _ (by omega : 0 < 2 * w), Nat.add_comm]

-- The boundaries of the cells lie at odd multiples of w. Doubling a point near a
-- boundary takes it near an even multiple, safely inside a cell.
private lemma stable {w a : ℕ} (hw : 0 < w) (ha : 4 * a ≤ w) (n : ℕ) :
    ∃ z ∈ ({n, 2 * n} : Finset ℕ), ∀ p ≤ a, cell w (z + p) = cell w z := by
  let m := n / (2 * w)
  let r := n % (2 * w)
  have hr : r < 2 * w := Nat.mod_lt _ (by omega)
  have hn : n = m * (2 * w) + r := (Nat.div_add_mod' ..).symm
  by_cases h : r + a < w
  · refine ⟨n, by simp, fun p hp ↦ ?_⟩
    conv_lhs => rw [hn, Nat.add_assoc, cell_period hw]
    conv_rhs => rw [hn, cell_period hw]
    simp [cell, Nat.div_eq_of_lt (by omega : r + p + w < 2 * w),
      Nat.div_eq_of_lt (by omega : r + w < 2 * w)]
  by_cases h' : w ≤ r
  · refine ⟨n, by simp, fun p hp ↦ ?_⟩
    conv_lhs => rw [hn, Nat.add_assoc, cell_period hw]
    conv_rhs => rw [hn, cell_period hw]
    have one (p') (hp' : p' ≤ a) : cell w (r + p') = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [one _ hp, ← Nat.add_zero r, one 0 (by omega)]
  · refine ⟨2 * n, by simp, fun p hp ↦ ?_⟩
    have hn' : 2 * n = (2 * m) * (2 * w) + 2 * r := by rw [hn]; ring
    conv_lhs => rw [hn', Nat.add_assoc, cell_period hw]
    conv_rhs => rw [hn', cell_period hw]
    have one (p') (hp' : p' ≤ a) : cell w (2 * r + p') = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [one _ hp, ← Nat.add_zero (2 * r), one 0 (by omega)]

private lemma far_bound {a d k t : ℕ} (hd : 1 ≤ d) (hlo : 4 * d ≤ base t)
    (hhi : base t ≤ 64 * d) (ha : 4 * a ≤ width t) (had : a ≤ d)
    (hm : ∀ i < k, colour (a + i * d) = colour a) : k ≤ 520 := by
  by_contra! hk
  -- The first multiple of d in the block and its double are both in the lower interval.
  let i := (base t - 1) / d + 1
  have hbase : 0 < base t := by unfold base; positivity
  have hi : base t ≤ i * d := by
    have := Nat.mod_lt (base t - 1) (by omega : 0 < d)
    have := Nat.div_add_mod' (base t - 1) d
    dsimp [i]; rw [Nat.add_mul]; omega
  have hu : i * d < base t + d := by
    dsimp [i]; rw [Nat.add_mul]; have := Nat.div_mul_le_self (base t - 1) d; omega
  have hile : i ≤ 65 := by nlinarith
  obtain ⟨z, hz, hs⟩ := stable (by unfold width; positivity) ha (i * d)
  obtain ⟨j, hj, hzj⟩ : ∃ j, (j = i ∨ j = 2 * i) ∧ z = j * d := by
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with h | h
    · exact ⟨i, Or.inl rfl, h⟩
    · exact ⟨2 * i, Or.inr rfl, by rw [h]; ring⟩
  have hlow : base t ≤ z := by rcases hj with rfl | rfl <;> nlinarith
  have hupper : a + z < 4 * base t := by rcases hj with rfl | rfl <;> nlinarith
  have hjle : j ≤ 130 := by omega
  have hc := (hm j (by omega)).trans (hm (4 * j) (by omega)).symm
  rw [← hzj, show 4 * j * d = 4 * z by rw [hzj]; ring,
    colour_low (by omega : base t ≤ a + z) hupper,
    colour_high (by omega : 4 * base t ≤ a + 4 * z) (by omega : a + 4 * z < 16 * base t),
    show (a + 4 * z) / 4 = z + a / 4 by omega, Nat.add_comm a z, hs a le_rfl,
    hs (a / 4) (by omega)] at hc
  simp at hc

-- A long run in one geometric interval would give a monochromatic set of distinct cells.
private lemma leaves_interval {j x D : ℕ} (hd : 8 * width (j / 2) ≤ D)
    (hstart : Nat.log 4 x = j)
    (hmono : ∀ i < span (j / 2), colour (x + i * D) = colour x) :
    j < Nat.log 4 (x + (span (j / 2) - 1) * D) := by
  let last := x + (span (j / 2) - 1) * D
  by_contra! h
  have hlog (i) (hi : i < span (j / 2)) : Nat.log 4 (x + i * D) = j := by
    apply le_antisymm ((Nat.log_mono_right (by gcongr; omega)).trans h)
    exact hstart ▸ Nat.log_mono_right (Nat.le_add_right ..)
  have hlast : last < base (j / 2 + 1) := by
    rw [base_eq]
    exact Nat.lt_pow_of_log_lt (by decide) (by dsimp [last]; omega)
  have hchoice := (block_choice (j / 2)).choose_spec (j % 2) (by omega) x D hd hlast
  have hc (i) (hi : i < span (j / 2)) :
      decide (label (j / 2) (j % 2) (x + i * D) ∈ reds (j / 2)) =
        decide (label (j / 2) (j % 2) x ∈ reds (j / 2)) := by
    have hh := hmono i hi
    simpa [colour, hlog i hi, hstart, paint] using hh
  by_cases hm : label (j / 2) (j % 2) x ∈ reds (j / 2)
  · apply hchoice.1
    intro i hi
    change label (j / 2) (j % 2) (x + i * D) ∈ reds (j / 2)
    simpa [hm] using hc i hi
  · apply hchoice.2
    intro i hi
    change label (j / 2) (j % 2) (x + i * D) ∉ reds (j / 2)
    simpa [hm] using hc i hi

private def runs (T : ℕ) := (4 * T + 1) * span (2 * T)
private def stride (T d : ℕ) := if 8 * width (2 * T) ≤ d then 1 else 8 * width (2 * T)

private lemma width_mono : Monotone width :=
  fun _ _ h ↦ Nat.pow_le_pow_right (by decide) (Nat.sqrt_le_sqrt h)

private lemma horizon {T d : ℕ} (hT : 16 ≤ T) :
    runs T * stride T d + 1 ≤ base T := by
  have hw : width (2 * T) ≤ 2 ^ T := by
    unfold width
    apply Nat.pow_le_pow_right (by decide)
    have := Nat.sqrt_le (2 * T)
    by_contra! h
    nlinarith
  have ht := T.lt_two_pow_self
  have hq : stride T d ≤ 8 * 2 ^ T := by unfold stride; split <;> omega
  have hbig : 2048 ≤ 2 ^ T := Nat.le_trans (by decide : 2048 ≤ 2 ^ 16)
    (Nat.pow_le_pow_right (by decide) hT)
  have hmult : runs T * stride T d ≤ (4 * 2 ^ T) * (24 * 2 ^ T) * (8 * 2 ^ T) := by
    unfold runs span
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hq
  rw [base, show 16 = 2 ^ 4 by decide, ← pow_mul, Nat.mul_comm 4 T, pow_mul]
  nlinarith [Nat.pow_le_pow_left hbig 3, Nat.mul_le_mul_right ((2 ^ T) ^ 3) hbig]

private lemma run_bound {a d k T : ℕ} (ha : 0 < a) (hd : 0 < d) (hT : 16 ≤ T)
    (had : max a d < base T) (hm : ∀ i < k, colour (a + i * d) = colour a) :
    k ≤ runs T * stride T d := by
  by_contra! hk
  -- Sample every q-th term, then group the samples into runs of length S.
  let q := stride T d
  let S := span (2 * T)
  let x (j : ℕ) := a + (j * S * q) * d
  have hq : 8 * width (2 * T) ≤ q * d := by
    dsimp [q, stride]; split
    · simpa
    · exact Nat.le_mul_of_pos_right _ hd
  have hlast : x (4 * T + 1) < 4 ^ (4 * T) := by
    have h := horizon (d := d) hT
    have heq : base T * base T = 4 ^ (4 * T) := by rw [base_eq, ← pow_add]; congr 1; omega
    rw [← heq]
    calc
      x (4 * T + 1) ≤ (runs T * q + 1) * max a d := by
        change a + runs T * q * d ≤ _
        rw [Nat.add_one_mul, Nat.add_comm a]; gcongr <;> omega
      _ ≤ base T * max a d := Nat.mul_le_mul_right _ h
      _ < _ := Nat.mul_lt_mul_of_pos_left had (by unfold base; positivity)
  have hm' (j) (hj : j ≤ 4 * T + 1) : Nat.log 4 (x j) < 4 * T := by
    apply Nat.log_lt_of_lt_pow (by dsimp [x]; omega)
    exact lt_of_le_of_lt (by dsimp [x]; gcongr) hlast
  -- Each run increases the base-four interval index, which is less than 4T throughout.
  have hl (j) (hj : j < 4 * T + 1) : Nat.log 4 (x j) < Nat.log 4 (x (j + 1)) := by
    let b := Nat.log 4 (x j)
    have hb : b / 2 ≤ 2 * T := by have := hm' j (by omega); dsimp [b]; omega
    have hs : span (b / 2) ≤ S := by dsimp [span, S]; omega
    have hidx (i) (hi : i < span (b / 2)) : (j * S + i) * q < k := by
      apply lt_of_le_of_lt _ hk
      apply Nat.mul_le_mul_right
      calc
        j * S + i ≤ (j + 1) * S := by rw [Nat.add_mul]; omega
        _ ≤ (4 * T + 1) * S := by gcongr; omega
    have hh (i) (hi : i < span (b / 2)) : colour (x j + i * (q * d)) = colour (x j) := by
      rw [show x j + i * (q * d) = a + ((j * S + i) * q) * d by dsimp [x]; ring,
        hm _ (hidx _ hi)]
      exact (hm _ (by simpa using hidx 0 (by dsimp [span]; omega))).symm
    apply (leaves_interval ((Nat.mul_le_mul_left 8 (width_mono hb)).trans hq)
      (j := b) rfl hh).trans_le
    apply Nat.log_mono_right
    have heq : x (j + 1) = x j + S * (q * d) := by dsimp [x]; ring
    rw [heq]; gcongr; omega
  have h (j) (hj : j ≤ 4 * T + 1) : j ≤ Nat.log 4 (x j) := by
    induction j with
    | zero => omega
    | succ j ih => have := ih (by omega); have := hl j (by omega); omega
  have := h (4 * T + 1) le_rfl
  have := hm' (4 * T + 1) le_rfl
  omega

private lemma runs_le {T m : ℕ} (hm : 10 ≤ m) (ht : T ≤ 2 ^ (5 * m)) :
    runs T ≤ 2 ^ (11 * m) := by
  let B := 2 ^ (5 * m)
  have hB : 1 ≤ B := Nat.two_pow_pos _
  have hm' : 256 ≤ 2 ^ m := (by decide : 256 ≤ 2 ^ 10).trans
    (Nat.pow_le_pow_right (by decide) hm)
  have ht' : T ≤ B := ht
  calc
    runs T ≤ (5 * B) * (36 * B) :=
      Nat.mul_le_mul (by omega) (by dsimp [span]; omega)
    _ ≤ B * B * 2 ^ m := by nlinarith [Nat.mul_le_mul_left (B * B) hm']
    _ = 2 ^ (11 * m) := by dsimp [B]; rw [← pow_add, ← pow_add]; congr 1; omega

private lemma stride_le {T d m : ℕ} (hm : 10 ≤ m) (ht : T ≤ m * m + 16) :
    stride T d ≤ 2 ^ (3 * m) := by
  have hs := Nat.sqrt_le (2 * T)
  have h : (2 * T).sqrt ≤ 2 * m := by by_contra! hh; nlinarith
  have hw : width (2 * T) ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by decide) h
  have hq : stride T d ≤ 8 * 2 ^ (2 * m) := by
    have := Nat.two_pow_pos (2 * m)
    unfold stride; split <;> omega
  apply hq.trans
  rw [show 8 = 2 ^ 3 by decide, ← pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

private lemma length_bound {a d k m : ℕ} (ha : 0 < a) (hd : 0 < d) (hm : 10 ≤ m)
    (ham : a < 2 ^ (m * m)) (hmono : ∀ i < k, colour (a + i * d) = colour a) :
    k ≤ 2 ^ (14 * m) := by
  let T := Nat.log 16 (max a d) + 16
  have hT : 16 ≤ T := by dsimp [T]; omega
  have hmax : max a d < base T := by
    apply Nat.lt_pow_of_log_lt (by decide)
    dsimp [T]; omega
  have hk := run_bound ha hd hT hmax hmono
  have hprod (ht : T ≤ 2 ^ (5 * m)) (hq : stride T d ≤ 2 ^ (3 * m)) :
      k ≤ 2 ^ (14 * m) := by
    calc
      k ≤ _ := hk
      _ ≤ _ := Nat.mul_le_mul (runs_le hm ht) hq
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hmp : m + 1 ≤ 2 ^ m := m.lt_two_pow_self
  have hms : m * m + 16 ≤ 2 ^ (2 * m) := by
    rw [two_mul, pow_add]
    nlinarith [Nat.mul_le_mul hmp hmp]
  by_cases had : d ≤ a
  · have ht : T ≤ m * m + 16 := by
      have hlog := Nat.log_lt_of_lt_pow (b := 2) (by omega : a ≠ 0) ham
      have := Nat.log_anti_left (n := a) (by decide : 1 < 2) (by decide : 2 ≤ 16)
      dsimp [T]; rw [max_eq_left had]; omega
    exact hprod (ht.trans (hms.trans (Nat.pow_le_pow_right (by decide) (by omega))))
      (stride_le hm ht)
  rw [max_eq_right (by omega : a ≤ d)] at hmax
  let u := Nat.log 16 (4 * d) + 1
  have hu : 4 * d < base u := Nat.lt_pow_succ_log_self (by decide) _
  have hu' : base u ≤ 64 * d := by
    have := Nat.pow_log_le_self 16 (by omega : 4 * d ≠ 0)
    dsimp [base, u]; rw [pow_succ]; omega
  by_cases hfar : 4 * a ≤ width u
  · exact (far_bound hd hu.le hu' hfar (by omega) hmono).trans
      ((by decide : 520 ≤ 2 ^ 10).trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hut : T ≤ u + 16 := by
    have := Nat.log_mono_right (b := 16) (show d ≤ 4 * d by omega)
    dsimp [T, u]; rw [max_eq_right (by omega : a ≤ d)]; omega
  have hs : u.sqrt < m * m + 2 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    calc
      width u < 4 * a := by omega
      _ < 4 * 2 ^ (m * m) := by omega
      _ = 2 ^ (m * m + 2) := by rw [pow_add]; ring
  have hu2 := Nat.lt_succ_sqrt u
  rw [Nat.succ_eq_add_one] at hu2
  have hml : u.sqrt + 1 ≤ 2 ^ (2 * m) := by omega
  have ht : T ≤ 2 ^ (5 * m) := by
    have h1 := Nat.mul_le_mul hml hml
    have h2 : 2 ^ (2 * m) * 2 ^ (2 * m) = 2 ^ (4 * m) := by
      rw [← pow_add]; congr 1; omega
    rw [h2] at h1
    have h3 : 16 ≤ 2 ^ (4 * m) := (by decide : 16 ≤ 2 ^ 4).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    have h4 : 2 ^ (4 * m + 1) ≤ 2 ^ (5 * m) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at h4
    omega
  apply hprod ht
  by_cases hsmall : T ≤ m * m + 16
  · exact stride_le hm hsmall
  have h32 : 32 ≤ T := by nlinarith
  have hsT := Nat.sqrt_le (2 * T)
  have hr : (2 * T).sqrt ≤ T := by by_contra! hh; nlinarith
  have hTlog : T = Nat.log 16 d + 16 := by dsimp [T]; rw [max_eq_right (by omega : a ≤ d)]
  have hstep : 8 * width (2 * T) ≤ d := by
    calc
      8 * width (2 * T) = 2 ^ (3 + (2 * T).sqrt) := by rw [pow_add]; rfl
      _ ≤ 2 ^ (4 * Nat.log 16 d) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 16 ^ Nat.log 16 d := by rw [pow_mul]; rfl
      _ ≤ d := Nat.pow_log_le_self _ (by omega)
  rw [stride, ite_eq_left hstep]
  exact Nat.two_pow_pos _

private lemma exponent_bound {r l ε : ℝ} (hr : r * r ≤ l) (hε : 0 < ε) :
    14 * (r + 10) ≤ (140 + 49 / ε) + l * ε := by
  apply (mul_le_mul_iff_of_pos_right hε).mp
  rw [add_mul, add_mul, div_mul_cancel₀ _ hε.ne']
  nlinarith [sq_nonneg (ε * r - 7), mul_le_mul_of_nonneg_right hr (sq_nonneg ε)]

/--
**Erdős Problem 984: a two-colouring with short monochromatic progressions exists.** There is a
colouring of the positive integers with two colours such that for every real $\varepsilon > 0$
there is a real constant $C_\varepsilon$ with the following property: whenever $a \ge 1$,
$d \ge 1$ and $k \ge 0$ are integers and $a, a + d, \dots, a + (k - 1)d$ all have the same
colour, $k \le C_\varepsilon a^\varepsilon$.

Source: T. F. Bloom, Erdős Problems,
Problem #984, https://www.erdosproblems.com/984 (status PROVED); resolution: Z. Hunter, proof in the
erdosproblems.com/984 comments, using Green's red-blue colourings for off-diagonal van der Waerden
numbers, erdosproblems.com/984: 'Zach Hunter has proved the answer is yes (see the comments)'; the
comment colours each block I_t = [100^t, 100^{t+1}) with no red 3-term progression and no blue
progression of length k_t = |I_t|^{o(1)} for odd t (colours swapped for even t),
https://www.erdosproblems.com/forum/thread/984.
-/
public theorem twoColouringShortProgressions_holds : twoColouringShortProgressions := by
  refine ⟨fun x ↦ if colour x then 1 else 0, fun ε hε ↦ ?_⟩
  refine ⟨(2 : ℝ) ^ (140 + 49 / ε), fun a d k ha hd hmono ↦ ?_⟩
  let L := Nat.log 2 a
  have hL := Nat.sqrt_le L
  have hupper := Nat.lt_pow_succ_log_self (b := 2) (by decide) a
  have hlen := length_bound (m := L.sqrt + 10) ha hd (by omega)
    (hupper.trans_le (Nat.pow_le_pow_right (by decide) (by
      have := Nat.lt_succ_sqrt L
      change L + 1 ≤ _
      nlinarith))) (fun i hi ↦ by
        have h := hmono i hi
        cases h₁ : colour (a + i * d) <;> cases h₂ : colour a <;> simp_all)
  have hreal : (L.sqrt : ℝ) * L.sqrt ≤ L := by exact_mod_cast hL
  have hexp := exponent_bound hreal hε
  calc
    (k : ℝ) ≤ 2 ^ (14 * (L.sqrt + 10) : ℕ) := by exact_mod_cast hlen
    _ = (2 : ℝ) ^ (14 * ((L.sqrt : ℝ) + 10)) := by
      rw [← Real.rpow_natCast]; simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ _ := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast_mul (by norm_num)]
      gcongr
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : a ≠ 0)

end MathlibExt.Combinatorics.ShortMonochromaticProgressionsErdosProblem984Wanted
