/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Real

/-!
# Erdős Problem 992: discrepancy of fractional parts of `α * xₙ`

Source record `EP-992`.

The theorem `conjecture_refuted` gives a negative answer by concatenating arithmetic progressions.
For almost every multiplier, infinitely many of these blocks fall entirely in the lower half of the
unit interval. The count on such a block forces a large discrepancy at one of its two endpoints.

Erdős Problem 992 asks: for integers `x₁ < x₂ < ⋯`, is it true that for
almost all `α ∈ [0, 1]` the discrepancy
`D(N) = max over intervals I of |count - |I| * N|` satisfies
`D(N) ≪ N ^ (1/2) * (log N) ^ o(1)`?

Gaps vs the source record:
- Only the first (weaker) bound is formalized; the stronger
  `(log log N)`-variant mentioned in the record is omitted.
- The record takes the maximum over all intervals; here the discrepancy is
  the supremum over closed intervals with rational endpoints in `[0, 1]`
  (so that counting is well-defined with decidable membership), which
  approximates the full-interval supremum.
- Indexing is 0-based (`x : ℕ → ℤ` with `StrictMono x`) rather than 1-based.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosSequenceDiscrepancyWanted

open MeasureTheory Filter

open Classical in
/-- **Counting fractional parts in a rational interval.** For a sequence of integers
$(x_n)_{n \ge 0}$, a real number $\alpha$, a natural number $N$ and rationals $p, q$, the number of
indices $n < N$ for which the fractional part $\{\alpha x_n\}$ lies in the closed interval
$[p, q]$. -/
noncomputable def CountQ (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (p q : ℚ) : ℕ :=
  ((Finset.range N).filter fun n =>
    Int.fract (α * (x n : ℝ)) ∈ Set.Icc (p : ℝ) (q : ℝ)).card

/-- **Discrepancy of fractional parts over rational intervals.** For a sequence of integers
$(x_n)_{n \ge 0}$, a real number $\alpha$ and a natural number $N$, the discrepancy $D(N)$ is the
supremum, over rationals $p, q$ with $0 \le p \le q \le 1$, of $\lvert A(p, q) - (q - p) N \rvert$,
where $A(p, q)$ is the number of indices $n < N$ for which the fractional part $\{\alpha x_n\}$
lies in the closed interval $[p, q]$. -/
noncomputable def discrep (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup { d : ℝ | ∃ p q : ℚ, 0 ≤ (p : ℝ) ∧ (q : ℝ) ≤ 1 ∧ (p : ℝ) ≤ (q : ℝ) ∧
    d = |(CountQ x α N p q : ℝ) - ((q : ℝ) - (p : ℝ)) * (N : ℝ)| }

/-- **Erdős Problem 992 on the discrepancy of fractional parts.** For a strictly increasing
sequence of integers $x_0 < x_1 < \cdots$, a real number $\alpha$ and a natural number $N$, let
$D(N)$ be the supremum, over rationals $p, q$ with $0 \le p \le q \le 1$, of
$\lvert A(p, q) - (q - p) N \rvert$, where $A(p, q)$ is the number of indices $n < N$ for which
the fractional part $\{\alpha x_n\}$ lies in $[p, q]$. The statement is that for every such
sequence, for almost every $\alpha \in [0, 1]$ (Lebesgue measure) and every $\varepsilon > 0$,
there is a real constant $C$ such that $D(N) \le C \sqrt{N} (\log N)^{\varepsilon}$ for all
sufficiently large $N$. -/
def conjecture : Prop :=
  ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
        ∀ᶠ N : ℕ in atTop,
          discrep x α N ≤ C * Real.sqrt (N : ℝ) * Real.rpow (Real.log (N : ℝ)) ε

open Set Finset

-- Block k has about k log k terms. Its mixed-radix digit has base twice that length.
private def length (k : ℕ) := max 1 k * (Nat.log 2 k + 1)
private def radix (k : ℕ) := 2 * length k
private def step (k : ℕ) := ∏ i ∈ range k, radix i
private def start (k : ℕ) := ∑ i ∈ range k, length i

private theorem length_pos (k : ℕ) : 0 < length k :=
  Nat.mul_pos (by simp) (by omega)

private theorem length_mono : Monotone length := by
  intro i j hij
  unfold length
  gcongr

private theorem radix_pos (k : ℕ) : 0 < radix k := Nat.mul_pos (by decide) (length_pos k)

private theorem step_pos (k : ℕ) : 0 < step k := Finset.prod_pos fun i _ => radix_pos i

private theorem step_succ (k : ℕ) : step (k + 1) = step k * radix k :=
  Finset.prod_range_succ _ _

private theorem start_succ (k : ℕ) : start (k + 1) = start k + length k :=
  Finset.sum_range_succ _ _

private theorem start_strict : StrictMono start := strictMono_nat_of_lt_succ fun k => by
  rw [start_succ]
  exact Nat.lt_add_of_pos_right (length_pos k)

private theorem divergence : ¬ Summable (fun k => (radix k : ℝ)⁻¹) := by
  intro h
  have hc := (summable_condensed_iff_of_nonneg
    (f := fun k => (radix k : ℝ)⁻¹) (fun _ => by positivity) (by
      intro m n _ hmn
      exact inv_anti₀ (by exact_mod_cast radix_pos m)
        (by exact_mod_cast Nat.mul_le_mul_left 2 (length_mono hmn)))).2 h
  have hs := hc.mul_left (2 : ℝ)
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).1
  refine hs.congr fun n => ?_
  have hp : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
  simp [radix, length, max_eq_right hp, Nat.log_pow (by decide : 1 < 2)]
  field_simp

private theorem fract_mul (y : ℝ) (b : ℕ) :
    Int.fract (Int.fract y * b) = Int.fract (y * b) := by
  rw [show Int.fract y = y - ⌊y⌋ from rfl, sub_mul, ← Int.cast_natCast b, ← Int.cast_mul,
    Int.fract_sub_intCast]

-- One mixed-radix step. A set avoiding digit zero occupies at most b - 1
-- inverse branches, each of which divides Lebesgue measure by b.
private theorem branch_bound {S T : Set ℝ} {b a : ℕ} (hb : 0 < b) (ha : a ≤ b)
    (hT : T ⊆ Set.Ico 0 1) (h : ∀ y ∈ S, y ∈ Set.Ico 0 1 ∧
      (a : ℝ) ≤ y * b ∧ Int.fract (y * b) ∈ T) :
    volume.real S ≤ (b - (a : ℝ)) * (volume.real T / b) := by
  let A (i : ℕ) : Set ℝ := (· * (b : ℝ)) ⁻¹' ((· + (-(i : ℝ))) ⁻¹' T)
  have hcover : S ⊆ ⋃ i ∈ Finset.Ico a b, A i := by
    intro y hy
    obtain ⟨hyI, hlo, ht⟩ := h y hy
    have hnon : 0 ≤ y * b := mul_nonneg hyI.1 (by positivity)
    refine mem_iUnion₂.mpr ⟨⌊y * b⌋₊, Finset.mem_Ico.mpr
      ⟨Nat.le_floor hlo, (Nat.floor_lt hnon).mpr ?_⟩, ?_⟩
    · simpa using mul_lt_mul_of_pos_right hyI.2 (Nat.cast_pos.mpr hb : 0 < (b : ℝ))
    · simpa [A, Int.fract, natCast_floor_eq_intCast_floor hnon, sub_eq_add_neg] using ht
  have vA (i : ℕ) : volume (A i) = ENNReal.ofReal (b : ℝ)⁻¹ * volume T := by
    simp [A, Real.volume_preimage_mul_right (Nat.cast_ne_zero.mpr hb.ne'),
      measure_preimage_add_right, abs_of_nonneg]
  have hfin : volume T ≠ ⊤ := measure_ne_top_of_subset hT (by simp)
  have hfinA (i : ℕ) : volume (A i) ≠ ⊤ := by rw [vA]; finiteness
  calc
    volume.real S ≤ volume.real (⋃ i ∈ Finset.Ico a b, A i) := measureReal_mono hcover
      (measure_biUnion_ne_top (Finset.Ico a b).finite_toSet fun i _ => hfinA i)
    _ ≤ ∑ i ∈ Finset.Ico a b, volume.real (A i) := measureReal_biUnion_finset_le _ _
    _ = _ := by
      simp [measureReal_def, vA, Nat.cast_sub ha, div_eq_inv_mul, ENNReal.toReal_ofReal]

private def good (α : ℝ) (k : ℕ) : Prop := Int.fract (α * step k) * radix k < 1

-- Follow the image of the exceptional set after k digits have been removed.
-- Its measure is at most one and increases by at least v 0 / radix k
-- at every step after M. Divergence of the reciprocal radices forces v 0 = 0.
private theorem tail_null (M : ℕ) :
    volume {α ∈ Set.Ico (0 : ℝ) 1 | ∀ k ≥ M, ¬good α k} = 0 := by
  let S := {α ∈ Set.Ico (0 : ℝ) 1 | ∀ k ≥ M, ¬good α k}
  let T (k : ℕ) := (fun α : ℝ => Int.fract (α * step k)) '' S
  let v (k : ℕ) := volume.real (T k)
  have hT (k : ℕ) : T k ⊆ Set.Ico 0 1 := by
    rintro _ ⟨α, _, rfl⟩
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hv (k : ℕ) : v k ≤ 1 := by
    simpa [Real.volume_real_Ico] using measureReal_mono (μ := volume) (hT k) (by simp)
  have hstep (k a : ℕ) (ha : a ≤ radix k)
      (hl : ∀ α ∈ S, (a : ℝ) ≤ Int.fract (α * step k) * radix k) :
      v k ≤ (radix k - (a : ℝ)) * (v (k + 1) / radix k) := by
    apply branch_bound (radix_pos k) ha (hT _)
    rintro y ⟨α, hα, rfl⟩
    refine ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, hl α hα, α, hα, ?_⟩
    rw [fract_mul, step_succ, Nat.cast_mul, mul_assoc]
  have hmono : Monotone v := monotone_nat_of_le_succ fun k => by
    have h := hstep k 0 (Nat.zero_le _) fun α _ => by
      rw [Nat.cast_zero]
      positivity
    simpa [mul_div_cancel₀, ne_of_gt (radix_pos k), mul_div_assoc'] using h
  have hsum : Summable fun k => v (k + 1) - v k := by
    apply summable_of_sum_range_le (c := 1) (fun k => sub_nonneg.mpr (hmono k.le_succ))
    intro n
    rw [Finset.sum_range_sub]
    exact sub_le_self _ measureReal_nonneg |>.trans (hv n)
  have hzero : v 0 = 0 := by
    by_contra hn
    have hpos : 0 < v 0 := lt_of_le_of_ne measureReal_nonneg (Ne.symm hn)
    apply divergence
    have hs := hsum.mul_left (v 0)⁻¹
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop M] with k hk
    have h := hstep k 1 (radix_pos k) fun α hα => by
      simpa [good] using hα.2 k hk
    have hb : 0 < (radix k : ℝ) := by exact_mod_cast radix_pos k
    have hinc : v 0 / radix k ≤ v (k + 1) - v k := by
      have h' : v k * radix k ≤ (radix k - (1 : ℝ)) * v (k + 1) := by
        rw [← le_div_iff₀ hb, mul_div_assoc]
        exact_mod_cast h
      rw [div_le_iff₀ hb]
      linarith only [h', hmono (Nat.zero_le (k + 1))]
    simp only [Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    rw [← div_eq_inv_mul, le_div_iff₀ hpos]
    simpa [div_eq_mul_inv, mul_comm] using hinc
  have h0 : T 0 = S := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      simpa [step, Int.fract_eq_self.mpr hβ.1] using hβ
    · intro hα
      exact ⟨α, hα, by simp [step, Int.fract_eq_self.mpr hα.1]⟩
  have hf : volume S ≠ ⊤ := measure_ne_top_of_subset (fun _ h => h.1) (t := S)
    (s := Set.Ico 0 1) (by simp)
  change volume S = 0
  apply Or.resolve_right _ hf
  apply (ENNReal.toReal_eq_zero_iff _).mp
  simpa only [v, h0, measureReal_def] using hzero

private theorem ae_good :
    ∀ᵐ α ∂volume.restrict (Set.Icc (0 : ℝ) 1), ∃ᶠ k in atTop, good α k := by
  rw [← Measure.restrict_congr_set Ico_ae_eq_Icc, ae_restrict_iff' measurableSet_Ico]
  have hm (M : ℕ) : ∀ᵐ α : ℝ, α ∈ Set.Ico 0 1 → ∃ k ≥ M, good α k := by
    rw [ae_iff]
    simpa only [not_imp, not_exists, not_and, mem_ofPred_eq] using tail_null M
  filter_upwards [ae_all_iff.mpr hm] with α h hα
  exact frequently_atTop.mpr fun M => h M hα

-- Concatenate the progressions step k, 2 * step k, ..., length k * step k.
private def block (n : ℕ) : ℕ := Nat.find (show ∃ k, n < start (k + 1) from
  ⟨n, Nat.lt_of_lt_of_le n.lt_succ_self (start_strict.id_le _)⟩)

private theorem block_spec (n : ℕ) : start (block n) ≤ n ∧ n < start (block n + 1) := by
  refine ⟨?_, Nat.find_spec (p := fun j => n < start (j + 1)) _⟩
  cases h : block n with
  | zero => simp [start]
  | succ k =>
    exact not_lt.mp (Nat.find_min (p := fun j => n < start (j + 1)) _
      (show k < block n by omega))

private theorem block_eq {k n : ℕ} (h₁ : start k ≤ n) (h₂ : n < start (k + 1)) :
    block n = k := by
  obtain ⟨h₃, h₄⟩ := block_spec n
  apply le_antisymm
  · by_contra! h
    exact (start_strict.monotone h).not_gt (h₃.trans_lt h₂)
  · by_contra! h
    exact (start_strict.monotone h).not_gt (h₁.trans_lt h₄)

private def seq (n : ℕ) : ℤ := ((step (block n) * (n - start (block n) + 1) : ℕ) : ℤ)

private theorem step_mono : Monotone step := monotone_nat_of_le_succ fun k => by
  rw [step_succ]
  exact Nat.le_mul_of_pos_right _ (radix_pos k)

private theorem seq_strict : StrictMono seq := by
  intro n m hnm
  obtain ⟨hn, hn'⟩ := block_spec n
  obtain ⟨hm, hm'⟩ := block_spec m
  unfold seq
  apply Nat.cast_lt.mpr
  rcases eq_or_ne (block n) (block m) with h | h
  · rw [← h]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (step_pos _)
  have hlt : block n < block m := by
    by_contra! hge
    have := start_strict.monotone (show block m + 1 ≤ block n by omega)
    omega
  have hlen : n - start (block n) + 1 ≤ length (block n) := by
    rw [start_succ] at hn'
    omega
  calc
    _ ≤ step (block n) * length (block n) := Nat.mul_le_mul_left _ hlen
    _ < step (block n + 1) := by
      rw [step_succ]
      apply Nat.mul_lt_mul_of_pos_left _ (step_pos _)
      have := length_pos (block n)
      unfold radix
      omega
    _ ≤ step (block m) := step_mono hlt
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

private theorem half_count_le (x : ℕ → ℤ) (α : ℝ) (N : ℕ) :
    |(CountQ x α N 0 (1 / 2) : ℝ) - N / 2| ≤ discrep x α N := by
  apply le_csSup
  · refine ⟨(N : ℝ), ?_⟩
    rintro _ ⟨p, q, hp, hq, hpq, rfl⟩
    have hc : CountQ x α N p q ≤ N := by
      simpa [CountQ] using (Finset.card_filter_le (s := range N)
        (fun n => Int.fract (α * (x n : ℝ)) ∈ Set.Icc (p : ℝ) (q : ℝ)))
    have hd : (q : ℝ) - p ≤ 1 := by linarith
    rw [abs_le]
    constructor <;> nlinarith [Nat.cast_le (α := ℝ).mpr hc, Nat.cast_nonneg (α := ℝ) N,
      mul_nonneg (sub_nonneg.mpr hpq) (Nat.cast_nonneg (α := ℝ) N),
      mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (α := ℝ) N)]
  · refine ⟨0, 1 / 2, ?_⟩
    norm_num
    ring_nf

private theorem count_block {α : ℝ} {k : ℕ} (hg : good α k) :
    CountQ seq α (start (k + 1)) 0 (1 / 2) = CountQ seq α (start k) 0 (1 / 2) + length k := by
  classical
  have hh (j : ℕ) (hj : j < length k) :
      Int.fract (α * (seq (start k + j) : ℝ)) ∈ Set.Icc ((0 : ℚ) : ℝ) ((1 / 2 : ℚ) : ℝ) := by
    have he := block_eq (k := k) (n := start k + j) (by omega) (by rw [start_succ]; omega)
    simp only [seq, he, Nat.add_sub_cancel_left]
    push_cast
    rw [← mul_assoc, ← Nat.cast_one (R := ℝ), ← Nat.cast_add, ← fract_mul]
    have h₀ := Int.fract_nonneg (α * step k)
    have h₁ : Int.fract (α * step k) * (length k : ℝ) < 1 / 2 := by
      unfold good radix at hg
      push_cast at hg
      linarith
    have h₂ := (mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).mpr hj) h₀).trans_lt h₁
    rw [Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩]
    exact ⟨by positivity, by simpa only [Nat.cast_one] using h₂.le⟩
  have hc (j : ℕ) (hj : j ≤ length k) : CountQ seq α (start k + j) 0 (1 / 2) =
      CountQ seq α (start k) 0 (1 / 2) + j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← Nat.add_assoc, ← Nat.add_assoc, ← ih (by omega)]
      simp only [CountQ, range_add_one (n := start k + j), Finset.filter_insert,
        hh j (by omega), ite_true]
      rw [Finset.card_insert_of_notMem (by simp)]
  rw [start_succ]
  exact hc _ le_rfl

-- Up to the end of block k there are at most (k + 1) * length k terms.
-- Taking fourth powers shows that a block eventually beats the proposed rate
-- at both its endpoints when ε = 1 / 4.
private theorem block_growth (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, 1 ≤ N → N ≤ start (k + 1) →
      4 * C * Real.sqrt N * (Real.log N) ^ (1 / 4 : ℝ) < length k := by
  obtain ⟨K, hK⟩ := exists_nat_gt (28 * (4 * C) ^ 4)
  filter_upwards [eventually_ge_atTop (2 ^ K), eventually_ge_atTop 1] with k hk hk₁
  intro N hN hN'
  let l := Nat.log 2 k + 1
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hlen : length k = k * l := by simp [length, max_eq_right hk₁, l]
  have ht : N ≤ (k + 1) * length k := hN'.trans <| by
    simpa [start, smul_eq_mul] using sum_le_card_nsmul (range (k + 1)) length (length k)
      (fun i hi => length_mono (Nat.le_of_lt_succ (mem_range.mp hi)))
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk₁
  have hl' : 1 ≤ (l : ℝ) := by exact_mod_cast hl
  have hNr : (N : ℝ) ≤ 2 * (k : ℝ) ^ 2 * l := by
    rw [hlen] at ht
    calc
      (N : ℝ) ≤ (k + 1 : ℕ) * ((k : ℝ) * l) := by exact_mod_cast ht
      _ ≤ (2 * k) * ((k : ℝ) * l) := by push_cast; gcongr; linarith
      _ = _ := by ring
  have hklog : Real.log k ≤ (l : ℝ) * Real.log 2 := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k).le
  have hlog : Real.log N ≤ 7 * (l : ℝ) := by
    have h := Real.log_le_log (by exact_mod_cast hN : (0 : ℝ) < N) hNr
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have h₂ := Real.log_le_self (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.log_le_self (show 0 ≤ (l : ℝ) by positivity),
      mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (l : ℝ) by positivity)]
  have hbig : 28 * (4 * C) ^ 4 < (l : ℝ) := hK.trans_le <| by
    exact_mod_cast (Nat.le_log_of_pow_le (by decide : 1 < 2) hk).trans (Nat.le_succ _)
  have hlog₀ := Real.log_natCast_nonneg N
  apply (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp
  have hpow : ((Real.log N) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = Real.log N := by
    rw [← Real.rpow_mul_natCast hlog₀]
    norm_num
  have hsqrt : Real.sqrt N ^ 4 = (N : ℝ) ^ 2 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, Real.sq_sqrt (by positivity)]
  calc
    _ = (4 * C) ^ 4 * ((N : ℝ) ^ 2) * Real.log N := by rw [mul_pow, mul_pow, hpow, hsqrt]
    _ ≤ (4 * C) ^ 4 * (2 * (k : ℝ) ^ 2 * l) ^ 2 * (7 * l) := by gcongr
    _ = (28 * (4 * C) ^ 4) * ((k : ℝ) ^ 4 * l ^ (3 : ℕ)) := by ring
    _ < (l : ℝ) * ((k : ℝ) ^ 4 * l ^ (3 : ℕ)) := by gcongr
    _ = _ := by rw [hlen]; push_cast; ring

/--
**Erdős Problem 992 has a negative answer.** For a sequence of integers $(x_n)_{n \ge 0}$, a real
number $\alpha$ and a natural number $N$, let $D(N)$ be the supremum, over rationals $p, q$ with
$0 \le p \le q \le 1$, of $\lvert A(p, q) - (q - p) N \rvert$, where $A(p, q)$ is the number of
indices $n < N$ for which the fractional part $\{\alpha x_n\}$ lies in $[p, q]$. It is not true
that for every strictly increasing sequence of integers $x_0 < x_1 < \cdots$, for almost every
$\alpha \in [0, 1]$ and every $\varepsilon > 0$ there is a real constant $C$ with
$D(N) \le C \sqrt{N} (\log N)^{\varepsilon}$ for all sufficiently large $N$.

Berkes and Philipp construct an increasing integer sequence $(n_k)$ with
$\limsup_N \lvert \sum_{k \le N} \cos(2\pi n_k \alpha) \rvert / \sqrt{N \log N} = \infty$ for almost
every $\alpha$; by Koksma's inequality, $D(N)$ is then not $O(\sqrt{N} (\log N)^{\varepsilon})$ for
$\varepsilon < 1/2$.

Source: C. Aistleitner, I. Berkes, R. Tichy, Lacunary sequences in analysis, probability and
number theory, arXiv preprint (2023), arXiv:2301.05561 (reporting I. Berkes, W. Philipp, J.
London Math. Soc. (2) 50 (1994), 454-464), https://arxiv.org/abs/2301.05561. Moved from
`OpenConjectures/NumberTheory/ErdosSequenceDiscrepancy`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨α, _, hα, hg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (by simp : volume (Set.Icc (0 : ℝ) 1) ≠ 0) ((h seq seq_strict).and ae_good)
  obtain ⟨C, hC⟩ := hα (1 / 4) (by norm_num)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hC
  obtain ⟨k, hk, hlarge, hkM, hk₁⟩ := (hg.and_eventually
    ((block_growth |C| (abs_nonneg C)).and
      ((eventually_ge_atTop M).and (eventually_ge_atTop 1)))).exists
  have h₁ : k ≤ start k := start_strict.id_le k
  have h₂ := (start_strict k.lt_succ_self).le
  have hb (N : ℕ) (hN : start k ≤ N) (hN' : N ≤ start (k + 1)) :
      |(CountQ seq α N 0 (1 / 2) : ℝ) - N / 2| < length k / (4 : ℝ) := by
    have hd := (half_count_le seq α N).trans (hM N (by omega))
    change _ ≤ C * Real.sqrt N * (Real.log N) ^ (1 / 4 : ℝ) at hd
    have hu := hlarge N (by omega) hN'
    have hle : C * Real.sqrt N * (Real.log N) ^ (1 / 4 : ℝ) ≤
        |C| * Real.sqrt N * (Real.log N) ^ (1 / 4 : ℝ) := by
      gcongr
      exact le_abs_self C
    linarith only [hd, hu, hle]
  have hleft := (abs_lt.mp (hb _ le_rfl h₂)).1
  have hright := (abs_lt.mp (hb _ h₂ le_rfl)).2
  rw [count_block hk, start_succ] at hright
  push_cast at hright
  linarith

end MathlibExt.NumberTheory.ErdosSequenceDiscrepancyWanted
