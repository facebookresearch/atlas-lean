/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint

/-!
# Veltkamp splitting in binary floating-point arithmetic

The four rounded operations of SPLIT decompose a binary floating-point number into a high part
and a low part with shorter, nonoverlapping significands, without changing their sum. The model
has unbounded exponents and rounds to nearest with ties to even, so neither overflow nor
underflow occurs. See J. R. Shewchuk, *Adaptive Precision Floating-Point Arithmetic and Fast
Robust Geometric Predicates*, CMU-CS-96-140R, §2.5, Theorem 17, which credits Dekker.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

@[expose] public section

/-- **Veltkamp splitting algorithm.** At precision `p`, first round `(2^s + 1) * a`, then round
its difference with `a`; subtract that second result from the first and round to obtain the
high part. The low part is the rounded difference between `a` and the high part. -/
def veltkampSplit (p s : ℕ) (a : K) : K × K :=
  let c := fl p ((2 ^ s + 1) * a)
  let big := fl p (c - a)
  let hi := fl p (c - big)
  (hi, fl p (a - hi))

/-- Two binary values are nonoverlapping if one is an integer multiple of a power of two and
the other is strictly smaller in magnitude than that power of two. -/
def Nonoverlapping (x y : K) : Prop :=
  (∃ (r t : ℤ), x = (r : K) * 2 ^ t ∧ |y| < 2 ^ t) ∨
    ∃ (r t : ℤ), y = (r : K) * 2 ^ t ∧ |x| < 2 ^ t

end

private theorem ulpExp_eq_of_binade {p : ℕ} {e : ℤ} {x : K}
    (hlo : (2 : K) ^ (e + (p : ℤ) - 1) ≤ x) (hhi : x < (2 : K) ^ (e + (p : ℤ))) :
    ulpExp p x = e := by
  have hx : 0 < x := (two_zpow_pos (e + (p : ℤ) - 1)).trans_le hlo
  have h₁ := (Int.zpow_le_iff_le_log (b := 2) (by decide) hx).mp (by simpa using hlo)
  have h₂ := (Int.lt_zpow_iff_log_lt (b := 2) (by decide) hx).mp (by simpa using hhi)
  rw [ulpExp, abs_of_pos hx]
  omega

private theorem fl_on_grid {p s : ℕ} (hp : 1 ≤ p) {x : K}
    (hlo : ((2 : K) ^ s) * 2 ^ (p - 1) ≤ x) (hhi : x ≤ ((2 : K) ^ s) * 2 ^ p) :
    fl p x = (rne (x / (2 : K) ^ s) : K) * 2 ^ s := by
  rcases hhi.lt_or_eq with hhi | rfl
  · have he : ulpExp p x = (s : ℤ) := by
      apply ulpExp_eq_of_binade
      · convert hlo using 1
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
        congr 1
        omega
      · rw [zpow_add₀ (show (2 : K) ≠ 0 by norm_num), zpow_natCast, zpow_natCast]
        exact hhi
    simp only [fl, he, zpow_natCast]
  · have hfloat : IsFloat p (((2 : K) ^ s) * 2 ^ p) := by
      refine ⟨1, (s : ℤ) + (p : ℤ), ?_, ?_⟩
      · simp only [abs_one]
        exact one_lt_pow₀ (by decide) (by omega)
      · rw [Int.cast_one, one_mul, zpow_add₀ two_ne_zero, zpow_natCast, zpow_natCast]
    rw [fl_eq_self hp hfloat, mul_comm ((2 : K) ^ s), mul_div_cancel_right₀ _ (by positivity)]
    have hr : rne ((2 : K) ^ p) = (2 : ℤ) ^ p := by
      simpa using (rne_intCast (K := K) ((2 : ℤ) ^ p))
    rw [hr]
    push_cast
    rfl

private theorem grid_round_error (x : K) (s : ℕ) :
    |(rne (x / (2 : K) ^ s) : K) * 2 ^ s - x| ≤ (2 : K) ^ s / 2 := by
  have hs : (0 : K) < 2 ^ s := by positivity
  have h := mul_le_mul_of_nonneg_right (abs_rne_sub_le_half (x / (2 : K) ^ s)) hs.le
  have heq : (rne (x / (2 : K) ^ s) : K) * 2 ^ s - x =
      ((rne (x / (2 : K) ^ s) : K) - x / 2 ^ s) * 2 ^ s := by
    rw [sub_mul, div_mul_cancel₀ _ hs.ne']
  rw [heq, abs_mul, abs_of_pos hs]
  linarith only [h]

omit [FloorRing K] in
private theorem isFloat_on_grid_of_abs_le {p : ℕ} {m e : ℤ} (hp : 1 ≤ p)
    (hm : |m| ≤ (2 : ℤ) ^ p) : IsFloat p ((m : K) * 2 ^ e) := by
  rcases hm.lt_or_eq with hm | hm
  · exact ⟨m, e, hm, rfl⟩
  · have hpos : (0 : ℤ) < (2 : ℤ) ^ p := by positivity
    have hone : (1 : ℤ) < (2 : ℤ) ^ p := one_lt_pow₀ (by decide) (by omega)
    rcases (abs_eq hpos.le).mp hm with rfl | rfl
    · refine ⟨1, (p : ℤ) + e, by simpa, ?_⟩
      rw [zpow_add₀ two_ne_zero, zpow_natCast]
      push_cast
      ring
    · refine ⟨-1, (p : ℤ) + e, by simpa, ?_⟩
      rw [zpow_add₀ two_ne_zero, zpow_natCast]
      push_cast
      ring

-- The first operation lies in one of two adjacent binades. Both rounding grids are
-- multiples of `2^s`, and even the coarser one incurs error at most `2^s`.
private theorem split_first {p s : ℕ} (hp : 1 ≤ p) {m : ℤ}
    (hm₁ : (2 : ℤ) ^ (p - 1) ≤ m) (hm₂ : m < (2 : ℤ) ^ p) :
    ∃ k : ℤ, fl p (((2 : K) ^ s + 1) * (m : K)) = (k : K) * 2 ^ s ∧
      |(k : K) * 2 ^ s - ((2 : K) ^ s + 1) * (m : K)| ≤ 2 ^ s := by
  have hD : (1 : K) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hm₁' : (2 : K) ^ (p - 1) ≤ (m : K) := by exact_mod_cast hm₁
  have hm₂' : (m : K) < (2 : K) ^ p := by exact_mod_cast hm₂
  have hm : (0 : K) ≤ (m : K) := (by positivity : (0 : K) ≤ 2 ^ (p - 1)).trans hm₁'
  have hU : (2 : K) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hp]
  let x : K := ((2 : K) ^ s + 1) * (m : K)
  change ∃ k : ℤ, fl p x = (k : K) * 2 ^ s ∧ |(k : K) * 2 ^ s - x| ≤ 2 ^ s
  by_cases h : x ≤ (2 : K) ^ s * 2 ^ p
  · have hlo : (2 : K) ^ s * 2 ^ (p - 1) ≤ x := by
      dsimp [x]
      nlinarith only [mul_le_mul_of_nonneg_left hm₁' (show (0 : K) ≤ 2 ^ s by positivity), hm]
    refine ⟨rne (x / (2 : K) ^ s), fl_on_grid hp hlo h, ?_⟩
    exact (grid_round_error x s).trans (by linarith only [hD])
  · have hlo : (2 : K) ^ (s + 1) * 2 ^ (p - 1) ≤ x := by
      rw [pow_succ, mul_assoc, ← hU]
      exact le_of_not_ge h
    have hhi : x ≤ (2 : K) ^ (s + 1) * 2 ^ p := by
      rw [pow_succ]
      dsimp [x]
      have h1 := mul_le_mul_of_nonneg_right (show (2 : K) ^ s + 1 ≤ 2 ^ s * 2 by linarith) hm
      have h2 := mul_le_mul_of_nonneg_left hm₂'.le
        (show (0 : K) ≤ 2 ^ s * 2 by positivity)
      exact h1.trans h2
    let k := rne (x / (2 : K) ^ (s + 1))
    have heq : ((2 * k : ℤ) : K) * 2 ^ s = (k : K) * 2 ^ (s + 1) := by
      rw [pow_succ]
      push_cast
      ring
    refine ⟨2 * k, ?_, ?_⟩
    · rw [heq]
      exact fl_on_grid hp hlo hhi
    · rw [heq]
      simpa [k, pow_succ] using (grid_round_error x (s + 1))

-- After subtracting the input, the exact difference is back on the finer binade (or
-- its representable upper endpoint). At the lower endpoint the first rounding is exact.
private theorem split_second_input {p s : ℕ} (hp : 2 ≤ p) (hsp : s ≤ p - 1) {m : ℤ} {c : K}
    (hm₁ : (2 : ℤ) ^ (p - 1) ≤ m) (hm₂ : m < (2 : ℤ) ^ p)
    (hc : c = fl p (((2 : K) ^ s + 1) * (m : K)))
    (he : |c - ((2 : K) ^ s + 1) * (m : K)| ≤ 2 ^ s) :
    (2 : K) ^ s * 2 ^ (p - 1) ≤ c - (m : K) ∧ c - (m : K) ≤ 2 ^ s * 2 ^ p := by
  have hD : (0 : K) ≤ 2 ^ s := by positivity
  have hU : (m : K) ≤ (2 : K) ^ p - 1 := by
    exact_mod_cast (show m ≤ (2 : ℤ) ^ p - 1 by omega)
  obtain ⟨hel, heu⟩ := abs_le.mp he
  constructor
  · rcases hm₁.lt_or_eq with hlt | heq
    · have hL : (2 : K) ^ (p - 1) + 1 ≤ (m : K) := by
        exact_mod_cast (show (2 : ℤ) ^ (p - 1) + 1 ≤ m by omega)
      nlinarith only [mul_le_mul_of_nonneg_left hL hD, hel]
    · have hm : (m : K) = (2 : K) ^ (p - 1) := by exact_mod_cast heq.symm
      have hfloat : IsFloat p (((2 : K) ^ s + 1) * (m : K)) := by
        refine ⟨2 ^ s + 1, (p - 1 : ℕ), ?_, ?_⟩
        · have hle : (2 : ℤ) ^ s ≤ 2 ^ (p - 1) := pow_le_pow_right₀ (by decide) hsp
          have hP : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ p by omega)]
          have hL : (1 : ℤ) < 2 ^ (p - 1) := one_lt_pow₀ (by decide) (by omega)
          rw [abs_of_pos (by positivity), hP]
          omega
        · rw [hm, zpow_natCast]
          push_cast
          rfl
      rw [hc, fl_eq_self (by omega) hfloat, hm]
      ring_nf
      exact le_rfl
  · nlinarith only [mul_le_mul_of_nonneg_left hU hD, heu]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] in
private theorem split_exponents {p s : ℕ} (hs : s ≤ p) :
    (2 : ℤ) ^ s * 2 ^ (p - s) = 2 ^ p := by
  rw [← pow_add, Nat.add_sub_of_le hs]

omit [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] in
private theorem isFloat_precision_mono {q p : ℕ} (hqp : q ≤ p) {x : K}
    (hx : IsFloat q x) : IsFloat p x := by
  obtain ⟨m, e, hm, rfl⟩ := hx
  exact ⟨m, e, hm.trans_le (pow_le_pow_right₀ (by decide) hqp), rfl⟩

-- The two rounded intermediate values share a `2^s` grid. The difference between
-- them is close to the original significand and still lies on this grid.
private theorem split_normalized {p s : ℕ} (hp : 3 ≤ p) (hs₂ : 2 ≤ s) (hsp : s < p)
    {m : ℤ} (hm₁ : (2 : ℤ) ^ (p - 1) ≤ m) (hm₂ : m < (2 : ℤ) ^ p) :
    ∃ h l : ℤ, veltkampSplit p s (m : K) = ((h : K) * 2 ^ s, (l : K)) ∧
      m = h * 2 ^ s + l ∧ 0 < h ∧ h ≤ 2 ^ (p - s) ∧ |l| ≤ 2 ^ (s - 1) := by
  let c := fl p (((2 : K) ^ s + 1) * (m : K))
  obtain ⟨k, hc, he⟩ := split_first (K := K) (p := p) (s := s) (by omega) hm₁ hm₂
  change c = (k : K) * 2 ^ s at hc
  change |(k : K) * 2 ^ s - ((2 : K) ^ s + 1) * (m : K)| ≤ 2 ^ s at he
  obtain ⟨hlo, hhi⟩ := split_second_input (by omega) (show s ≤ p - 1 by omega)
    hm₁ hm₂ (rfl : c = _) (hc ▸ he)
  let j := rne ((c - (m : K)) / (2 : K) ^ s)
  let h := k - j
  let l := m - h * 2 ^ s
  have hb : fl p (c - (m : K)) = (j : K) * 2 ^ s := fl_on_grid (by omega) hlo hhi
  have hdiff : c - fl p (c - (m : K)) = (h : K) * 2 ^ s := by
    rw [hb, hc]
    simp only [h, Int.cast_sub, sub_mul]
  have hl : (l : K) = (m : K) - (h : K) * 2 ^ s := by simp [l]
  have hE : |(l : K)| ≤ (2 : K) ^ s / 2 := by
    rw [hl, ← hdiff]
    have herror := grid_round_error (c - (m : K)) s
    change |(j : K) * 2 ^ s - (c - (m : K))| ≤ (2 : K) ^ s / 2 at herror
    rw [← hb] at herror
    convert herror using 2
    ring
  have hmD : (2 : K) ^ s ≤ (m : K) := by
    exact (pow_le_pow_right₀ (by norm_num) (show s ≤ p - 1 by omega)).trans (by exact_mod_cast hm₁)
  have hD : (0 : K) < 2 ^ s := by positivity
  have hhpos : 0 < h := by
    have hpos : 0 < (h : K) * 2 ^ s := by
      have hle := (abs_le.mp hE).2
      rw [hl] at hle
      linarith only [hle, hmD, hD]
    exact_mod_cast (pos_of_mul_pos_left hpos hD.le)
  have hhbound : h ≤ 2 ^ (p - s) := by
    by_contra! hn
    have hi : (2 : K) ^ (p - s) + 1 ≤ (h : K) := by
      exact_mod_cast (show (2 : ℤ) ^ (p - s) + 1 ≤ h by omega)
    have hpow : (2 : K) ^ s * 2 ^ (p - s) = 2 ^ p := by
      exact_mod_cast split_exponents hsp.le
    have hm' : (m : K) < (2 : K) ^ p := by exact_mod_cast hm₂
    have hg := mul_le_mul_of_nonneg_left hi hD.le
    have hl' := (abs_le.mp hE).1
    rw [hl] at hl'
    nlinarith only [hg, hm', hl', hpow, hD]
  have hlbound : |l| ≤ (2 : ℤ) ^ (s - 1) := by
    have hpow : (2 : K) ^ s = 2 * 2 ^ (s - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ s by omega)]
    rw [hpow] at hE
    exact_mod_cast (show |(l : K)| ≤ (2 : K) ^ (s - 1) by linarith only [hE])
  have hhfit : IsFloat (p - s) ((h : K) * 2 ^ s) := by
    rw [← zpow_natCast]
    exact isFloat_on_grid_of_abs_le (by omega) (by rwa [abs_of_pos hhpos])
  have hlfit : IsFloat (s - 1) (l : K) := by
    simpa using (isFloat_on_grid_of_abs_le (K := K) (e := 0) (by omega) hlbound)
  refine ⟨h, l, ?_, by dsimp [l]; ring, hhpos, hhbound, hlbound⟩
  unfold veltkampSplit
  change (fl p (c - fl p (c - (m : K))), fl p ((m : K) - fl p (c - fl p (c - (m : K))))) = _
  rw [hdiff, fl_eq_self (by omega) (isFloat_precision_mono (by omega) hhfit), ← hl,
    fl_eq_self (by omega) (isFloat_precision_mono (by omega) hlfit)]

-- Multiplying a nonzero value by a power of two shifts its binade and its rounding
-- grid by the same amount, leaving the argument to integer rounding unchanged.
private theorem fl_mul_two_zpow (p : ℕ) (x : K) (e : ℤ) :
    fl p (x * 2 ^ e) = fl p x * 2 ^ e := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [fl_zero]
  have hx' : 0 < |x| := abs_pos.2 hx
  have he : (0 : K) < 2 ^ e := two_zpow_pos e
  have hlo : (2 : K) ^ Int.log 2 |x| ≤ |x| := by
    simpa using Int.zpow_log_le_self (b := 2) (by decide) hx'
  have hhi : |x| < (2 : K) ^ (Int.log 2 |x| + 1) := by
    simpa using Int.lt_zpow_succ_log_self (b := 2) (by decide) |x|
  have hpos := mul_pos hx' he
  have hlog₁ : Int.log 2 |x| + e ≤ Int.log 2 (|x| * 2 ^ e) := by
    apply (Int.zpow_le_iff_le_log (b := 2) (by decide) hpos).1
    simpa [zpow_add₀ (two_ne_zero : (2 : K) ≠ 0)] using
      mul_le_mul_of_nonneg_right hlo he.le
  have hlog₂ : Int.log 2 (|x| * 2 ^ e) < (Int.log 2 |x| + 1) + e := by
    apply (Int.lt_zpow_iff_log_lt (b := 2) (by decide) hpos).1
    simpa [zpow_add₀ (two_ne_zero : (2 : K) ≠ 0)] using
      mul_lt_mul_of_pos_right hhi he
  have hExp : ulpExp p (x * 2 ^ e) = ulpExp p x + e := by
    rw [ulpExp, ulpExp, abs_mul, abs_of_pos he]
    omega
  rw [fl, fl, hExp, zpow_add₀ two_ne_zero, mul_div_mul_right _ _ he.ne', mul_assoc]

private theorem rne_neg (x : K) : rne (-x) = -rne x := by
  set n := ⌊x⌋ with hn
  have hlo : (n : K) ≤ x := Int.floor_le x
  have hhi : x < (n : K) + 1 := Int.lt_floor_add_one x
  rcases hlo.eq_or_lt with hx | hx
  · rw [← hx, ← Int.cast_neg, rne_intCast, rne_intCast]
  -- Away from integers, negation swaps the two adjacent integers and their distances.
  have hfloor : ⌊-x⌋ = -(n + 1) := by
    apply Int.floor_eq_iff.2
    push_cast
    constructor <;> linarith
  have hfrac : -x - ((-(n + 1) : ℤ) : K) = 1 - (x - (n : K)) := by
    push_cast
    ring
  rw [rne, rne, hfloor, ← hn, hfrac]
  simp only [even_neg, even_add_one, ← Int.not_even_iff_odd]
  by_cases hlt : x - (n : K) < 1 / 2
  · rw [ite_eq_right (show ¬ 1 - (x - (n : K)) < 1 / 2 by linarith),
      ite_eq_left (show 1 / 2 < 1 - (x - (n : K)) by linarith), ite_eq_left hlt]
    omega
  by_cases hgt : 1 / 2 < x - (n : K)
  · rw [ite_eq_left (show 1 - (x - (n : K)) < 1 / 2 by linarith),
      ite_eq_right hlt, ite_eq_left hgt]
  have htie : x - (n : K) = 1 / 2 := by linarith
  rw [ite_eq_right (show ¬ 1 - (x - (n : K)) < 1 / 2 by linarith),
    ite_eq_right (show ¬ 1 / 2 < 1 - (x - (n : K)) by linarith),
    ite_eq_right hlt, ite_eq_right hgt]
  by_cases he : Even n <;> simp [he]

private theorem fl_neg (p : ℕ) (x : K) : fl p (-x) = -fl p x := by
  simp only [fl, ulpExp, abs_neg, neg_div, rne_neg, Int.cast_neg, neg_mul]

private theorem exists_normalized_int {p : ℕ} (hp : 1 ≤ p) {x : K} (hx : 0 < x)
    (hf : IsFloat p x) : ∃ m e : ℤ, 2 ^ (p - 1) ≤ m ∧ m < 2 ^ p ∧ x = (m : K) * 2 ^ e := by
  let e := ulpExp p x
  let m := rne (x / 2 ^ e)
  have he := two_zpow_pos (K := K) e
  have hrepr : x = (m : K) * 2 ^ e := (fl_eq_self hp hf).symm
  have hscaled : x / 2 ^ e = (m : K) := (div_eq_iff he.ne').2 hrepr
  have hb : (2 : K) ^ (p - 1) ≤ |x / 2 ^ e| ∧ |x / 2 ^ e| < 2 ^ p :=
    scaled_bounds hp hx.ne'
  rw [abs_of_pos (div_pos hx he), hscaled] at hb
  exact ⟨m, e, by exact_mod_cast hb.1, by exact_mod_cast hb.2, hrepr⟩

private theorem split_mul_two_zpow (p s : ℕ) (a : K) (e : ℤ) :
    veltkampSplit p s (a * 2 ^ e) =
      ((veltkampSplit p s a).1 * 2 ^ e, (veltkampSplit p s a).2 * 2 ^ e) := by
  simp only [veltkampSplit, ← mul_assoc, fl_mul_two_zpow, ← sub_mul]

private theorem split_neg (p s : ℕ) (a : K) :
    veltkampSplit p s (-a) = (-(veltkampSplit p s a).1, -(veltkampSplit p s a).2) := by
  have hsub (x y : K) : -x - -y = -(x - y) := by ring
  simp only [veltkampSplit, mul_neg, fl_neg, hsub]

private theorem split_pos_grid {p s : ℕ} (hp : 3 ≤ p) (hs₂ : 2 ≤ s) (hsp : s < p)
    {a : K} (ha : 0 < a) (hf : IsFloat p a) :
    ∃ h l e : ℤ,
      veltkampSplit p s a = ((h : K) * 2 ^ ((s : ℤ) + e), (l : K) * 2 ^ e) ∧
      a = ((h : K) * 2 ^ s + (l : K)) * 2 ^ e ∧
      0 < h ∧ h ≤ 2 ^ (p - s) ∧ |l| ≤ 2 ^ (s - 1) := by
  obtain ⟨m, e, hm₁, hm₂, ha_eq⟩ := exists_normalized_int (by omega) ha hf
  obtain ⟨h, l, hsplit, hm, hh, hfit, hlfit⟩ := split_normalized (K := K) hp hs₂ hsp hm₁ hm₂
  refine ⟨h, l, e, ?_, ?_, hh, hfit, hlfit⟩
  · rw [ha_eq, split_mul_two_zpow, hsplit, zpow_add₀ two_ne_zero, zpow_natCast, mul_assoc]
  · have heq : (m : K) = (h : K) * 2 ^ s + (l : K) := by exact_mod_cast hm
    rw [ha_eq, heq]

private theorem split_nonzero_grid {p s : ℕ} (hp : 3 ≤ p) (hs₂ : 2 ≤ s) (hsp : s < p)
    {a : K} (ha : a ≠ 0) (hf : IsFloat p a) :
    ∃ h l e : ℤ,
      veltkampSplit p s a = ((h : K) * 2 ^ ((s : ℤ) + e), (l : K) * 2 ^ e) ∧
      a = ((h : K) * 2 ^ s + (l : K)) * 2 ^ e ∧
      1 ≤ |h| ∧ |h| ≤ 2 ^ (p - s) ∧ |l| ≤ 2 ^ (s - 1) := by
  rcases ha.lt_or_gt with hneg | hpos
  · have hf' : IsFloat p (-a) := by
      obtain ⟨m, e, hm, ha_eq⟩ := hf
      exact ⟨-m, e, by simpa, by rw [ha_eq, Int.cast_neg, neg_mul]⟩
    obtain ⟨h, l, e, hsplit, ha_eq, hh, hfit, hlfit⟩ :=
      split_pos_grid hp hs₂ hsp (neg_pos.mpr hneg) hf'
    have hsplit' := split_neg p s (-a)
    rw [neg_neg, hsplit] at hsplit'
    refine ⟨-h, -l, e, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Int.cast_neg, neg_mul] using hsplit'
    · push_cast
      calc
        a = -(-a) := (neg_neg a).symm
        _ = -(((h : K) * 2 ^ s + (l : K)) * 2 ^ e) := congrArg Neg.neg ha_eq
        _ = (-↑h * 2 ^ s + -↑l) * 2 ^ e := by ring
    · rw [abs_neg, abs_of_pos hh]
      omega
    · simpa only [abs_neg, abs_of_pos hh] using hfit
    · simpa only [abs_neg] using hlfit
  · obtain ⟨h, l, e, hsplit, ha_eq, hh, hfit, hlfit⟩ := split_pos_grid hp hs₂ hsp hpos hf
    refine ⟨h, l, e, hsplit, ha_eq, ?_, ?_, hlfit⟩
    · rw [abs_of_pos hh]
      omega
    · simpa only [abs_of_pos hh] using hfit

/-- **Correctness of Veltkamp splitting.** For a binary floating-point number `a` with an
unbounded exponent and a `p`-bit significand, `p ≥ 3`, take an integer split point `s` with
`p / 2 ≤ s ≤ p - 1`, where the lower bound is ordinary (not truncated) division. The four
round-to-nearest, ties-to-even operations return high and low parts that sum to `a`, have at
most `p - s` and `s - 1` significand bits respectively, and are nonoverlapping. The high part
has at least the magnitude of the low part. -/
public theorem veltkampSplit_spec {p s : ℕ} (hp : 3 ≤ p) (hhalf : p ≤ 2 * s) (hsp : s < p)
    {a : K} (ha : IsFloat p a) :
    let hi := (veltkampSplit p s a).1
    let lo := (veltkampSplit p s a).2
    a = hi + lo ∧ |lo| ≤ |hi| ∧ IsFloat (p - s) hi ∧ IsFloat (s - 1) lo ∧
      Nonoverlapping hi lo := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp only [veltkampSplit, mul_zero, fl_zero, sub_zero, add_zero, abs_zero, le_refl, true_and]
    refine ⟨⟨0, 0, by simp, by simp⟩, ⟨0, 0, by simp, by simp⟩, Or.inl ⟨0, 0, ?_, ?_⟩⟩
    · simp
    · simp
  obtain ⟨h, l, e, hsplit, ha_eq, hh, hfit, hlfit⟩ :=
    split_nonzero_grid hp (by omega) hsp ha₀ ha
  dsimp only
  rw [hsplit]
  dsimp only
  have hexp : (2 : K) ^ ((s : ℤ) + e) = 2 ^ s * 2 ^ e := by
    rw [zpow_add₀ two_ne_zero, zpow_natCast]
  have hLo : |(l : K) * 2 ^ e| < (2 : K) ^ ((s : ℤ) + e) := by
    rw [hexp, abs_mul, abs_of_pos (two_zpow_pos (K := K) e)]
    apply mul_lt_mul_of_pos_right _ (two_zpow_pos (K := K) e)
    have hle : |(l : K)| ≤ (2 : K) ^ (s - 1) := by exact_mod_cast hlfit
    exact hle.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hHi : (2 : K) ^ ((s : ℤ) + e) ≤ |(h : K) * 2 ^ ((s : ℤ) + e)| := by
    have he := two_zpow_pos (K := K) ((s : ℤ) + e)
    rw [abs_mul, abs_of_pos he]
    have hh' : (1 : K) ≤ |(h : K)| := by exact_mod_cast hh
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh' he.le
  refine ⟨?_, hLo.le.trans hHi, isFloat_on_grid_of_abs_le (by omega) hfit,
    isFloat_on_grid_of_abs_le (by omega) hlfit, Or.inl ⟨h, (s : ℤ) + e, rfl, hLo⟩⟩
  rw [ha_eq, hexp]
  ring

end Cslib.Algorithms.Lean.FloatingPoint
