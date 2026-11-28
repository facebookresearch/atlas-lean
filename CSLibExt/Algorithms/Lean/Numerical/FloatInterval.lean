/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
public import MathlibExt.Analysis.Numerical.IntervalExpressions

/-!
# Directed rounding and floating-point interval arithmetic

True directed rounding (round-down `rd`, round-up `ru`) for the bounded binary
formats of `FloatingPoint.lean` (`IsFloatIn p qmin qmax`), outward-rounded
interval addition, subtraction and multiplication over the rational interval
carrier, and a stepwise-rounded evaluator for the division-free fragment of
the interval expression syntax whose successful outputs enclose every
compatible pointwise value.

Domain hypotheses throughout: `1 ≤ p`, `qmin ≤ qmax`, and `|x| ≤ M` with
`M = (2 ^ p - 1) * 2 ^ qmax` for bounded-format optimality; the checked
functions test only `|x| ≤ M` at runtime and fail outside it instead of
saturating, while `1 ≤ p` and `qmin ≤ qmax` are caller hypotheses for the
optimality and format theorems. Division is not part of this unit.

## Main results

* `rd_isFloatIn`, `ru_isFloatIn`: round-down/up land in the format.
* `le_rd_of_isFloatIn`, `ru_le_of_isFloatIn`: greatest/least properties.
* `floatOk_eq_true_iff`: the boolean check decides format membership.
* `addF`/`subF`/`mulF` widen lemmas: outward-rounded operations widen.
* `evalF_encloses`: successful evaluation encloses every compatible pointwise value.

van Emden and Moa, The Fundamental Theorems of Interval Analysis,
arXiv:cs/0701141, Section 3.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.FloatInterval

open Cslib.Algorithms.Lean.FloatingPoint
open MathlibExt.Analysis.Numerical.Certified

/-- The magnitude bound `M = (2^p - 1) * 2^qmax`; when `qmin ≤ qmax` it is
the largest finite value of the bounded format. -/
def maxFloat (p : ℕ) (qmax : ℤ) : ℚ :=
  (2 ^ p - 1) * 2 ^ qmax

/-- The rounding grid exponent at `x`: the last-place exponent, clamped below
at `qmin` so subnormal values round on the `2^qmin` grid. -/
def rdExp (p : ℕ) (qmin : ℤ) (x : ℚ) : ℤ :=
  max qmin (ulpExp p x)

/-- **Round down** to the format grid: the greatest representable value at or below `x`
when `1 ≤ p`, `qmin ≤ qmax` and `|x| ≤ maxFloat p qmax`. -/
def rd (p : ℕ) (qmin : ℤ) (x : ℚ) : ℚ :=
  ⌊x / 2 ^ rdExp p qmin x⌋ * 2 ^ rdExp p qmin x

/-- **Round up** to the format grid: the least representable value at or above `x` when
`1 ≤ p`, `qmin ≤ qmax` and `|x| ≤ maxFloat p qmax`. -/
def ru (p : ℕ) (qmin : ℤ) (x : ℚ) : ℚ :=
  ⌈x / 2 ^ rdExp p qmin x⌉ * 2 ^ rdExp p qmin x

/-- Checked round down: fails outside the rounding domain `[-M, M]`. -/
def rdChecked (p : ℕ) (qmin qmax : ℤ) (x : ℚ) : Option ℚ :=
  if |x| ≤ maxFloat p qmax then some (rd p qmin x) else none

/-- Checked round up: fails outside the rounding domain `[-M, M]`. -/
def ruChecked (p : ℕ) (qmin qmax : ℤ) (x : ℚ) : Option ℚ :=
  if |x| ≤ maxFloat p qmax then some (ru p qmin x) else none

/-- **Round-down underestimates**: `rd x` never exceeds `x`, with no hypotheses. -/
theorem rd_le (p : ℕ) (qmin : ℤ) (x : ℚ) : rd p qmin x ≤ x := by
  unfold rd
  have hpos : (0 : ℚ) < 2 ^ rdExp p qmin x := by positivity
  have hle : ((⌊x / 2 ^ rdExp p qmin x⌋ : ℤ) : ℚ) ≤ x / 2 ^ rdExp p qmin x :=
    Int.floor_le _
  have hmul := mul_le_mul_of_nonneg_right hle hpos.le
  rwa [div_mul_cancel₀ x (ne_of_gt hpos)] at hmul

/-- **Round-up overestimates**: `x` never exceeds `ru x`, with no hypotheses. -/
theorem le_ru (p : ℕ) (qmin : ℤ) (x : ℚ) : x ≤ ru p qmin x := by
  unfold ru
  have hpos : (0 : ℚ) < 2 ^ rdExp p qmin x := by positivity
  have hle : x / 2 ^ rdExp p qmin x ≤ ((⌈x / 2 ^ rdExp p qmin x⌉ : ℤ) : ℚ) :=
    Int.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hle hpos.le
  rwa [div_mul_cancel₀ x (ne_of_gt hpos)] at hmul

/-- **Round-down stays in the format**: for `1 ≤ p`, `qmin ≤ qmax` and `|x|` within the
format maximum, `rd x` is representable. -/
theorem rd_isFloatIn {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {x : ℚ} (hx : |x| ≤ maxFloat p qmax) : IsFloatIn p qmin qmax (rd p qmin x) := by
  unfold maxFloat at hx
  unfold rd
  by_cases hzero : (⌊x / 2 ^ rdExp p qmin x⌋ : ℚ) * 2 ^ rdExp p qmin x = 0
  · refine ⟨0, qmin, by simp, le_rfl, hq, ?_⟩
    simp [hzero]
  · have hpos_e : (0 : ℚ) < (2 : ℚ) ^ rdExp p qmin x := by positivity
    have hpow_ne : (2 : ℚ) ^ rdExp p qmin x ≠ 0 := ne_of_gt hpos_e
    have hfloor_ne : ⌊x / 2 ^ rdExp p qmin x⌋ ≠ 0 := by
      intro hcon
      apply hzero
      simp [hcon]
    have hx_ne : x ≠ 0 := by
      intro hcon
      apply hfloor_ne
      simp [hcon]
    have habs_lt : |x / (2 : ℚ) ^ rdExp p qmin x| < (2 : ℚ) ^ p := by
      rcases le_total qmin (ulpExp p x) with hle | hle
      · have heq : rdExp p qmin x = ulpExp p x := max_eq_right hle
        rw [heq]
        exact (scaled_bounds hp hx_ne).2
      · have heq : rdExp p qmin x = qmin := max_eq_left hle
        rw [heq]
        have hlog_le : Int.log 2 |x| ≤ qmin + ((p : ℤ) - 1) := by
          unfold ulpExp at hle
          omega
        have hlog1_le : Int.log 2 |x| + 1 ≤ qmin + (p : ℤ) := by omega
        have hmono : ((2 : ℕ) : ℚ) ^ (Int.log 2 |x| + 1) ≤
            ((2 : ℕ) : ℚ) ^ (qmin + (p : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) hlog1_le
        have hlt : |x| < ((2 : ℕ) : ℚ) ^ (Int.log 2 |x| + 1) :=
          Int.lt_zpow_succ_log_self (by norm_num) _
        have hlt2 : |x| < ((2 : ℕ) : ℚ) ^ (qmin + (p : ℤ)) :=
          lt_of_lt_of_le hlt hmono
        have hlt3 : |x| < (2 : ℚ) ^ (qmin + (p : ℤ)) := by simpa using hlt2
        have hpos_q : (0 : ℚ) < (2 : ℚ) ^ qmin := by positivity
        have hz : (2 : ℚ) ^ (qmin + (p : ℤ)) = (2 : ℚ) ^ qmin * (2 : ℚ) ^ p := by
          rw [zpow_add₀ (by norm_num), zpow_natCast]
        rw [hz] at hlt3
        have habs_eq : |x / (2 : ℚ) ^ qmin| = |x| / (2 : ℚ) ^ qmin := by
          rw [abs_div, abs_of_pos hpos_q]
        rw [habs_eq, div_lt_iff₀ hpos_q]
        calc |x| < (2 : ℚ) ^ qmin * (2 : ℚ) ^ p := hlt3
          _ = (2 : ℚ) ^ p * (2 : ℚ) ^ qmin := mul_comm _ _
    have hy_lt : x / (2 : ℚ) ^ rdExp p qmin x < (2 : ℚ) ^ p :=
      lt_of_le_of_lt (le_abs_self _) habs_lt
    have hy_gt : -((2 : ℚ) ^ p) < x / (2 : ℚ) ^ rdExp p qmin x :=
      neg_lt_of_abs_lt habs_lt
    have hfloor_lo : -((2 : ℤ) ^ p) ≤ ⌊x / 2 ^ rdExp p qmin x⌋ := by
      have h1 : x / (2 : ℚ) ^ rdExp p qmin x - 1 < ((⌊x / 2 ^ rdExp p qmin x⌋ : ℤ) : ℚ) :=
        Int.sub_one_lt_floor _
      have h2 : (-((2 : ℚ) ^ p) - 1) < ((⌊x / 2 ^ rdExp p qmin x⌋ : ℤ) : ℚ) := by linarith
      have hcast : (((-((2 : ℤ) ^ p) - 1 : ℤ)) : ℚ) = (-((2 : ℚ) ^ p) - 1) := by
        push_cast
        ring
      have h3 : (-((2 : ℤ) ^ p) - 1 : ℤ) < ⌊x / 2 ^ rdExp p qmin x⌋ := by
        rw [← hcast] at h2
        exact Int.cast_lt.mp h2
      omega
    have hfloor_hi : ⌊x / 2 ^ rdExp p qmin x⌋ < (2 : ℤ) ^ p := by
      have h1 : ((⌊x / 2 ^ rdExp p qmin x⌋ : ℤ) : ℚ) ≤ x / (2 : ℚ) ^ rdExp p qmin x :=
        Int.floor_le _
      have h2 : ((⌊x / 2 ^ rdExp p qmin x⌋ : ℤ) : ℚ) < (2 : ℚ) ^ p :=
        lt_of_le_of_lt h1 hy_lt
      have hcast : ((((2 : ℤ) ^ p : ℤ)) : ℚ) = (2 : ℚ) ^ p := by push_cast; ring
      rw [← hcast] at h2
      exact Int.cast_lt.mp h2
    have h_ulp_le : ulpExp p x ≤ qmax := by
      have hpos_q : (0 : ℚ) < (2 : ℚ) ^ qmax := by positivity
      have hlt1 : ((2 : ℚ) ^ p - 1) * (2 : ℚ) ^ qmax < (2 : ℚ) ^ p * (2 : ℚ) ^ qmax := by
        apply mul_lt_mul_of_pos_right _ hpos_q
        linarith
      have hz2 : (2 : ℚ) ^ p * (2 : ℚ) ^ qmax = (2 : ℚ) ^ (qmax + (p : ℤ)) := by
        have h1 : (2 : ℚ) ^ p = (2 : ℚ) ^ ((p : ℤ)) := by rw [zpow_natCast]
        rw [h1, mul_comm, zpow_add₀ (by norm_num)]
      have hlt2 : |x| < (2 : ℚ) ^ (qmax + (p : ℤ)) :=
        lt_of_le_of_lt hx (hlt1.trans_le hz2.le)
      have hr : (0 : ℚ) < |x| := abs_pos.mpr hx_ne
      have hb : (1 : ℕ) < 2 := by norm_num
      have hiff := (Int.lt_zpow_iff_log_lt (R := ℚ) (x := qmax + (p : ℤ)) hb hr)
      have hlt_cast : |x| < ((2 : ℕ) : ℚ) ^ (qmax + (p : ℤ)) := by simpa using hlt2
      have hlog_lt : Int.log 2 |x| < qmax + (p : ℤ) := hiff.mp hlt_cast
      unfold ulpExp
      omega
    have he_le : rdExp p qmin x ≤ qmax := max_le hq h_ulp_le
    by_cases h_eq : ⌊x / 2 ^ rdExp p qmin x⌋ = -((2 : ℤ) ^ p)
    · -- renormalization
      have h2p_ge2 : (2 : ℚ) ≤ (2 : ℚ) ^ p := by
        have hle : (2 : ℚ) ^ 1 ≤ (2 : ℚ) ^ p := pow_le_pow_right₀ (by norm_num) hp
        simpa using hle
      have hsub_pos : (0 : ℚ) < (2 : ℚ) ^ p - 1 := by linarith
      have hfloor := (Int.floor_eq_iff).mp h_eq
      have hcast1 : (((-((2 : ℤ) ^ p) : ℤ)) : ℚ) = (-((2 : ℚ) ^ p)) := by push_cast; ring
      rw [hcast1] at hfloor
      have hy_lt2 : x / (2 : ℚ) ^ rdExp p qmin x < -((2 : ℚ) ^ p) + 1 := hfloor.2
      have hy_neg : x / (2 : ℚ) ^ rdExp p qmin x < 0 := by linarith
      have habs_eq2 : |x / (2 : ℚ) ^ rdExp p qmin x| = -(x / (2 : ℚ) ^ rdExp p qmin x) :=
        abs_of_neg hy_neg
      have hgt : ((2 : ℚ) ^ p - 1) < |x / (2 : ℚ) ^ rdExp p qmin x| := by
        rw [habs_eq2]
        linarith
      have hx_eq : |x| = |x / (2 : ℚ) ^ rdExp p qmin x| * (2 : ℚ) ^ rdExp p qmin x := by
        have h1 : (x / (2 : ℚ) ^ rdExp p qmin x) * (2 : ℚ) ^ rdExp p qmin x = x :=
          div_mul_cancel₀ _ hpow_ne
        calc |x| = |(x / (2 : ℚ) ^ rdExp p qmin x) * (2 : ℚ) ^ rdExp p qmin x| := by
              rw [h1]
          _ = |x / (2 : ℚ) ^ rdExp p qmin x| * (2 : ℚ) ^ rdExp p qmin x := by
              rw [abs_mul, abs_of_pos hpos_e]
      have hlt_ren : ((2 : ℚ) ^ p - 1) * (2 : ℚ) ^ rdExp p qmin x <
          ((2 : ℚ) ^ p - 1) * (2 : ℚ) ^ qmax := by
        calc ((2 : ℚ) ^ p - 1) * (2 : ℚ) ^ rdExp p qmin x
            < |x / (2 : ℚ) ^ rdExp p qmin x| * (2 : ℚ) ^ rdExp p qmin x := by
              apply mul_lt_mul_of_pos_right hgt hpos_e
          _ = |x| := by rw [hx_eq]
          _ ≤ ((2 : ℚ) ^ p - 1) * (2 : ℚ) ^ qmax := hx
      have hz_lt : (2 : ℚ) ^ rdExp p qmin x < (2 : ℚ) ^ qmax :=
        lt_of_mul_lt_mul_left hlt_ren hsub_pos.le
      have he_lt : rdExp p qmin x < qmax :=
        (zpow_lt_zpow_iff_right₀ (by norm_num)).mp hz_lt
      have he1_le : rdExp p qmin x + 1 ≤ qmax := by omega
      have hqmin_le1 : qmin ≤ rdExp p qmin x + 1 := by
        have hqm : qmin ≤ rdExp p qmin x := le_max_left _ _
        omega
      have hm_lt : |(-((2 : ℤ) ^ (p - 1)))| < (2 : ℤ) ^ p := by
        rw [abs_neg, abs_of_nonneg (by positivity)]
        have hltp : p - 1 < p := by omega
        have hnat : (2 : ℕ) ^ (p - 1) < (2 : ℕ) ^ p :=
          Nat.pow_lt_pow_right (by norm_num) hltp
        have hc1 : ((2 : ℤ) ^ (p - 1)) = ((((2 : ℕ) ^ (p - 1) : ℕ)) : ℤ) := by
          push_cast
          ring
        have hc2 : ((2 : ℤ) ^ p) = ((((2 : ℕ) ^ p : ℕ)) : ℤ) := by push_cast; ring
        rw [hc1, hc2]
        exact_mod_cast hnat
      have hp_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp
      have hz_pow : (2 : ℤ) ^ p = (2 : ℤ) ^ (p - 1) * 2 := by
        conv_lhs => rw [← hp_eq]
        rw [pow_succ]
      have hq_pow : (2 : ℚ) ^ (rdExp p qmin x + 1) = (2 : ℚ) ^ rdExp p qmin x * 2 := by
        rw [zpow_add_one₀ (by norm_num)]
      have heq_rd : (⌊x / 2 ^ rdExp p qmin x⌋ : ℚ) * 2 ^ rdExp p qmin x =
          (((-((2 : ℤ) ^ (p - 1)) : ℤ)) : ℚ) * 2 ^ (rdExp p qmin x + 1) := by
        rw [h_eq]
        have hcast : (((-((2 : ℤ) ^ p) : ℤ)) : ℚ) = -(((2 : ℚ) ^ (p - 1)) * 2) := by
          rw [hz_pow]
          push_cast
          ring
        rw [hcast, hq_pow]
        push_cast
        ring
      exact ⟨-((2 : ℤ) ^ (p - 1)), rdExp p qmin x + 1, hm_lt, hqmin_le1, he1_le, heq_rd⟩
    · have hgt : -((2 : ℤ) ^ p) < ⌊x / 2 ^ rdExp p qmin x⌋ :=
        lt_of_le_of_ne hfloor_lo (Ne.symm h_eq)
      have habs_m : |⌊x / 2 ^ rdExp p qmin x⌋| < (2 : ℤ) ^ p :=
        abs_lt.mpr ⟨hgt, hfloor_hi⟩
      exact ⟨⌊x / 2 ^ rdExp p qmin x⌋, rdExp p qmin x, habs_m, le_max_left _ _, he_le, rfl⟩

/-- **Round-up is negated round-down.** Rounding up `x` equals `-rd (-x)`,
with no format hypotheses. -/
theorem ru_eq_neg_rd_neg (p : ℕ) (qmin : ℤ) (x : ℚ) :
    ru p qmin x = -rd p qmin (-x) := by
  have hexp : rdExp p qmin (-x) = rdExp p qmin x := by
    unfold rdExp ulpExp
    rw [abs_neg]
  unfold ru rd
  rw [hexp]
  have hdiv : (-x) / (2 : ℚ) ^ rdExp p qmin x =
      -(x / (2 : ℚ) ^ rdExp p qmin x) := by
    rw [neg_div]
  rw [hdiv, Int.floor_neg]
  push_cast
  ring

/-- **Round-up stays in the format**: for `1 ≤ p`, `qmin ≤ qmax` and `|x|` within the
format maximum, `ru x` is representable. -/
theorem ru_isFloatIn {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {x : ℚ} (hx : |x| ≤ maxFloat p qmax) : IsFloatIn p qmin qmax (ru p qmin x) := by
  have hru_eq : ru p qmin x = -rd p qmin (-x) := ru_eq_neg_rd_neg p qmin x
  have hx_neg : |-x| ≤ maxFloat p qmax := by
    rw [abs_neg]
    exact hx
  have hrd : IsFloatIn p qmin qmax (rd p qmin (-x)) := rd_isFloatIn hp hq hx_neg
  rw [hru_eq]
  obtain ⟨m, e', hm, hqmin, hqmax, heq⟩ := hrd
  refine ⟨-m, e', by simpa using hm, hqmin, hqmax, ?_⟩
  rw [heq]
  push_cast
  ring

/-- **Round-down is greatest**: any representable `y ≤ x` lies below `rd x`, under `1 ≤ p`,
`qmin ≤ qmax` and `|x|` within the format maximum. -/
theorem le_rd_of_isFloatIn {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (_hq : qmin ≤ qmax)
    {x y : ℚ} (_hx : |x| ≤ maxFloat p qmax) (hy : IsFloatIn p qmin qmax y) (h : y ≤ x) :
    y ≤ rd p qmin x := by
  unfold rd
  by_cases hx0 : x = 0
  · subst hx0
    have hrd0 : (⌊(0:ℚ) / 2 ^ rdExp p qmin 0⌋ : ℚ) * 2 ^ rdExp p qmin 0 = 0 := by simp
    rw [hrd0]
    exact h
  · have hx_ne : x ≠ 0 := hx0
    obtain ⟨m, e', hm, hqmin_e', he'_qmax, heq⟩ := hy
    rcases lt_or_ge e' (rdExp p qmin x) with hlt | hle
    · have he_eq : rdExp p qmin x = ulpExp p x := by
        rcases le_total qmin (ulpExp p x) with hle2 | hle2
        · exact max_eq_right hle2
        · have heq2 : rdExp p qmin x = qmin := max_eq_left hle2
          omega
      rcases le_total (0:ℚ) x with hx_nonneg | hx_nonpos
      · have hx_pos : (0:ℚ) < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
        have hpos_e : (0:ℚ) < (2:ℚ) ^ rdExp p qmin x := by positivity
        have hpos_e' : (0:ℚ) < (2:ℚ)^e' := by positivity
        have hm_le : |m| ≤ (2:ℤ)^p - 1 := by omega
        have hcast_le0 : ((|m| : ℤ) : ℚ) ≤ (2:ℚ)^p - 1 := by
          have h1 : ((|m| : ℤ) : ℚ) ≤ ((((2:ℤ)^p - 1 : ℤ)) : ℚ) :=
            Int.cast_le.mpr hm_le
          have h2 : ((((2:ℤ)^p - 1 : ℤ)) : ℚ) = (2:ℚ)^p - 1 := by
            push_cast
            ring
          rwa [h2] at h1
        have hy_le_m : |(m : ℚ) * (2:ℚ)^e'| ≤ ((2:ℚ)^p - 1) * (2:ℚ)^e' := by
          have habs : |(m : ℚ) * (2:ℚ)^e'| = ((|m| : ℤ) : ℚ) * (2:ℚ)^e' := by
            rw [abs_mul, abs_of_pos hpos_e', Int.cast_abs]
          rw [habs]
          apply mul_le_mul_of_nonneg_right hcast_le0 hpos_e'.le
        have hy_le : |y| ≤ ((2:ℚ)^p - 1) * (2:ℚ)^e' := by
          rw [heq]
          exact hy_le_m
        have he'_le : e' ≤ rdExp p qmin x - 1 := by omega
        have hmono_e' : (2:ℚ)^e' ≤ (2:ℚ)^(rdExp p qmin x - 1) :=
          zpow_le_zpow_right₀ (by norm_num) he'_le
        have hnonneg_sub : (0:ℚ) ≤ (2:ℚ)^p - 1 := by
          have hge : (1:ℚ) ≤ (2:ℚ)^p := by
            calc (1:ℚ) = (2:ℚ)^(0:ℕ) := by simp
              _ ≤ (2:ℚ)^p := pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
          linarith
        have hle_mul : ((2:ℚ)^p - 1) * (2:ℚ)^e' ≤
            ((2:ℚ)^p - 1) * (2:ℚ)^(rdExp p qmin x - 1) :=
          mul_le_mul_of_nonneg_left hmono_e' hnonneg_sub
        have hlt_double : ((2:ℚ)^p - 1) * (2:ℚ)^(rdExp p qmin x - 1) <
            (2:ℚ)^(p-1) * (2:ℚ)^(rdExp p qmin x) := by
          have hz_sub : (2:ℚ)^(rdExp p qmin x - 1) * 2 = (2:ℚ)^(rdExp p qmin x) := by
            have h1 : (rdExp p qmin x - 1) + 1 = rdExp p qmin x := by omega
            calc (2:ℚ)^(rdExp p qmin x - 1) * 2 = (2:ℚ)^((rdExp p qmin x - 1)+1) := by
                    rw [zpow_add_one₀ (by norm_num)]
              _ = (2:ℚ)^(rdExp p qmin x) := by rw [h1]
          have h2mul : (2:ℚ) * (2:ℚ)^(rdExp p qmin x - 1) = (2:ℚ)^(rdExp p qmin x) := by
            rw [mul_comm]
            exact hz_sub
          have hp_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp
          have hpow_eq : (2:ℚ) * (2:ℚ)^(p-1) = (2:ℚ)^p := by
            conv_rhs => rw [← hp_eq]
            rw [pow_succ]
            ring
          have h2A : (2:ℚ) * (((2:ℚ)^p - 1) * (2:ℚ)^(rdExp p qmin x - 1)) =
              ((2:ℚ)^p - 1) * (2:ℚ)^(rdExp p qmin x) := by
            calc (2:ℚ) * (((2:ℚ)^p - 1) * (2:ℚ)^(rdExp p qmin x - 1))
                = ((2:ℚ)^p - 1) * ((2:ℚ) * (2:ℚ)^(rdExp p qmin x - 1)) := by ring
              _ = ((2:ℚ)^p - 1) * (2:ℚ)^(rdExp p qmin x) := by rw [h2mul]
          have h2B : (2:ℚ) * ((2:ℚ)^(p-1) * (2:ℚ)^(rdExp p qmin x)) =
              (2:ℚ)^p * (2:ℚ)^(rdExp p qmin x) := by
            calc (2:ℚ) * ((2:ℚ)^(p-1) * (2:ℚ)^(rdExp p qmin x))
                = ((2:ℚ) * (2:ℚ)^(p-1)) * (2:ℚ)^(rdExp p qmin x) := by ring
              _ = (2:ℚ)^p * (2:ℚ)^(rdExp p qmin x) := by rw [hpow_eq]
          have hlt2 : (2:ℚ) * (((2:ℚ)^p - 1) * (2:ℚ)^(rdExp p qmin x - 1)) <
              (2:ℚ) * ((2:ℚ)^(p-1) * (2:ℚ)^(rdExp p qmin x)) := by
            rw [h2A, h2B]
            apply mul_lt_mul_of_pos_right _ hpos_e
            linarith
          exact lt_of_mul_lt_mul_left hlt2 (by norm_num)
        have hdiv_pos : (0:ℚ) < x / (2:ℚ)^(rdExp p qmin x) := div_pos hx_pos hpos_e
        have habs_eq : |x / (2:ℚ)^(rdExp p qmin x)| = x / (2:ℚ)^(rdExp p qmin x) :=
          abs_of_pos hdiv_pos
        have hscaled := (scaled_bounds hp hx_ne).1
        have hscaled2 : (2:ℚ)^(p-1) ≤ |x / (2:ℚ)^(rdExp p qmin x)| := by
          rw [he_eq]
          exact hscaled
        rw [habs_eq] at hscaled2
        have hcast_pm1 : ((((2:ℤ)^(p-1) : ℤ)) : ℚ) = (2:ℚ)^(p-1) := by norm_cast
        have hfloor_ge : (2:ℤ)^(p-1) ≤ ⌊x / (2:ℚ)^(rdExp p qmin x)⌋ := by
          rw [Int.le_floor, hcast_pm1]
          exact hscaled2
        have hcast_le2 : ((((2:ℤ)^(p-1) : ℤ)) : ℚ) ≤
            ((⌊x / (2:ℚ)^(rdExp p qmin x)⌋ : ℤ) : ℚ) :=
          Int.cast_le.mpr hfloor_ge
        have hle_rd : (2:ℚ)^(p-1) * (2:ℚ)^(rdExp p qmin x) ≤
            ((⌊x / (2:ℚ)^(rdExp p qmin x)⌋ : ℤ) : ℚ) * (2:ℚ)^(rdExp p qmin x) := by
          have hle_cast : (2:ℚ)^(p-1) ≤ ((⌊x / (2:ℚ)^(rdExp p qmin x)⌋ : ℤ) : ℚ) := by
            rw [← hcast_pm1]
            exact hcast_le2
          exact mul_le_mul_of_nonneg_right hle_cast hpos_e.le
        have h_y_le_B : y ≤ ((2:ℚ)^p - 1) * (2:ℚ)^(rdExp p qmin x - 1) :=
          le_trans (le_trans (le_abs_self y) hy_le) hle_mul
        have h_y_lt_rd : y < ((⌊x / (2:ℚ)^(rdExp p qmin x)⌋ : ℤ) : ℚ) *
            (2:ℚ)^(rdExp p qmin x) :=
          lt_of_lt_of_le (lt_of_le_of_lt h_y_le_B hlt_double) hle_rd
        exact le_of_lt h_y_lt_rd
      · have hx_neg : x < 0 := lt_of_le_of_ne hx_nonpos hx_ne
        have he_lt_ulp : e' < ulpExp p x := by simpa [he_eq] using hlt
        have habs_m : |(m : ℚ) * (2:ℚ)^e'| < |x| := by
          have hpos_e' : (0:ℚ) < (2:ℚ)^e' := by positivity
          have hm_le : |m| ≤ (2:ℤ)^p - 1 := by omega
          have hcast_le : ((|m| : ℤ) : ℚ) ≤ (2:ℚ)^p - 1 := by
            have h1 : ((|m| : ℤ) : ℚ) ≤ ((((2:ℤ)^p - 1 : ℤ)) : ℚ) :=
              Int.cast_le.mpr hm_le
            have h2 : ((((2:ℤ)^p - 1 : ℤ)) : ℚ) = (2:ℚ)^p - 1 := by
              push_cast
              ring
            rwa [h2] at h1
          have hy_le : |(m : ℚ) * (2:ℚ)^e'| ≤ ((2:ℚ)^p - 1) * (2:ℚ)^e' := by
            have habs : |(m : ℚ) * (2:ℚ)^e'| = ((|m| : ℤ) : ℚ) * (2:ℚ)^e' := by
              rw [abs_mul, abs_of_pos hpos_e', Int.cast_abs]
            rw [habs]
            apply mul_le_mul_of_nonneg_right hcast_le hpos_e'.le
          have hlt1 : ((2:ℚ)^p - 1) * (2:ℚ)^e' < (2:ℚ)^p * (2:ℚ)^e' := by
            apply mul_lt_mul_of_pos_right _ hpos_e'
            linarith
          have he_le2 : e' ≤ Int.log 2 |x| - (p:ℤ) := by
            unfold ulpExp at he_lt_ulp
            omega
          have hmono : (2:ℚ)^e' ≤ (2:ℚ)^(Int.log 2 |x| - (p:ℤ)) :=
            zpow_le_zpow_right₀ (by norm_num) he_le2
          have h2p_nonneg : (0:ℚ) ≤ (2:ℚ)^p := by positivity
          have hle2 : (2:ℚ)^p * (2:ℚ)^e' ≤
              (2:ℚ)^p * (2:ℚ)^(Int.log 2 |x| - (p:ℤ)) :=
            mul_le_mul_of_nonneg_left hmono h2p_nonneg
          have hz_eq : (2:ℚ)^p * (2:ℚ)^(Int.log 2 |x| - (p:ℤ)) =
              (2:ℚ)^(Int.log 2 |x|) := by
            have h1 : (2:ℚ)^p = (2:ℚ)^((p:ℤ)) := by rw [zpow_natCast]
            rw [h1, ← zpow_add₀ (by norm_num)]
            congr 1
            omega
          have hr : (0:ℚ) < |x| := abs_pos.mpr hx_ne
          have hlog_le : ((2:ℕ):ℚ)^(Int.log 2 |x|) ≤ |x| :=
            Int.zpow_log_le_self (by norm_num) hr
          have hlog_le2 : (2:ℚ)^(Int.log 2 |x|) ≤ |x| := by simpa using hlog_le
          calc |(m : ℚ) * (2:ℚ)^e'| ≤ ((2:ℚ)^p - 1) * (2:ℚ)^e' := hy_le
            _ < (2:ℚ)^p * (2:ℚ)^e' := hlt1
            _ ≤ (2:ℚ)^p * (2:ℚ)^(Int.log 2 |x| - (p:ℤ)) := hle2
            _ = (2:ℚ)^(Int.log 2 |x|) := hz_eq
            _ ≤ |x| := hlog_le2
        have habs_lt : |y| < |x| := by rw [heq]; exact habs_m
        have hy_neg : y < 0 := lt_of_le_of_lt h hx_neg
        have hx_abs : |x| = -x := abs_of_neg hx_neg
        have hy_abs : |y| = -y := abs_of_neg hy_neg
        have hle_abs : |x| ≤ |y| := by
          rw [hx_abs, hy_abs]
          exact neg_le_neg h
        have hfalse : False := lt_irrefl _ (lt_of_lt_of_le habs_lt hle_abs)
        exact False.elim hfalse
    · have hpos : (0:ℚ) < (2:ℚ) ^ rdExp p qmin x := by positivity
      have hpow_ne : (2:ℚ) ^ rdExp p qmin x ≠ 0 := ne_of_gt hpos
      have hd_nonneg : 0 ≤ e' - rdExp p qmin x := by omega
      have hn_eq : ((e' - rdExp p qmin x).toNat : ℤ) = e' - rdExp p qmin x :=
        Int.toNat_of_nonneg hd_nonneg
      have hz_add : (2:ℚ)^e' = (2:ℚ)^(rdExp p qmin x) * (2:ℚ)^(e' - rdExp p qmin x) := by
        have h1 : rdExp p qmin x + (e' - rdExp p qmin x) = e' := by omega
        conv_lhs => rw [← h1]
        rw [zpow_add₀ (by norm_num)]
      have hz_nat : (2:ℚ)^(e' - rdExp p qmin x) = (2:ℚ)^((e' - rdExp p qmin x).toNat) := by
        conv_lhs => rw [← hn_eq]
        rw [zpow_natCast]
      have hcast_pow : (2:ℚ)^((e' - rdExp p qmin x).toNat) =
          (((2:ℤ)^((e' - rdExp p qmin x).toNat) : ℤ) : ℚ) := by norm_cast
      set n := (e' - rdExp p qmin x).toNat with hn
      have hy_eq : y = ((m * (2:ℤ)^n : ℤ) : ℚ) * (2:ℚ)^(rdExp p qmin x) := by
        rw [heq, hz_add, hz_nat, hcast_pow]
        push_cast
        ring
      have hdiv_le : y / (2:ℚ)^(rdExp p qmin x) ≤ x / (2:ℚ)^(rdExp p qmin x) :=
        (div_le_div_iff_of_pos_right hpos).mpr h
      have hy_div : y / (2:ℚ)^(rdExp p qmin x) = ((m * (2:ℤ)^n : ℤ) : ℚ) := by
        rw [hy_eq, mul_div_cancel_right₀ _ hpow_ne]
      have hle_floor : m * (2:ℤ)^n ≤ ⌊x / (2:ℚ)^(rdExp p qmin x)⌋ := by
        rw [Int.le_floor, ← hy_div]
        exact hdiv_le
      have hcast_le : ((m * (2:ℤ)^n : ℤ) : ℚ) ≤ ((⌊x / (2:ℚ)^(rdExp p qmin x)⌋ : ℤ) : ℚ) :=
        Int.cast_le.mpr hle_floor
      calc y = ((m * (2:ℤ)^n : ℤ) : ℚ) * (2:ℚ)^(rdExp p qmin x) := hy_eq
        _ ≤ (((⌊x / (2:ℚ)^(rdExp p qmin x)⌋ : ℤ)) : ℚ) * (2:ℚ)^(rdExp p qmin x) :=
          mul_le_mul_of_nonneg_right hcast_le hpos.le

/-- **Round-up is least**: any representable `y ≥ x` lies above `ru x`, under `1 ≤ p`,
`qmin ≤ qmax` and `|x|` within the format maximum. -/
theorem ru_le_of_isFloatIn {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {x y : ℚ} (hx : |x| ≤ maxFloat p qmax) (hy : IsFloatIn p qmin qmax y) (h : x ≤ y) :
    ru p qmin x ≤ y := by
  have hru_eq : ru p qmin x = -rd p qmin (-x) := ru_eq_neg_rd_neg p qmin x
  have hy_neg : IsFloatIn p qmin qmax (-y) := by
    obtain ⟨m, e', hm, hqmin, hqmax, heq⟩ := hy
    refine ⟨-m, e', by simpa using hm, hqmin, hqmax, ?_⟩
    rw [heq]
    push_cast
    ring
  have hx_neg : |-x| ≤ maxFloat p qmax := by
    rw [abs_neg]
    exact hx
  have h_neg : -y ≤ -x := neg_le_neg h
  have h_le : -y ≤ rd p qmin (-x) :=
    le_rd_of_isFloatIn hp hq hx_neg hy_neg h_neg
  have h2 : -rd p qmin (-x) ≤ y := by
    have h3 := neg_le_neg h_le
    simpa using h3
  rwa [hru_eq]

/-- **Format members respect the magnitude bound**: if `y` satisfies
`IsFloatIn p qmin qmax y` then `|y| ≤ maxFloat p qmax`. -/
theorem abs_le_maxFloat_of_isFloatIn {p : ℕ} {qmin qmax : ℤ} {y : ℚ}
    (hy : IsFloatIn p qmin qmax y) : |y| ≤ maxFloat p qmax := by
  unfold maxFloat
  obtain ⟨m, e', hm, hqmin, heqmax, heq⟩ := hy
  have hm_le : |m| ≤ (2:ℤ)^p - 1 := by omega
  have hcast_le : ((|m| : ℤ) : ℚ) ≤ (2:ℚ)^p - 1 := by
    have h1 : ((|m| : ℤ) : ℚ) ≤ ((((2:ℤ)^p - 1 : ℤ)) : ℚ) := Int.cast_le.mpr hm_le
    have h2 : ((((2:ℤ)^p - 1 : ℤ)) : ℚ) = (2:ℚ)^p - 1 := by push_cast; ring
    rwa [h2] at h1
  have hpos_e : (0:ℚ) < (2:ℚ)^e' := by positivity
  have hpos_q : (0:ℚ) ≤ (2:ℚ)^qmax := by positivity
  have hy_eq : |y| = ((|m| : ℤ) : ℚ) * (2:ℚ)^e' := by
    rw [heq, abs_mul, abs_of_pos hpos_e, Int.cast_abs]
  have hmono : (2:ℚ)^e' ≤ (2:ℚ)^qmax := zpow_le_zpow_right₀ (by norm_num) heqmax
  have hnonneg_abs : (0:ℚ) ≤ ((|m| : ℤ) : ℚ) := by positivity
  calc |y| = ((|m| : ℤ) : ℚ) * (2:ℚ)^e' := hy_eq
    _ ≤ ((|m| : ℤ) : ℚ) * (2:ℚ)^qmax := mul_le_mul_of_nonneg_left hmono hnonneg_abs
    _ ≤ ((2:ℚ)^p - 1) * (2:ℚ)^qmax := mul_le_mul_of_nonneg_right hcast_le hpos_q

/-- **Round-down fixes format members.** Under valid precision and exponent bounds,
rounding down a representable value returns it unchanged. -/
theorem rd_of_isFloatIn {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {y : ℚ} (hy : IsFloatIn p qmin qmax y) : rd p qmin y = y := by
  have hy_abs : |y| ≤ maxFloat p qmax := abs_le_maxFloat_of_isFloatIn hy
  have h_le1 : rd p qmin y ≤ y := rd_le p qmin y
  have h_le2 : y ≤ rd p qmin y := le_rd_of_isFloatIn hp hq hy_abs hy le_rfl
  exact le_antisymm h_le1 h_le2

/-- **Round-up fixes format members.** Under valid precision and exponent bounds,
rounding up a representable value returns it unchanged. -/
theorem ru_of_isFloatIn {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {y : ℚ} (hy : IsFloatIn p qmin qmax y) : ru p qmin y = y := by
  have hy_abs : |y| ≤ maxFloat p qmax := abs_le_maxFloat_of_isFloatIn hy
  have h_le1 : y ≤ ru p qmin y := le_ru p qmin y
  have h_le2 : ru p qmin y ≤ y := ru_le_of_isFloatIn hp hq hy_abs hy le_rfl
  exact le_antisymm h_le2 h_le1

/-- **Round-down is monotone in range.** Under valid format bounds with both inputs
in range, `x ≤ y` implies `rd x ≤ rd y`. -/
theorem rd_mono {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {x y : ℚ} (hx : |x| ≤ maxFloat p qmax) (hy : |y| ≤ maxFloat p qmax) (h : x ≤ y) :
    rd p qmin x ≤ rd p qmin y := by
  have hrdx : IsFloatIn p qmin qmax (rd p qmin x) := rd_isFloatIn hp hq hx
  have hle : rd p qmin x ≤ y := le_trans (rd_le _ _ _) h
  exact le_rd_of_isFloatIn hp hq hy hrdx hle

/-- **Round-up is monotone in range.** Under valid format bounds with both inputs
in range, `x ≤ y` implies `ru x ≤ ru y`. -/
theorem ru_mono {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {x y : ℚ} (hx : |x| ≤ maxFloat p qmax) (hy : |y| ≤ maxFloat p qmax) (h : x ≤ y) :
    ru p qmin x ≤ ru p qmin y := by
  have hruy : IsFloatIn p qmin qmax (ru p qmin y) := ru_isFloatIn hp hq hy
  have hle : x ≤ ru p qmin y := le_trans h (le_ru _ _ _)
  exact ru_le_of_isFloatIn hp hq hx hruy hle

/-- **Checked round-down succeeds in range.** Success holds exactly when `|x|` is in
range and the result equals plain round-down. -/
theorem rdChecked_eq_some_iff {p : ℕ} {qmin qmax : ℤ} {x y : ℚ} :
    rdChecked p qmin qmax x = some y ↔ |x| ≤ maxFloat p qmax ∧ y = rd p qmin x := by
  unfold rdChecked
  by_cases h : |x| ≤ maxFloat p qmax <;> simp [h, eq_comm]

/-- **Checked round-up succeeds in range.** Success holds exactly when `|x|` is in
range and the result equals plain round-up. -/
theorem ruChecked_eq_some_iff {p : ℕ} {qmin qmax : ℤ} {x y : ℚ} :
    ruChecked p qmin qmax x = some y ↔ |x| ≤ maxFloat p qmax ∧ y = ru p qmin x := by
  unfold ruChecked
  by_cases h : |x| ≤ maxFloat p qmax <;> simp [h, eq_comm]

/-- **Format membership check**: under `1 ≤ p` and `qmin ≤ qmax` it decides
`IsFloatIn p qmin qmax x` (see `floatOk_eq_true_iff`); at an empty format
(`qmax < qmin`) it can return `true` for non-members
(e.g. `floatOk 3 1 0 0 = true` and `floatOk 3 1 0 2 = true`). -/
def floatOk (p : ℕ) (qmin qmax : ℤ) (x : ℚ) : Bool :=
  decide (|x| ≤ maxFloat p qmax) && decide (rd p qmin x = x)

/-- **Boolean check decides membership**: under `1 ≤ p` and `qmin ≤ qmax`, `floatOk`
holds exactly for representable values. -/
theorem floatOk_eq_true_iff {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {x : ℚ} : floatOk p qmin qmax x = true ↔ IsFloatIn p qmin qmax x := by
  unfold floatOk
  constructor
  · intro hok
    obtain ⟨hx, hfix⟩ := (by simpa using hok)
    have hrd : IsFloatIn p qmin qmax (rd p qmin x) := rd_isFloatIn hp hq hx
    rwa [hfix] at hrd
  · intro hy
    have hy_abs : |x| ≤ maxFloat p qmax := abs_le_maxFloat_of_isFloatIn hy
    have hfix : rd p qmin x = x := rd_of_isFloatIn hp hq hy
    simp [hy_abs, hfix]

/-- A nonempty rational interval whose endpoints lie in the bounded format. -/
def IsFloatInterval (p : ℕ) (qmin qmax : ℤ) (I : RatInterval) : Prop :=
  I.lower ≤ I.upper ∧ IsFloatIn p qmin qmax I.lower ∧ IsFloatIn p qmin qmax I.upper

/-- Outward-rounded interval addition, checked against overflow. -/
def addF (p : ℕ) (qmin qmax : ℤ) (I J : RatInterval) : Option RatInterval := do
  let l ← rdChecked p qmin qmax (I.lower + J.lower)
  let u ← ruChecked p qmin qmax (I.upper + J.upper)
  pure ⟨l, u⟩

/-- Outward-rounded interval subtraction `[RD(l1-u2), RU(u1-l2)]`, checked. -/
def subF (p : ℕ) (qmin qmax : ℤ) (I J : RatInterval) : Option RatInterval := do
  let l ← rdChecked p qmin qmax (I.lower - J.upper)
  let u ← ruChecked p qmin qmax (I.upper - J.lower)
  pure ⟨l, u⟩

/-- Outward-rounded interval multiplication over the four corner products. -/
def mulF (p : ℕ) (qmin qmax : ℤ) (I J : RatInterval) : Option RatInterval := do
  let lo := min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  let hi := max (max (I.lower * J.lower) (I.lower * J.upper))
    (max (I.upper * J.lower) (I.upper * J.upper))
  let l ← rdChecked p qmin qmax lo
  let u ← ruChecked p qmin qmax hi
  pure ⟨l, u⟩

/-- **Rounded constant.** The result is the outward enclosure `[rd q, ru q]`,
failing when `|q| > maxFloat p qmax`. Under `1 ≤ p` and `qmin ≤ qmax` it is
the singleton `{q}` exactly when `q` is representable; at an empty format it
still returns `[rd q, ru q]` for `|q| ≤ maxFloat p qmax` (e.g. the singleton
`2` for `constF 3 1 0 2`), with no representable endpoint. -/
def constF (p : ℕ) (qmin qmax : ℤ) (q : ℚ) : Option RatInterval := do
  let l ← rdChecked p qmin qmax q
  let u ← ruChecked p qmin qmax q
  pure ⟨l, u⟩

/-- **Rounded addition stays in the format.** Under valid format bounds, a successful
step on float intervals yields a float interval. -/
theorem addF_isFloatInterval {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {I J K : RatInterval} (hI : IsFloatInterval p qmin qmax I)
    (hJ : IsFloatInterval p qmin qmax J) (h : addF p qmin qmax I J = some K) :
    IsFloatInterval p qmin qmax K := by
  rw [addF] at h
  obtain ⟨l, hl, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hK⟩ := Option.bind_eq_some_iff.mp h₂
  obtain rfl := Option.some.inj hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨hxl, rfl⟩ := hl
  obtain ⟨hxu, rfl⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · exact (rd_le _ _ _).trans ((add_le_add hI.1 hJ.1).trans (le_ru _ _ _))
  · exact rd_isFloatIn hp hq hxl
  · exact ru_isFloatIn hp hq hxu

/-- **Rounded addition widens.** A successful step encloses the exact interval sum,
with no format hypotheses. -/
theorem addF_widen {p : ℕ} {qmin qmax : ℤ} {I J K : RatInterval}
    (h : addF p qmin qmax I J = some K) :
    K.lower ≤ (I.add J).lower ∧ (I.add J).upper ≤ K.upper := by
  rw [addF] at h
  obtain ⟨l, hl, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hK⟩ := Option.bind_eq_some_iff.mp h₂
  obtain rfl := Option.some.inj hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨-, rfl⟩ := hl
  obtain ⟨-, rfl⟩ := hu
  simp only [RatInterval.add_lower, RatInterval.add_upper]
  exact ⟨rd_le _ _ _, le_ru _ _ _⟩

/-- **Rounded subtraction stays in the format.** Under valid format bounds, a successful
step on float intervals yields a float interval. -/
theorem subF_isFloatInterval {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {I J K : RatInterval} (hI : IsFloatInterval p qmin qmax I)
    (hJ : IsFloatInterval p qmin qmax J) (h : subF p qmin qmax I J = some K) :
    IsFloatInterval p qmin qmax K := by
  rw [subF] at h
  obtain ⟨l, hl, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hK⟩ := Option.bind_eq_some_iff.mp h₂
  obtain rfl := Option.some.inj hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨hxl, rfl⟩ := hl
  obtain ⟨hxu, rfl⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · exact (rd_le _ _ _).trans ((sub_le_sub hI.1 hJ.1).trans (le_ru _ _ _))
  · exact rd_isFloatIn hp hq hxl
  · exact ru_isFloatIn hp hq hxu

/-- **Rounded subtraction widens.** A successful step encloses the exact interval
difference, with no format hypotheses. -/
theorem subF_widen {p : ℕ} {qmin qmax : ℤ} {I J K : RatInterval}
    (h : subF p qmin qmax I J = some K) :
    K.lower ≤ (I.sub J).lower ∧ (I.sub J).upper ≤ K.upper := by
  rw [subF] at h
  obtain ⟨l, hl, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hK⟩ := Option.bind_eq_some_iff.mp h₂
  obtain rfl := Option.some.inj hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨-, rfl⟩ := hl
  obtain ⟨-, rfl⟩ := hu
  simp only [RatInterval.sub_lower, RatInterval.sub_upper]
  exact ⟨rd_le _ _ _, le_ru _ _ _⟩

/-- **Rounded multiplication stays in the format.** Under valid format bounds, a
successful step on float intervals yields a float interval. -/
theorem mulF_isFloatInterval {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {I J K : RatInterval} (_hI : IsFloatInterval p qmin qmax I)
    (_hJ : IsFloatInterval p qmin qmax J) (h : mulF p qmin qmax I J = some K) :
    IsFloatInterval p qmin qmax K := by
  rw [mulF] at h
  obtain ⟨l, hl, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hK⟩ := Option.bind_eq_some_iff.mp h₂
  obtain rfl := Option.some.inj hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨hxl, rfl⟩ := hl
  obtain ⟨hxu, rfl⟩ := hu
  have h1 : min (min (I.lower * J.lower) (I.lower * J.upper))
      (min (I.upper * J.lower) (I.upper * J.upper)) ≤ I.lower * J.lower :=
    (min_le_left _ _).trans (min_le_left _ _)
  have h2 : I.lower * J.lower ≤ max (max (I.lower * J.lower) (I.lower * J.upper))
      (max (I.upper * J.lower) (I.upper * J.upper)) :=
    (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · exact (rd_le _ _ _).trans (h1.trans (h2.trans (le_ru _ _ _)))
  · exact rd_isFloatIn hp hq hxl
  · exact ru_isFloatIn hp hq hxu

/-- **Rounded multiplication widens.** A successful step encloses the exact interval
product, with no format hypotheses. -/
theorem mulF_widen {p : ℕ} {qmin qmax : ℤ} {I J K : RatInterval}
    (h : mulF p qmin qmax I J = some K) :
    K.lower ≤ (I.mul J).lower ∧ (I.mul J).upper ≤ K.upper := by
  rw [mulF] at h
  obtain ⟨l, hl, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hK⟩ := Option.bind_eq_some_iff.mp h₂
  obtain rfl := Option.some.inj hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨-, rfl⟩ := hl
  obtain ⟨-, rfl⟩ := hu
  simp only [RatInterval.mul_lower, RatInterval.mul_upper]
  exact ⟨rd_le _ _ _, le_ru _ _ _⟩

/-- **Negation preserves float intervals.** Negating a float interval yields a float
interval, with no format hypotheses. -/
theorem neg_isFloatInterval {p : ℕ} {qmin qmax : ℤ} {I : RatInterval}
    (hI : IsFloatInterval p qmin qmax I) : IsFloatInterval p qmin qmax I.neg := by
  refine ⟨?_, ?_, ?_⟩
  · change -I.upper ≤ -I.lower
    exact neg_le_neg hI.1
  · change IsFloatIn p qmin qmax (-I.upper)
    obtain ⟨m, e, hm, h1, h2, hx⟩ := hI.2.2
    exact ⟨-m, e, by rwa [abs_neg], h1, h2, by rw [hx]; push_cast; ring⟩
  · change IsFloatIn p qmin qmax (-I.lower)
    obtain ⟨m, e, hm, h1, h2, hx⟩ := hI.2.1
    exact ⟨-m, e, by rwa [abs_neg], h1, h2, by rw [hx]; push_cast; ring⟩

/-- **Rounded constants stay in the format.** Under valid format bounds, a successful
constant step yields a float interval. -/
theorem constF_isFloatInterval {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p) (hq : qmin ≤ qmax)
    {q : ℚ} {K : RatInterval} (h : constF p qmin qmax q = some K) :
    IsFloatInterval p qmin qmax K := by
  rw [constF] at h
  obtain ⟨l, hl, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hK⟩ := Option.bind_eq_some_iff.mp h₂
  obtain rfl := Option.some.inj hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨hxl, rfl⟩ := hl
  obtain ⟨hxu, rfl⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · exact (rd_le _ _ _).trans (le_ru _ _ _)
  · exact rd_isFloatIn hp hq hxl
  · exact ru_isFloatIn hp hq hxu

/-- **Rounded constants widen.** A successful constant step encloses the exact singleton,
with no format hypotheses. -/
theorem constF_widen {p : ℕ} {qmin qmax : ℤ} {q : ℚ} {K : RatInterval}
    (h : constF p qmin qmax q = some K) :
    K.lower ≤ (RatInterval.ofRat q).lower ∧ (RatInterval.ofRat q).upper ≤ K.upper := by
  rw [constF] at h
  obtain ⟨l, hl, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hK⟩ := Option.bind_eq_some_iff.mp h₂
  obtain rfl := Option.some.inj hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨-, rfl⟩ := hl
  obtain ⟨-, rfl⟩ := hu
  simp only [RatInterval.ofRat_lower, RatInterval.ofRat_upper]
  exact ⟨rd_le _ _ _, le_ru _ _ _⟩

/-- Stepwise outward-rounded evaluation of an interval expression.
Variable intervals pass through after the `floatOk` check on both endpoints
plus the order check, and negation is exact (no rounding at `var`/`neg` nodes);
division nodes fail unconditionally. A `const`, `add`, `sub` or `mul` node fails
the whole evaluation when a constant, or an unrounded operation bound computed
from its already-rounded children, lies outside `[-M, M]` with
`M = maxFloat p qmax`. -/
def evalF {α : Type*} (p : ℕ) (qmin qmax : ℤ) (valI : α → RatInterval) :
    RatInterval.Expr α → Option RatInterval
  | .var a =>
      if floatOk p qmin qmax (valI a).lower && floatOk p qmin qmax (valI a).upper
          && decide ((valI a).lower ≤ (valI a).upper) then
        some (valI a)
      else
        none
  | .const q => constF p qmin qmax q
  | .neg e => (evalF p qmin qmax valI e).map RatInterval.neg
  | .add e₁ e₂ => do
      let I ← evalF p qmin qmax valI e₁
      let J ← evalF p qmin qmax valI e₂
      addF p qmin qmax I J
  | .sub e₁ e₂ => do
      let I ← evalF p qmin qmax valI e₁
      let J ← evalF p qmin qmax valI e₂
      subF p qmin qmax I J
  | .mul e₁ e₂ => do
      let I ← evalF p qmin qmax valI e₁
      let J ← evalF p qmin qmax valI e₂
      mulF p qmin qmax I J
  | .div _ _ => none

/-- **Rounded evaluation widens**: under `1 ≤ p` and `qmin ≤ qmax`, a
successful `evalF` result has representable endpoints and encloses the exact
interval evaluation. -/
theorem evalF_widen {α : Type*} {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p)
    (hq : qmin ≤ qmax) {valI : α → RatInterval} (e : RatInterval.Expr α)
    {K : RatInterval} (h : evalF p qmin qmax valI e = some K) :
    K.lower ≤ (e.evalI valI).lower ∧ (e.evalI valI).upper ≤ K.upper ∧
      IsFloatInterval p qmin qmax K := by
  have mul_mono : ∀ (I J A B : RatInterval),
      A.lower ≤ A.upper → B.lower ≤ B.upper →
      I.lower ≤ A.lower → A.upper ≤ I.upper →
      J.lower ≤ B.lower → B.upper ≤ J.upper →
      (I.mul J).lower ≤ (A.mul B).lower ∧
        (A.mul B).upper ≤ (I.mul J).upper := by
    intro I J A B hA hB h1l h1u h2l h2u
    have hc1_b1 : A.lower ≤ I.upper := le_trans hA h1u
    have ha1_d1 : I.lower ≤ A.upper := le_trans h1l hA
    have hc2_b2 : B.lower ≤ J.upper := le_trans hB h2u
    have ha2_d2 : J.lower ≤ B.upper := le_trans h2l hB
    have mem_c1 : I.Encloses (A.lower : ℝ) :=
      ⟨by exact_mod_cast h1l, by exact_mod_cast hc1_b1⟩
    have mem_d1 : I.Encloses (A.upper : ℝ) :=
      ⟨by exact_mod_cast ha1_d1, by exact_mod_cast h1u⟩
    have mem_c2 : J.Encloses (B.lower : ℝ) :=
      ⟨by exact_mod_cast h2l, by exact_mod_cast hc2_b2⟩
    have mem_d2 : J.Encloses (B.upper : ℝ) :=
      ⟨by exact_mod_cast ha2_d2, by exact_mod_cast h2u⟩
    have e1 := mem_c1.mul mem_c2
    have e2 := mem_c1.mul mem_d2
    have e3 := mem_d1.mul mem_c2
    have e4 := mem_d1.mul mem_d2
    rw [RatInterval.encloses_iff] at e1 e2 e3 e4
    have lo1 : (I.mul J).lower ≤ A.lower * B.lower := by
      have hrr : ((I.mul J).lower : ℝ) ≤ (A.lower : ℝ) * (B.lower : ℝ) :=
        e1.1
      exact_mod_cast hrr
    have lo2 : (I.mul J).lower ≤ A.lower * B.upper := by
      have hrr : ((I.mul J).lower : ℝ) ≤ (A.lower : ℝ) * (B.upper : ℝ) :=
        e2.1
      exact_mod_cast hrr
    have lo3 : (I.mul J).lower ≤ A.upper * B.lower := by
      have hrr : ((I.mul J).lower : ℝ) ≤ (A.upper : ℝ) * (B.lower : ℝ) :=
        e3.1
      exact_mod_cast hrr
    have lo4 : (I.mul J).lower ≤ A.upper * B.upper := by
      have hrr : ((I.mul J).lower : ℝ) ≤ (A.upper : ℝ) * (B.upper : ℝ) :=
        e4.1
      exact_mod_cast hrr
    have hi1 : A.lower * B.lower ≤ (I.mul J).upper := by
      have hrr : (A.lower : ℝ) * (B.lower : ℝ) ≤ ((I.mul J).upper : ℝ) :=
        e1.2
      exact_mod_cast hrr
    have hi2 : A.lower * B.upper ≤ (I.mul J).upper := by
      have hrr : (A.lower : ℝ) * (B.upper : ℝ) ≤ ((I.mul J).upper : ℝ) :=
        e2.2
      exact_mod_cast hrr
    have hi3 : A.upper * B.lower ≤ (I.mul J).upper := by
      have hrr : (A.upper : ℝ) * (B.lower : ℝ) ≤ ((I.mul J).upper : ℝ) :=
        e3.2
      exact_mod_cast hrr
    have hi4 : A.upper * B.upper ≤ (I.mul J).upper := by
      have hrr : (A.upper : ℝ) * (B.upper : ℝ) ≤ ((I.mul J).upper : ℝ) :=
        e4.2
      exact_mod_cast hrr
    have hlow : (I.mul J).lower ≤ (A.mul B).lower := by
      have hAlo : (A.mul B).lower =
          min (min (A.lower * B.lower) (A.lower * B.upper))
            (min (A.upper * B.lower) (A.upper * B.upper)) := rfl
      rw [hAlo]
      exact le_min (le_min lo1 lo2) (le_min lo3 lo4)
    have hhigh : (A.mul B).upper ≤ (I.mul J).upper := by
      have hAhi : (A.mul B).upper =
          max (max (A.lower * B.lower) (A.lower * B.upper))
            (max (A.upper * B.lower) (A.upper * B.upper)) := rfl
      rw [hAhi]
      exact max_le (max_le hi1 hi2) (max_le hi3 hi4)
    exact ⟨hlow, hhigh⟩
  have evalI_nonempty : ∀ (e₀ : RatInterval.Expr α) (K₀ : RatInterval),
      evalF p qmin qmax valI e₀ = some K₀ →
        (e₀.evalI valI).lower ≤ (e₀.evalI valI).upper := by
    intro e₀
    induction e₀ with
    | var a =>
        intro K₀ h₀
        simp only [evalF] at h₀
        cases hc : (floatOk p qmin qmax (valI a).lower &&
            floatOk p qmin qmax (valI a).upper &&
            decide ((valI a).lower ≤ (valI a).upper)) with
        | false =>
            simp [hc] at h₀
        | true =>
            obtain rfl := (by simpa [hc] using h₀)
            have hcond := (Bool.and_eq_true_iff.mp hc).2
            have hle := of_decide_eq_true hcond
            simpa [RatInterval.Expr.evalI] using hle
    | const q =>
        intro K₀ h₀
        simp [RatInterval.Expr.evalI]
    | neg e ih =>
        intro K₀ h₀
        cases hI : evalF p qmin qmax valI e with
        | none =>
            simp [evalF, hI] at h₀
        | some I =>
            obtain rfl := (by simpa [evalF, hI] using h₀)
            have h0 := ih _ hI
            simpa [RatInterval.Expr.evalI] using neg_le_neg h0
    | add e₁ e₂ ih₁ ih₂ =>
        intro K₀ h₀
        cases hA : evalF p qmin qmax valI e₁ with
        | none =>
            simp [evalF, hA] at h₀
        | some A =>
            rw [evalF, hA] at h₀
            change Option.bind _ _ = _ at h₀
            rw [Option.bind_some] at h₀
            cases hB : evalF p qmin qmax valI e₂ with
            | none =>
                simp [hB] at h₀
            | some B =>
                simp [hB] at h₀
                have h1 := ih₁ _ hA
                have h2 := ih₂ _ hB
                simpa [RatInterval.Expr.evalI] using add_le_add h1 h2
    | sub e₁ e₂ ih₁ ih₂ =>
        intro K₀ h₀
        cases hA : evalF p qmin qmax valI e₁ with
        | none =>
            simp [evalF, hA] at h₀
        | some A =>
            rw [evalF, hA] at h₀
            change Option.bind _ _ = _ at h₀
            rw [Option.bind_some] at h₀
            cases hB : evalF p qmin qmax valI e₂ with
            | none =>
                simp [hB] at h₀
            | some B =>
                simp [hB] at h₀
                have h1 := ih₁ _ hA
                have h2 := ih₂ _ hB
                simpa [RatInterval.Expr.evalI] using sub_le_sub h1 h2
    | mul e₁ e₂ ih₁ ih₂ =>
        intro K₀ h₀
        simp [RatInterval.Expr.evalI]
    | div e₁ e₂ =>
        intro K₀ h₀
        simp [evalF] at h₀
  revert K h
  induction e with
  | var a =>
      intro K h
      simp only [evalF] at h
      cases hc : (floatOk p qmin qmax (valI a).lower &&
          floatOk p qmin qmax (valI a).upper &&
          decide ((valI a).lower ≤ (valI a).upper)) with
      | false =>
          simp [hc] at h
      | true =>
          obtain rfl := (by simpa [hc] using h)
          have h12 := (Bool.and_eq_true_iff.mp hc).1
          have h3 := (Bool.and_eq_true_iff.mp hc).2
          have hf1 := (Bool.and_eq_true_iff.mp h12).1
          have hf2 := (Bool.and_eq_true_iff.mp h12).2
          have hle := of_decide_eq_true h3
          have hi1 : IsFloatIn p qmin qmax (valI a).lower :=
            (floatOk_eq_true_iff hp hq).mp hf1
          have hi2 : IsFloatIn p qmin qmax (valI a).upper :=
            (floatOk_eq_true_iff hp hq).mp hf2
          have heval : ((.var a : RatInterval.Expr α).evalI valI) =
              valI a := rfl
          rw [heval]
          exact ⟨le_rfl, le_rfl, hle, hi1, hi2⟩
  | const q =>
      intro K h
      simp only [evalF] at h
      have hw := constF_widen h
      have hi := constF_isFloatInterval hp hq h
      have heval : ((.const q : RatInterval.Expr α).evalI valI) =
          RatInterval.ofRat q := rfl
      rw [heval]
      exact ⟨hw.1, hw.2, hi⟩
  | neg e ih =>
      intro K h
      cases hI : evalF p qmin qmax valI e with
      | none =>
          simp [evalF, hI] at h
      | some I =>
          obtain rfl := (by simpa [evalF, hI] using h)
          have ih3 := ih hI
          obtain ⟨hl, hu, hfloat⟩ := ih3
          have heval : (((.neg e : RatInterval.Expr α)).evalI valI) =
              (e.evalI valI).neg := rfl
          rw [heval]
          have hlow : (I.neg).lower ≤ ((e.evalI valI).neg).lower := by
            have hneg : -I.upper ≤ -((e.evalI valI).upper) := neg_le_neg hu
            simpa [RatInterval.neg_lower] using hneg
          have hhigh : ((e.evalI valI).neg).upper ≤ (I.neg).upper := by
            have hneg : -((e.evalI valI).lower) ≤ -I.lower := neg_le_neg hl
            simpa [RatInterval.neg_upper] using hneg
          have hfi := neg_isFloatInterval hfloat
          exact ⟨hlow, hhigh, hfi⟩
  | add e₁ e₂ ih₁ ih₂ =>
      intro K h
      cases hA : evalF p qmin qmax valI e₁ with
      | none =>
          simp [evalF, hA] at h
      | some A =>
          have hA' := by simpa [evalF, hA] using h
          cases hB : evalF p qmin qmax valI e₂ with
          | none =>
              simp [hB] at hA'
          | some B =>
              have hB' := by simpa [hB] using hA'
              have ihA := ih₁ hA
              have ihB := ih₂ hB
              obtain ⟨hlA, huA, hfA⟩ := ihA
              obtain ⟨hlB, huB, hfB⟩ := ihB
              have hw := addF_widen hB'
              have hfi := addF_isFloatInterval hp hq hfA hfB hB'
              have heval : (((.add e₁ e₂ : RatInterval.Expr α)).evalI valI) =
                  (e₁.evalI valI).add (e₂.evalI valI) := rfl
              rw [heval]
              have hlow : K.lower ≤
                  ((e₁.evalI valI).add (e₂.evalI valI)).lower := by
                have hle : A.lower + B.lower ≤
                    (e₁.evalI valI).lower + (e₂.evalI valI).lower :=
                  add_le_add hlA hlB
                have hw1 : K.lower ≤ (A.add B).lower := hw.1
                have hadd : (A.add B).lower = A.lower + B.lower := rfl
                have headd : ((e₁.evalI valI).add (e₂.evalI valI)).lower =
                    (e₁.evalI valI).lower + (e₂.evalI valI).lower := rfl
                rw [hadd] at hw1
                rw [headd]
                exact le_trans hw1 hle
              have hhigh : ((e₁.evalI valI).add (e₂.evalI valI)).upper ≤
                  K.upper := by
                have hle : (e₁.evalI valI).upper + (e₂.evalI valI).upper ≤
                    A.upper + B.upper :=
                  add_le_add huA huB
                have hw2 : (A.add B).upper ≤ K.upper := hw.2
                have hadd : (A.add B).upper = A.upper + B.upper := rfl
                have headd : ((e₁.evalI valI).add (e₂.evalI valI)).upper =
                    (e₁.evalI valI).upper + (e₂.evalI valI).upper := rfl
                rw [hadd] at hw2
                rw [headd]
                exact le_trans hle hw2
              exact ⟨hlow, hhigh, hfi⟩
  | sub e₁ e₂ ih₁ ih₂ =>
      intro K h
      cases hA : evalF p qmin qmax valI e₁ with
      | none =>
          simp [evalF, hA] at h
      | some A =>
          have hA' := by simpa [evalF, hA] using h
          cases hB : evalF p qmin qmax valI e₂ with
          | none =>
              simp [hB] at hA'
          | some B =>
              have hB' := by simpa [hB] using hA'
              have ihA := ih₁ hA
              have ihB := ih₂ hB
              obtain ⟨hlA, huA, hfA⟩ := ihA
              obtain ⟨hlB, huB, hfB⟩ := ihB
              have hw := subF_widen hB'
              have hfi := subF_isFloatInterval hp hq hfA hfB hB'
              have heval : (((.sub e₁ e₂ : RatInterval.Expr α)).evalI valI) =
                  (e₁.evalI valI).sub (e₂.evalI valI) := rfl
              rw [heval]
              have hlow : K.lower ≤
                  ((e₁.evalI valI).sub (e₂.evalI valI)).lower := by
                have hle : A.lower - B.upper ≤
                    (e₁.evalI valI).lower - (e₂.evalI valI).upper :=
                  sub_le_sub hlA huB
                have hw1 : K.lower ≤ (A.sub B).lower := hw.1
                have hadd : (A.sub B).lower = A.lower - B.upper := rfl
                have headd : ((e₁.evalI valI).sub (e₂.evalI valI)).lower =
                    (e₁.evalI valI).lower - (e₂.evalI valI).upper := rfl
                rw [hadd] at hw1
                rw [headd]
                exact le_trans hw1 hle
              have hhigh : ((e₁.evalI valI).sub (e₂.evalI valI)).upper ≤
                  K.upper := by
                have hle : (e₁.evalI valI).upper - (e₂.evalI valI).lower ≤
                    A.upper - B.lower :=
                  sub_le_sub huA hlB
                have hw2 : (A.sub B).upper ≤ K.upper := hw.2
                have hadd : (A.sub B).upper = A.upper - B.lower := rfl
                have headd : ((e₁.evalI valI).sub (e₂.evalI valI)).upper =
                    (e₁.evalI valI).upper - (e₂.evalI valI).lower := rfl
                rw [hadd] at hw2
                rw [headd]
                exact le_trans hle hw2
              exact ⟨hlow, hhigh, hfi⟩
  | mul e₁ e₂ ih₁ ih₂ =>
      intro K h
      cases hA : evalF p qmin qmax valI e₁ with
      | none =>
          simp [evalF, hA] at h
      | some A =>
          have hA' := by simpa [evalF, hA] using h
          cases hB : evalF p qmin qmax valI e₂ with
          | none =>
              simp [hB] at hA'
          | some B =>
              have hB' := by simpa [hB] using hA'
              have ihA := ih₁ hA
              have ihB := ih₂ hB
              obtain ⟨hlA, huA, hfA⟩ := ihA
              obtain ⟨hlB, huB, hfB⟩ := ihB
              have hw := mulF_widen hB'
              have hfi := mulF_isFloatInterval hp hq hfA hfB hB'
              have hnA := evalI_nonempty e₁ A hA
              have hnB := evalI_nonempty e₂ B hB
              have hmono := mul_mono A B (e₁.evalI valI) (e₂.evalI valI)
                hnA hnB hlA huA hlB huB
              have heval : (((.mul e₁ e₂ : RatInterval.Expr α)).evalI valI) =
                  (e₁.evalI valI).mul (e₂.evalI valI) := rfl
              rw [heval]
              have hlow : K.lower ≤
                  ((e₁.evalI valI).mul (e₂.evalI valI)).lower :=
                le_trans hw.1 hmono.1
              have hhigh : ((e₁.evalI valI).mul (e₂.evalI valI)).upper ≤
                  K.upper :=
                le_trans hmono.2 hw.2
              exact ⟨hlow, hhigh, hfi⟩
  | div e₁ e₂ =>
      intro K h
      simp [evalF] at h

/-- **Successful evaluation is well-defined.** A successful stepwise evaluation implies
the expression is well-defined on the interval valuation. -/
theorem evalF_wellDefined {α : Type*} {p : ℕ} {qmin qmax : ℤ}
    {valI : α → RatInterval} (e : RatInterval.Expr α) {K : RatInterval}
    (h : evalF p qmin qmax valI e = some K) : e.WellDefined valI = true := by
  revert K h
  induction e with
  | var a =>
      intro K h
      rfl
  | const q =>
      intro K h
      rfl
  | neg e ih =>
      intro K h
      cases hI : evalF p qmin qmax valI e with
      | none =>
          simp [evalF, hI] at h
      | some I =>
          obtain rfl := (by simpa [evalF, hI] using h)
          have hw := ih hI
          simpa [RatInterval.Expr.WellDefined] using hw
  | add e₁ e₂ ih₁ ih₂ =>
      intro K h
      cases hA : evalF p qmin qmax valI e₁ with
      | none =>
          simp [evalF, hA] at h
      | some A =>
          rw [evalF, hA] at h
          change Option.bind _ _ = _ at h
          rw [Option.bind_some] at h
          cases hB : evalF p qmin qmax valI e₂ with
          | none =>
              simp [hB] at h
          | some B =>
              simp [hB] at h
              have hw1 := ih₁ hA
              have hw2 := ih₂ hB
              simp [RatInterval.Expr.WellDefined, hw1, hw2]
  | sub e₁ e₂ ih₁ ih₂ =>
      intro K h
      cases hA : evalF p qmin qmax valI e₁ with
      | none =>
          simp [evalF, hA] at h
      | some A =>
          rw [evalF, hA] at h
          change Option.bind _ _ = _ at h
          rw [Option.bind_some] at h
          cases hB : evalF p qmin qmax valI e₂ with
          | none =>
              simp [hB] at h
          | some B =>
              simp [hB] at h
              have hw1 := ih₁ hA
              have hw2 := ih₂ hB
              simp [RatInterval.Expr.WellDefined, hw1, hw2]
  | mul e₁ e₂ ih₁ ih₂ =>
      intro K h
      cases hA : evalF p qmin qmax valI e₁ with
      | none =>
          simp [evalF, hA] at h
      | some A =>
          rw [evalF, hA] at h
          change Option.bind _ _ = _ at h
          rw [Option.bind_some] at h
          cases hB : evalF p qmin qmax valI e₂ with
          | none =>
              simp [hB] at h
          | some B =>
              simp [hB] at h
              have hw1 := ih₁ hA
              have hw2 := ih₂ hB
              simp [RatInterval.Expr.WellDefined, hw1, hw2]
  | div e₁ e₂ =>
      intro K h
      simp [evalF] at h

/-- **Rounded evaluation is sound**: under `1 ≤ p` and `qmin ≤ qmax`, when every variable
interval encloses its pointwise value, a successful `evalF` result encloses the exact
real evaluation. -/
theorem evalF_encloses {α : Type*} {p : ℕ} {qmin qmax : ℤ} (hp : 1 ≤ p)
    (hq : qmin ≤ qmax) {valI : α → RatInterval} {val : α → ℝ}
    (hval : ∀ a, (valI a).Encloses (val a)) (e : RatInterval.Expr α)
    {K : RatInterval} (h : evalF p qmin qmax valI e = some K) :
    K.Encloses (e.eval val) := by
  have hw : e.WellDefined valI = true := evalF_wellDefined e h
  have henc : (e.evalI valI).Encloses (e.eval val) :=
    RatInterval.Expr.encloses_eval hval e hw
  have hwiden := evalF_widen hp hq e h
  exact henc.widen hwiden.1 hwiden.2.1

end Cslib.Algorithms.Lean.FloatInterval
