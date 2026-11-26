/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Data.Seq.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ContinuedFractions.CommonPrefix

/-!
# The conjugate continued fraction is not purely periodic

For integers `P`, `Q` and `D` with `0 < D` not a perfect square and `0 < Q`, the simple
continued fraction of the conjugate `(P - √D) / Q` is not purely periodic
(`MetaMathlibExt.conjugate_continuedFraction_not_purelyPeriodic`): there is no period `s ≥ 1`
with `a_{n+s} = a_n` for every `n ≥ 0`, where the partial quotients `a_n` include
`a_0 = ⌊(P - √D) / Q⌋`. Complete quotients and convergents are developed in private helpers.

Statements from Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Complete quotients of `x`: `cfXi x 0 = x`, `cfXi x (n+1) = (fract (cfXi x n))⁻¹`. -/
private noncomputable def cfXi (x : ℝ) : ℕ → ℝ
  | 0 => x
  | (n + 1) => (Int.fract (cfXi x n))⁻¹

private theorem cfXi_zero (x : ℝ) : cfXi x 0 = x := rfl

private theorem cfXi_succ (x : ℝ) (n : ℕ) : cfXi x (n + 1) = (Int.fract (cfXi x n))⁻¹ := rfl

/-- The fractional part of an irrational is irrational. -/
private theorem irr_fract (y : ℝ) (hy : Irrational y) : Irrational (Int.fract y) := by
  unfold Irrational
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  apply hy
  exact ⟨(⌊y⌋ : ℚ) + q, by
    push_cast
    rw [hq]
    exact Int.floor_add_fract y⟩

/-- Every complete quotient of an irrational is irrational. -/
private theorem irr_cfXi (x : ℝ) (hx : Irrational x) : ∀ n : ℕ, Irrational (cfXi x n)
  | 0 => by rwa [cfXi_zero]
  | (n + 1) => by rw [cfXi_succ]; exact (irr_fract _ (irr_cfXi x hx n)).inv

/-- The fractional part of a complete quotient never vanishes. -/
private theorem fract_cfXi_ne (x : ℝ) (hx : Irrational x) (n : ℕ) :
    Int.fract (cfXi x n) ≠ 0 := by
  intro h0
  apply (irr_cfXi x hx n)
  exact ⟨(⌊cfXi x n⌋ : ℚ), by
    push_cast
    have h1 := Int.floor_add_fract (cfXi x n)
    rw [h0, add_zero] at h1
    exact h1⟩

private theorem fract_cfXi_pos (x : ℝ) (hx : Irrational x) (n : ℕ) :
    0 < Int.fract (cfXi x n) :=
  lt_of_le_of_ne' (Int.fract_nonneg _) (fract_cfXi_ne x hx n)

private theorem fract_cfXi_lt_one (x : ℝ) (_hx : Irrational x) (n : ℕ) :
    Int.fract (cfXi x n) < 1 :=
  Int.fract_lt_one _

/-- Complete quotients from index one on exceed one. -/
private theorem one_lt_cfXi_succ (x : ℝ) (hx : Irrational x) (n : ℕ) :
    1 < cfXi x (n + 1) :=
  (one_lt_inv₀ (fract_cfXi_pos x hx n)).mpr (fract_cfXi_lt_one x hx n)

private theorem floor_cfXi_ge_one (x : ℝ) (hx : Irrational x) (n : ℕ) :
    1 ≤ ⌊cfXi x (n + 1)⌋ := by
  rw [Int.le_floor]
  exact_mod_cast le_of_lt (one_lt_cfXi_succ x hx n)

/-- Splitting a complete quotient into integer and fractional parts. -/
private theorem cfXi_eq_floor_add_inv (x : ℝ) (_hx : Irrational x) (n : ℕ) :
    cfXi x (n + 1) = ↑⌊cfXi x (n + 1)⌋ + (cfXi x (n + 2))⁻¹ := by
  have h2 : cfXi x (n + 2) = (Int.fract (cfXi x (n + 1)))⁻¹ := cfXi_succ x (n + 1)
  have h1 := Int.floor_add_fract (cfXi x (n + 1))
  rw [h2, inv_inv]
  exact h1.symm

/-- Complete quotients commute with shifting past one step. -/
private theorem cfXi_shift (v : ℝ) (k : ℕ) :
    cfXi ((Int.fract v)⁻¹) k = cfXi v (k + 1) := by
  induction k with
  | zero => rw [cfXi_zero, cfXi_succ, cfXi_zero]
  | succ k ih => rw [cfXi_succ, cfXi_succ, ih]

/-- Complete quotients commute with shifting past `s` steps. -/
private theorem cfXi_shift_add (x : ℝ) (s m : ℕ) :
    cfXi (cfXi x s) m = cfXi x (m + s) := by
  induction s generalizing m with
  | zero => rw [cfXi_zero, Nat.add_zero]
  | succ s ih =>
    have e : cfXi x (s + 1) = (Int.fract (cfXi x s))⁻¹ := cfXi_succ x s
    rw [e, cfXi_shift, ih]
    congr 1
    omega

/-- Numerator convergents: `P 0 = 1`, `P 1 = ⌊x⌋`, `P (n+2) = ⌊ξ (n+1)⌋ P (n+1) + P n`. -/
private noncomputable def cfP (x : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => ⌊x⌋
  | (n + 2) => ⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n

/-- Denominator convergents: `Q 0 = 0`, `Q 1 = 1`, `Q (n+2) = ⌊ξ (n+1)⌋ Q (n+1) + Q n`. -/
private noncomputable def cfQ (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n

private theorem cfP_zero (x : ℝ) : cfP x 0 = 1 := rfl

private theorem cfP_one (x : ℝ) : cfP x 1 = ⌊x⌋ := rfl

private theorem cfP_add_two (x : ℝ) (n : ℕ) : cfP x (n + 2)
    = ⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n := rfl

private theorem cfQ_zero (x : ℝ) : cfQ x 0 = 0 := rfl

private theorem cfQ_one (x : ℝ) : cfQ x 1 = 1 := rfl

private theorem cfQ_add_two (x : ℝ) (n : ℕ) : cfQ x (n + 2)
    = ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n := rfl

/-- Denominators are nonnegative and at least one from index one on. -/
private theorem cfQ_nonneg_pos (x : ℝ) (hx : Irrational x) (n : ℕ) :
    0 ≤ cfQ x n ∧ 1 ≤ cfQ x (n + 1) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [cfQ_zero]
    · change (1 : ℤ) ≤ cfQ x 1
      rw [cfQ_one]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨zero_le_one.trans h2, ?_⟩
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e, cfQ_add_two x n]
    have ha1 := floor_cfXi_ge_one x hx n
    have hmul : (1 : ℤ) ≤ ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) :=
      one_le_mul_of_one_le_of_one_le ha1 h2
    linarith

/-- Numerators are at least one when the head coefficient is. -/
private theorem cfP_ge_one (x : ℝ) (hx : Irrational x) (h0 : 1 ≤ ⌊x⌋) (n : ℕ) :
    1 ≤ cfP x n := by
  induction n using Nat.twoStepInduction with
  | zero => rw [cfP_zero]
  | one => rw [cfP_one]; exact h0
  | more n ih1 ih2 =>
    rw [cfP_add_two]
    have ha := floor_cfXi_ge_one x hx n
    have hmul := one_le_mul_of_one_le_of_one_le ha ih2
    linarith [hmul, ih1]

/-- The Möbius identity: `x = (P (n+1) ξ (n+1) + P n) / (Q (n+1) ξ (n+1) + Q n)`. -/
private theorem cfMobius (x : ℝ) (hx : Irrational x) (n : ℕ) :
    x = ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
      / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
  induction n with
  | zero =>
    change x = ((cfP x 1 : ℝ) * cfXi x 1 + (cfP x 0 : ℝ))
      / ((cfQ x 1 : ℝ) * cfXi x 1 + (cfQ x 0 : ℝ))
    have hfx : Int.fract x ≠ 0 := by
      have h := fract_cfXi_ne x hx 0
      rwa [cfXi_zero] at h
    have hxi : cfXi x 1 = (Int.fract x)⁻¹ := cfXi_succ x 0
    rw [cfP_one, cfP_zero, cfQ_one, cfQ_zero, hxi]
    have h1 := Int.floor_add_fract x
    have hden : ((1 : ℤ) : ℝ) * (Int.fract x)⁻¹ + ((0 : ℤ) : ℝ) ≠ 0 := by
      have hne := inv_ne_zero hfx
      simpa using hne
    have hfinv : (Int.fract x)⁻¹ * Int.fract x = 1 := inv_mul_cancel₀ hfx
    rw [eq_div_iff hden]
    linear_combination hfinv - (Int.fract x)⁻¹ * h1
  | succ n ih =>
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e, cfP_add_two x n, cfQ_add_two x n]
    have hgt : (1 : ℝ) < cfXi x (n + 2) := one_lt_cfXi_succ x hx (n + 1)
    have ht : cfXi x (n + 2) ≠ 0 := by linarith
    have hs := cfXi_eq_floor_add_inv x hx n
    have hts : cfXi x (n + 2) * cfXi x (n + 1)
        = cfXi x (n + 2) * ↑⌊cfXi x (n + 1)⌋ + 1 := by
      conv_lhs => rw [hs]
      rw [mul_add, mul_inv_cancel₀ ht]
    have hnum : ((⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n : ℤ) : ℝ)
          * cfXi x (n + 2) + (cfP x (n + 1) : ℝ)
        = cfXi x (n + 2)
          * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) := by
      push_cast
      linear_combination -((cfP x (n + 1) : ℝ)) * hts
    have hden : ((⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n : ℤ) : ℝ)
          * cfXi x (n + 2) + (cfQ x (n + 1) : ℝ)
        = cfXi x (n + 2)
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
      push_cast
      linear_combination -((cfQ x (n + 1) : ℝ)) * hts
    rw [hnum, hden, mul_div_mul_left _ _ ht]
    exact ih

/-- The computation stream of an irrational lists its complete quotients. -/
private theorem stream_eq_cfXi (x : ℝ) (hx : Irrational x) (n : ℕ) :
    GenContFract.IntFractPair.stream x n
      = some ⟨⌊cfXi x n⌋, Int.fract (cfXi x n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hfr : Int.fract (cfXi x n) ≠ 0 := fract_cfXi_ne x hx n
    rw [GenContFract.IntFractPair.stream_succ_of_some ih hfr]
    change some (GenContFract.IntFractPair.of (Int.fract (cfXi x n))⁻¹)
      = some ⟨⌊cfXi x (n + 1)⌋, Int.fract (cfXi x (n + 1))⟩
    rw [← cfXi_succ x n]
    rfl

/-- A periodic stream has periodic complete-quotient floors. -/
private theorem floor_periodic (x : ℝ) (hx : Irrational x) (s : ℕ)
    (hper : ∀ n : ℕ, (GenContFract.IntFractPair.stream x (n + s)).map (·.b)
      = (GenContFract.IntFractPair.stream x n).map (·.b)) (n : ℕ) :
    ⌊cfXi x (n + s)⌋ = ⌊cfXi x n⌋ := by
  have h := hper n
  rw [stream_eq_cfXi x hx (n + s), stream_eq_cfXi x hx n] at h
  simpa using h

/-- Partial denominators of an irrational are shifted complete-quotient floors. -/
private theorem partDens_eq (v : ℝ) (hv : Irrational v) (i : ℕ) :
    (GenContFract.of v).partDens.get? i = some (((⌊cfXi v (i + 1)⌋ : ℤ) : ℝ)) := by
  have hs := stream_eq_cfXi v hv (i + 1)
  have hg := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hs
  change (Stream'.Seq.map GenContFract.Pair.b (GenContFract.of v).s).get? i = _
  rw [Stream'.Seq.map_get?, hg]
  rfl

/-- The conjugate `(P - √D) / Q` is irrational. -/
private theorem irr_conj (P Q D : ℤ) (hD : 0 < D) (hsq : ¬ IsSquare D) (hQ : 0 < Q) :
    Irrational (((P : ℝ) - √(D : ℝ)) / Q) := by
  have hsqrt : Irrational √(D : ℝ) :=
    (irrational_sqrt_intCast_iff_of_nonneg (le_of_lt hD)).mpr hsq
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  apply hsqrt
  refine ⟨(P : ℚ) - (Q : ℚ) * q, ?_⟩
  push_cast
  have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hQ
  have hx : ((P : ℝ) - √(D : ℝ)) / (Q : ℝ) = (q : ℝ) := hq.symm
  have hmul : (Q : ℝ) * (((P : ℝ) - √(D : ℝ)) / (Q : ℝ)) = (P : ℝ) - √(D : ℝ) := by
    rw [mul_comm ((Q : ℝ)), div_mul_cancel₀ _ hQne]
  have h2 : (Q : ℝ) * (q : ℝ) = (P : ℝ) - √(D : ℝ) := by
    rw [← hx]
    exact hmul
  linarith [h2]

/-- Powers `2 ^ (1 - k)` get arbitrarily small. -/
private theorem exists_zpow_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, (2 : ℝ) ^ (1 - (k : ℤ)) < ε := by
  have hNpow : ∀ N : ℕ, N ≤ 2 ^ N := by
    intro N
    induction N with
    | zero => decide
    | succ n ih =>
      have hpos : 0 < 2 ^ n := pow_pos (by decide) n
      have h2 : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ]; ring
      omega
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨N, ?_⟩
  have hN2 : ((N : ℕ) : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast hNpow N
  have h2ε : (2 : ℝ) < (N : ℝ) * ε := by
    have h := hN
    rw [div_lt_iff₀ hε] at h
    exact h
  rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast]
  rw [div_lt_iff₀ (pow_pos (by norm_num) N)]
  calc (2 : ℝ) < (N : ℝ) * ε := h2ε
    _ ≤ (2 : ℝ) ^ N * ε := mul_le_mul_of_nonneg_right hN2 (le_of_lt hε)
    _ = ε * (2 : ℝ) ^ N := by ring

/-- **The conjugate continued fraction is not purely periodic.** Let $P$, $Q$ and $D$ be integers
with $D > 0$ not a perfect square and $Q > 0$, and let $\bar\alpha = (P - \sqrt{D})/Q$. Then the
simple continued fraction $[a_0; a_1, a_2, \dots]$ of $\bar\alpha$, which is infinite because
$\bar\alpha$ is irrational, is not purely periodic: there is no integer $s \ge 1$ with
$a_{n+s} = a_n$ for all $n \ge 0$. Here $a_0 = \lfloor \bar\alpha \rfloor$ is included.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Lemma 3. -/
public theorem conjugate_continuedFraction_not_purelyPeriodic (P Q D : ℤ) (hD : 0 < D)
    (hsq : ¬ IsSquare D) (hQ : 0 < Q) :
    ¬ ∃ s : ℕ, 0 < s ∧ ∀ n : ℕ,
      (GenContFract.IntFractPair.stream (((P : ℝ) - √(D : ℝ)) / Q) (n + s)).map (·.b) =
        (GenContFract.IntFractPair.stream (((P : ℝ) - √(D : ℝ)) / Q) n).map (·.b) := by
  set x : ℝ := ((P : ℝ) - √(D : ℝ)) / Q with hx_def
  clear_value x
  have hirr : Irrational x := by
    rw [hx_def]
    exact irr_conj P Q D hD hsq hQ
  rintro ⟨s, hs, hper⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hs)
  have hfloor1 : 1 ≤ ⌊x⌋ := by
    have h := floor_periodic x hirr (t + 1) hper 0
    rw [Nat.zero_add, cfXi_zero] at h
    rw [← h]
    exact floor_cfXi_ge_one x hirr t
  have hfr0 : 0 < Int.fract x := by
    have h := fract_cfXi_pos x hirr 0
    rwa [cfXi_zero] at h
  have h1lt : 1 < x := by
    have hfloor := Int.floor_add_fract x
    have hle : (1 : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hfloor1
    linarith [hfloor, hfr0, hle]
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hsqrt_pos : 0 < √(D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hx1 := h1lt
  rw [hx_def, lt_div_iff₀ hQpos] at hx1
  have hPgt : √(D : ℝ) < (P : ℝ) := by linarith [hx1, hQpos]
  have hPsq : (D : ℝ) < (P : ℝ) ^ 2 := by
    have h1 : √(D : ℝ) ^ 2 < (P : ℝ) ^ 2 :=
      sq_lt_sq' (by linarith [hPgt, hsqrt_pos]) hPgt
    rwa [Real.sq_sqrt (by exact_mod_cast le_of_lt hD)] at h1
  have hPsqZ : D < P ^ 2 := by exact_mod_cast hPsq
  have h0 : (GenContFract.of x).h = (GenContFract.of (cfXi x (t + 1))).h := by
    rw [GenContFract.of_h_eq_floor, GenContFract.of_h_eq_floor]
    have h := floor_periodic x hirr (t + 1) hper 0
    rw [Nat.zero_add, cfXi_zero] at h
    exact_mod_cast h.symm
  have hk : ∀ k : ℕ, ∀ i < k, (GenContFract.of x).partDens.get? i
      = (GenContFract.of (cfXi x (t + 1))).partDens.get? i := by
    intro k i _
    rw [partDens_eq x hirr i, partDens_eq (cfXi x (t + 1)) (irr_cfXi x hirr (t + 1)) i,
      cfXi_shift_add]
    have hcast : ((⌊cfXi x (i + 1)⌋ : ℤ) : ℝ)
        = ((⌊cfXi x ((i + 1) + (t + 1))⌋ : ℤ) : ℝ) := by
      have h' : ⌊cfXi x (i + 1)⌋ = ⌊cfXi x ((i + 1) + (t + 1))⌋ :=
        (floor_periodic x hirr (t + 1) hper (i + 1)).symm
      exact_mod_cast h'
    rw [hcast]
  have huniq : cfXi x (t + 1) = x := by
    have hle : ∀ k : ℕ, |x - cfXi x (t + 1)| ≤ (2 : ℝ) ^ (1 - ((k : ℕ) : ℤ)) :=
      fun k => abs_sub_le_of_contFrac_prefix_eq x (cfXi x (t + 1)) k h0 (hk k)
    by_contra hne
    have hpos : 0 < |x - cfXi x (t + 1)| :=
      abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
    obtain ⟨k, hk'⟩ := exists_zpow_lt _ hpos
    linarith [hle k, hk']
  have hX : cfXi x (t + 1) = x := huniq
  have hmob := cfMobius x hirr t
  rw [hX] at hmob
  have hCpos : (0 : ℤ) < cfQ x (t + 1) :=
    lt_of_lt_of_le zero_lt_one (cfQ_nonneg_pos x hirr t).2
  have hDnonneg : (0 : ℤ) ≤ cfQ x t := (cfQ_nonneg_pos x hirr t).1
  have hBpos : (0 : ℤ) < cfP x t :=
    lt_of_lt_of_le zero_lt_one (cfP_ge_one x hirr hfloor1 t)
  have hden_pos : (0 : ℝ) < (cfQ x (t + 1) : ℝ) * x + (cfQ x t : ℝ) := by
    have h1 : (0 : ℝ) < (cfQ x (t + 1) : ℝ) := by exact_mod_cast hCpos
    have h2 : (0 : ℝ) ≤ (cfQ x t : ℝ) := by exact_mod_cast hDnonneg
    have h4 : (0 : ℝ) < (cfQ x (t + 1) : ℝ) * x := mul_pos h1 (lt_trans zero_lt_one h1lt)
    linarith [h4, h2]
  have hden_ne : (cfQ x (t + 1) : ℝ) * x + (cfQ x t : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hmul : x * ((cfQ x (t + 1) : ℝ) * x + (cfQ x t : ℝ))
      = (cfP x (t + 1) : ℝ) * x + (cfP x t : ℝ) := by
    have h := hmob
    rw [eq_div_iff hden_ne] at h
    exact h
  have hi : (Q : ℝ) ^ 2 * x ^ 2 + (-(2 * (P : ℝ) * (Q : ℝ))) * x
      + ((P : ℝ) ^ 2 - (D : ℝ)) = 0 := by
    have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hQ
    have hQx : (Q : ℝ) * x = (P : ℝ) - √(D : ℝ) := by
      rw [hx_def, mul_comm ((Q : ℝ)), div_mul_cancel₀ _ hQne]
    have hsq : ((Q : ℝ) * x - (P : ℝ)) ^ 2 = (D : ℝ) := by
      have h1 : (Q : ℝ) * x - (P : ℝ) = -√(D : ℝ) := by linarith [hQx]
      have h2 : √(D : ℝ) ^ 2 = (D : ℝ) :=
        Real.sq_sqrt (by exact_mod_cast le_of_lt hD)
      rw [h1]
      linear_combination h2
    linear_combination hsq
  have hii : (cfQ x (t + 1) : ℝ) * x ^ 2
      + ((cfQ x t : ℝ) - (cfP x (t + 1) : ℝ)) * x + (-(cfP x t : ℝ)) = 0 := by
    linear_combination hmul
  have hlin : ((cfQ x (t + 1) * (-(2 * P * Q)) - Q ^ 2 * (cfQ x t - cfP x (t + 1)) : ℤ) : ℝ)
        * x
      + ((cfQ x (t + 1) * (P ^ 2 - D) - Q ^ 2 * (-(cfP x t)) : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination (cfQ x (t + 1) : ℝ) * hi - (Q : ℝ) ^ 2 * hii
  by_cases hL : cfQ x (t + 1) * (-(2 * P * Q)) - Q ^ 2 * (cfQ x t - cfP x (t + 1)) = 0
  · have hM : cfQ x (t + 1) * (P ^ 2 - D) - Q ^ 2 * (-(cfP x t)) = 0 := by
      have h := hlin
      rw [hL, Int.cast_zero, zero_mul, zero_add] at h
      exact_mod_cast h
    have hQ2 : (0 : ℤ) < Q ^ 2 := by
      rw [pow_two]
      exact mul_pos hQ hQ
    have hprod : cfQ x (t + 1) * (P ^ 2 - D) < 0 := by
      have hQB : (0 : ℤ) < Q ^ 2 * cfP x t := mul_pos hQ2 hBpos
      have heq : cfQ x (t + 1) * (P ^ 2 - D) = -(Q ^ 2 * cfP x t) := by
        linear_combination hM
      rw [heq]
      linarith [hQB]
    have hPlt : P ^ 2 - D < 0 := by
      by_contra hcon
      push Not at hcon
      have hnn : (0 : ℤ) ≤ cfQ x (t + 1) * (P ^ 2 - D) :=
        mul_nonneg (le_of_lt hCpos) hcon
      linarith [hprod, hnn]
    omega
  · exfalso
    have hLne : ((cfQ x (t + 1) * (-(2 * P * Q))
        - Q ^ 2 * (cfQ x t - cfP x (t + 1)) : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast hL
    have hxfrac : x = ((-(cfQ x (t + 1) * (P ^ 2 - D) - Q ^ 2 * (-(cfP x t))) : ℤ) : ℝ)
        / ((cfQ x (t + 1) * (-(2 * P * Q)) - Q ^ 2 * (cfQ x t - cfP x (t + 1)) : ℤ) : ℝ) := by
      rw [eq_div_iff hLne]
      have hlin' := hlin
      push_cast at hlin' ⊢
      linear_combination hlin'
    exact (hirr.ne_rational _ _) hxfrac

end

end MetaMathlibExt
