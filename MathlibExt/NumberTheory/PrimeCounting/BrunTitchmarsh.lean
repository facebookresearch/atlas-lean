/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.PrimeCounting.ResidueClass
import MathlibExt.NumberTheory.PrimeCounting.WeightedLargeSieve
import MathlibExt.NumberTheory.PrimeCounting.ArithmeticLargeSieve
import MathlibExt.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Brun–Titchmarsh inequality

This file records the standard upper bound for primes in one residue class.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted

private theorem btLogSevenUpper :
    Real.log 7 < (8 * Real.log 2 + 4 * Real.log 3) / 5 := by
  have hpow : (7 : ℝ) ^ 5 < 2 ^ 8 * 3 ^ 4 := by norm_num
  have hlog : Real.log ((7 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8 * 3 ^ 4) :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog ⊢
  linarith

private noncomputable def btSieveFunction (α β v : ℝ) : ℝ :=
  (α + β / v) * Real.log v

private theorem btSieveFunction_hasDerivAt (α β v : ℝ) (hv : v ≠ 0) :
    HasDerivAt (btSieveFunction α β)
      ((α * v + β * (1 - Real.log v)) / v ^ 2) v := by
  have hdiv : HasDerivAt (fun w : ℝ => β / w) (-β / v ^ 2) v := by
    convert (hasDerivAt_const v β).div (hasDerivAt_id v) hv using 1
    · ext w
      rfl
    · simp
  have hleft : HasDerivAt (fun w : ℝ => α + β / w) (-β / v ^ 2) v := by
    convert (hasDerivAt_const v α).add hdiv using 1
    ring
  convert hleft.mul (Real.hasDerivAt_log hv) using 1
  · rfl
  · field_simp
    ring

private theorem btSieveFunction_twenty :
    btSieveFunction (1 / 4) (3 / 2) 20 < 1 := by
  have hlog : Real.log (20 : ℝ) = 2 * Real.log 2 + Real.log 5 := by
    rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [btSieveFunction, hlog]
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num at h2 h5 ⊢
  linarith

private theorem btSieveFunction_eighteen :
    btSieveFunction (1 / 6) 3 18 < 1 := by
  have hlog : Real.log (18 : ℝ) = Real.log 2 + 2 * Real.log 3 := by
    rw [show (18 : ℝ) = 2 * 3 ^ 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [btSieveFunction, hlog]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  norm_num at h2 h3 ⊢
  linarith

private theorem btSieveFunction_twoSeventy :
    btSieveFunction (1 / 6) 3 270 < 1 := by
  have hlog : Real.log (270 : ℝ) =
      Real.log 2 + 3 * Real.log 3 + Real.log 5 := by
    rw [show (270 : ℝ) = (2 * 3 ^ 3) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [btSieveFunction, hlog]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num at h2 h3 h5 ⊢
  linarith

private theorem btSieveFunction_fortyTwo :
    btSieveFunction (2 / 15) (11 / 2) 42 < 1 := by
  have hlog : Real.log (42 : ℝ) =
      Real.log 2 + Real.log 3 + Real.log 7 := by
    rw [show (42 : ℝ) = (2 * 3) * 7 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [btSieveFunction, hlog]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h7 := btLogSevenUpper
  norm_num at h2 h3 h7 ⊢
  linarith

private theorem btSieveFunction_thousand :
    btSieveFunction (2 / 15) (11 / 2) 1000 < 1 := by
  have hlog : Real.log (1000 : ℝ) =
      3 * (Real.log 2 + Real.log 5) := by
    rw [show (1000 : ℝ) = (2 * 5) ^ 3 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [btSieveFunction, hlog]
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num at h2 h5 ⊢
  linarith

private theorem btSieveFunction_sevenHundred :
    btSieveFunction (96 / 1001) 35 700 < 1 := by
  have hlog : Real.log (700 : ℝ) =
      Real.log 7 + 2 * (Real.log 2 + Real.log 5) := by
    rw [show (700 : ℝ) = 7 * (2 * 5) ^ 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [btSieveFunction, hlog]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_lt_d9
  have h7 := btLogSevenUpper
  norm_num at h2 h3 h5 h7 ⊢
  linarith

private theorem btSieveFunction_twentyThousand :
    btSieveFunction (96 / 1001) 35 20000 < 1 := by
  have hlog : Real.log (20000 : ℝ) =
      5 * Real.log 2 + 4 * Real.log 5 := by
    rw [show (20000 : ℝ) = 2 ^ 5 * 5 ^ 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [btSieveFunction, hlog]
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num at h2 h5 ⊢
  linarith

private theorem btSieveDerivNumerator_mono {α β x y : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hx : β / α ≤ x) (hxy : x ≤ y) :
    α * x + β * (1 - Real.log x) ≤
      α * y + β * (1 - Real.log y) := by
  have hxpos : 0 < x := lt_of_lt_of_le (div_pos hβ hα) hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hlog := Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
  rw [Real.log_div hypos.ne' hxpos.ne'] at hlog
  have hβα : β ≤ α * x := by
    rw [div_le_iff₀ hα] at hx
    nlinarith
  have hscaled : β * (Real.log y - Real.log x) ≤ α * (y - x) := by
    have hfirst : β * (Real.log y - Real.log x) ≤ β * (y / x - 1) := by
      nlinarith
    have hsecond : β * (y / x - 1) ≤ α * (y - x) := by
      rw [show y / x - 1 = (y - x) / x by field_simp]
      rw [show β * ((y - x) / x) = β * (y - x) / x by ring]
      rw [div_le_iff₀ hxpos]
      nlinarith
    exact hfirst.trans hsecond
  linarith

private theorem btSieveFunction_le_max_endpoints {α β L U v : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hturn : β / α ≤ L)
    (hLv : L ≤ v) (hvU : v ≤ U) :
    btSieveFunction α β v ≤
      max (btSieveFunction α β L) (btSieveFunction α β U) := by
  have hLpos : 0 < L := lt_of_lt_of_le (div_pos hβ hα) hturn
  have hvpos : 0 < v := hLpos.trans_le hLv
  by_cases hsign : α * v + β * (1 - Real.log v) ≤ 0
  · have hanti : AntitoneOn (btSieveFunction α β) (Set.Icc L v) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc L v)
      · intro x hx
        exact (btSieveFunction_hasDerivAt α β x
          (ne_of_gt (hLpos.trans_le hx.1))).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (btSieveFunction_hasDerivAt α β x
          (ne_of_gt (hLpos.trans_le hx'.1))).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        have hnum := btSieveDerivNumerator_mono hα hβ (hturn.trans hx'.1) hx'.2
        have hderiv := (btSieveFunction_hasDerivAt α β x
          (ne_of_gt (hLpos.trans_le hx'.1))).deriv
        rw [hderiv]
        exact div_nonpos_of_nonpos_of_nonneg (hnum.trans hsign) (sq_nonneg x)
    exact (hanti ⟨le_rfl, hLv⟩ ⟨hLv, le_rfl⟩ hLv).trans (le_max_left _ _)
  · have hsign' : 0 ≤ α * v + β * (1 - Real.log v) := le_of_not_ge hsign
    have hmono : MonotoneOn (btSieveFunction α β) (Set.Icc v U) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc v U)
      · intro x hx
        exact (btSieveFunction_hasDerivAt α β x
          (ne_of_gt (hvpos.trans_le hx.1))).continuousAt.continuousWithinAt
      · intro x hx
        have hx' := interior_subset hx
        exact (btSieveFunction_hasDerivAt α β x
          (ne_of_gt (hvpos.trans_le hx'.1))).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        have hnum := btSieveDerivNumerator_mono hα hβ (hturn.trans hLv) hx'.1
        have hderiv := (btSieveFunction_hasDerivAt α β x
          (ne_of_gt (hvpos.trans_le hx'.1))).deriv
        rw [hderiv]
        exact div_nonneg (hsign'.trans hnum) (sq_nonneg x)
    exact (hmono ⟨le_rfl, hvU⟩ ⟨hvU, le_rfl⟩ hvU).trans (le_max_right _ _)

private theorem btFirstDerivNumerator_pos {v : ℝ} (hv : 0 < v) :
    0 < (1 / 4 : ℝ) * v + (3 / 2) * (1 - Real.log v) := by
  have hlog6 : Real.log (6 : ℝ) < 2 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    have h2 := Real.log_two_lt_d9
    have h3 := Real.log_three_lt_d9
    norm_num at h2 h3 ⊢
    linarith
  have hratio :=
    Real.log_le_sub_one_of_pos (div_pos hv (by norm_num : (0 : ℝ) < 6))
  rw [Real.log_div hv.ne' (by norm_num)] at hratio
  norm_num at hratio ⊢
  linarith

private theorem btSieveFunction_firstRange {v : ℝ} (hv : 1 < v) (hv20 : v ≤ 20) :
    btSieveFunction (1 / 4) (3 / 2) v < 1 := by
  have hmono : MonotoneOn (btSieveFunction (1 / 4) (3 / 2)) (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro x hx
      exact (btSieveFunction_hasDerivAt (1 / 4) (3 / 2) x
        (ne_of_gt (zero_lt_one.trans_le hx))).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (btSieveFunction_hasDerivAt (1 / 4) (3 / 2) x
        (ne_of_gt (zero_lt_one.trans_le hx'))).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have hxpos : 0 < x := zero_lt_one.trans_le hx'
      have hderiv :=
        (btSieveFunction_hasDerivAt (1 / 4) (3 / 2) x hxpos.ne').deriv
      rw [hderiv]
      exact div_nonneg (btFirstDerivNumerator_pos hxpos).le (sq_nonneg x)
  exact (hmono hv.le (by norm_num) hv20).trans_lt btSieveFunction_twenty

private theorem btSieveFunction_secondRange {v : ℝ} (h18v : 18 ≤ v) (hv270 : v ≤ 270) :
    btSieveFunction (1 / 6) 3 v < 1 := by
  have hmax := btSieveFunction_le_max_endpoints
    (α := (1 / 6 : ℝ)) (β := 3) (L := 18) (U := 270) (v := v)
    (by norm_num) (by norm_num) (by norm_num) h18v hv270
  exact hmax.trans_lt (max_lt btSieveFunction_eighteen btSieveFunction_twoSeventy)

private theorem btSieveFunction_thirdRange {v : ℝ} (h42v : 42 ≤ v) (hv1000 : v ≤ 1000) :
    btSieveFunction (2 / 15) (11 / 2) v < 1 := by
  have hmax := btSieveFunction_le_max_endpoints
    (α := (2 / 15 : ℝ)) (β := (11 / 2 : ℝ)) (L := 42) (U := 1000) (v := v)
    (by norm_num) (by norm_num) (by norm_num) h42v hv1000
  exact hmax.trans_lt (max_lt btSieveFunction_fortyTwo btSieveFunction_thousand)

private theorem btSieveFunction_fourthRange {v : ℝ}
    (h700v : 700 ≤ v) (hv20000 : v ≤ 20000) :
    btSieveFunction (96 / 1001) 35 v < 1 := by
  have hmax := btSieveFunction_le_max_endpoints
    (α := (96 / 1001 : ℝ)) (β := 35) (L := 700) (U := 20000) (v := v)
    (by norm_num) (by norm_num) (by norm_num) h700v hv20000
  exact hmax.trans_lt
    (max_lt btSieveFunction_sevenHundred btSieveFunction_twentyThousand)

private theorem btSieveFunction_smallRange (v : ℝ) (hv : 1 < v) (hv20000 : v ≤ 20000) :
    btSieveFunction (1 / 4) (3 / 2) v < 1 ∨
      btSieveFunction (1 / 6) 3 v < 1 ∨
      btSieveFunction (2 / 15) (11 / 2) v < 1 ∨
      btSieveFunction (96 / 1001) 35 v < 1 := by
  by_cases hv20 : v ≤ 20
  · exact Or.inl (btSieveFunction_firstRange hv hv20)
  by_cases hv270 : v ≤ 270
  · exact Or.inr (Or.inl (btSieveFunction_secondRange (by linarith) hv270))
  by_cases hv1000 : v ≤ 1000
  · exact Or.inr (Or.inr (Or.inl
      (btSieveFunction_thirdRange (by linarith) hv1000)))
  exact Or.inr (Or.inr (Or.inr
    (btSieveFunction_fourthRange (by linarith) hv20000)))

private theorem btSumMoebiusDivisors (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

private theorem btDivisorsGcd (P n : ℕ) (hP : P ≠ 0) :
    (Nat.gcd P n).divisors = P.divisors.filter (· ∣ n) := by
  have hg : Nat.gcd P n ≠ 0 :=
    (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hP)).ne'
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hd, -⟩
    exact ⟨⟨(Nat.dvd_gcd_iff.mp hd).1, hP⟩, (Nat.dvd_gcd_iff.mp hd).2⟩
  · rintro ⟨⟨hdP, -⟩, hdn⟩
    exact ⟨Nat.dvd_gcd hdP hdn, hg⟩

private theorem btMobiusCoprimeIndicator (P n : ℕ) (hP : P ≠ 0) :
    (∑ d ∈ P.divisors,
      if d ∣ n then ArithmeticFunction.moebius d else 0) =
      if Nat.Coprime P n then 1 else 0 := by
  rw [← Finset.sum_filter, ← btDivisorsGcd P n hP]
  rw [btSumMoebiusDivisors]

private theorem btCountModEq_le (X m a : ℕ) (hm : 0 < m) :
    (X + 1).count (· ≡ a [MOD m]) ≤ X / m + 1 := by
  rw [Nat.count_modEq_card (X + 1) hm a, Nat.succ_div]
  by_cases hd : m ∣ X + 1
  · have hmod : (X + 1) % m = 0 := Nat.mod_eq_zero_of_dvd hd
    simp [hd, hmod]
  · simp [hd]
    split <;> omega

private theorem btCardRangeModEq_le (X m a : ℕ) (hm : 0 < m) :
    (((Finset.range (X + 1)).filter (· ≡ a [MOD m])).card : ℝ) ≤
      (X : ℝ) / m + 1 := by
  have hnat := btCountModEq_le X m a hm
  rw [Nat.count_eq_card_filter_range] at hnat
  calc
    (((Finset.range (X + 1)).filter (· ≡ a [MOD m])).card : ℝ) ≤
        ((X / m + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((X / m : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ (X : ℝ) / m + 1 := by
      simpa only [add_comm] using
        (add_le_add_right (Nat.cast_div_le (α := ℝ) (m := X) (n := m)) 1)

private theorem btCardRangeModSubDivAbsLe (N m b : ℕ)
    (hm : 0 < m) (hb : b < m) :
    |(((Finset.range N).filter (fun n ↦ n % m = b)).card : ℝ) - (N : ℝ) / m| ≤ 1 := by
  have hcount := Nat.count_modEq_card N hm b
  have hmod : b % m = b := Nat.mod_eq_of_lt hb
  have hcard : Nat.count (fun n ↦ n ≡ b [MOD m]) N =
      ((Finset.range N).filter (fun n ↦ n % m = b)).card := by
    rw [Nat.count_eq_card_filter_range]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hnb⟩
      exact ⟨hn, by simpa only [Nat.ModEq, hmod] using hnb⟩
    · rintro ⟨hn, hnb⟩
      exact ⟨hn, by simpa only [Nat.ModEq, hmod] using hnb⟩
  rw [hcard, hmod] at hcount
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdecomp : (N : ℝ) = m * (N / m : ℕ) + (N % m : ℕ) := by
    have h := Nat.div_add_mod N m
    exact_mod_cast h.symm
  have hlt : ((N % m : ℕ) : ℝ) < m := by
    exact_mod_cast Nat.mod_lt N hm
  have hdiv : (N : ℝ) / m = (N / m : ℕ) + (N % m : ℕ) / (m : ℝ) := by
    field_simp
    linarith
  have hfracNonneg : (0 : ℝ) ≤ (N % m : ℕ) / (m : ℝ) := by positivity
  have hfracLeOne : ((N % m : ℕ) : ℝ) / m ≤ 1 := by
    rw [div_le_one hmR]
    exact hlt.le
  by_cases hif : b < N % m
  · simp only [hif, ite_true] at hcount
    have hcast : ((((Finset.range N).filter (fun n ↦ n % m = b)).card : ℕ) : ℝ) =
        (N / m : ℕ) + 1 := by exact_mod_cast hcount
    rw [hcast, hdiv]
    rw [show ((N / m : ℕ) : ℝ) + 1 -
      ((N / m : ℕ) + (N % m : ℕ) / (m : ℝ)) =
        1 - (N % m : ℕ) / (m : ℝ) by ring]
    rw [abs_sub_le_iff]
    constructor <;> linarith
  · simp only [hif, ite_false] at hcount
    have hcast : ((((Finset.range N).filter (fun n ↦ n % m = b)).card : ℕ) : ℝ) =
        (N / m : ℕ) := by exact_mod_cast hcount
    rw [hcast, hdiv]
    rw [show ((N / m : ℕ) : ℝ) -
      ((N / m : ℕ) + (N % m : ℕ) / (m : ℝ)) =
        -((N % m : ℕ) / (m : ℝ)) by ring, abs_neg,
      abs_of_nonneg hfracNonneg]
    exact hfracLeOne

private theorem btModEq_succ_iff (m c n : ℕ) (hm : 0 < m) :
    n + 1 ≡ c [MOD m] ↔ n ≡ (c + m - 1) % m [MOD m] := by
  have hshift : n + 1 ≡ c [MOD m] ↔ n ≡ c + m - 1 [MOD m] := by
    constructor
    · intro h
      have h' := h.add_right (m - 1)
      have h'' : n + m ≡ c + m - 1 [MOD m] := by
        convert h' using 1
        · omega
        · omega
      exact Nat.add_modEq_right.symm.trans h''
    · intro h
      have h' := h.add_right 1
      have h'' : n + 1 ≡ c + m [MOD m] := by
        convert h' using 1
        omega
      exact h''.trans Nat.add_modEq_right
  rw [hshift]
  simp only [Nat.ModEq, Nat.mod_mod]

private theorem btCardIocModEq_eq_rangeShift (X m c : ℕ) (hm : 0 < m) :
    ((Finset.Ioc 0 X).filter (· ≡ c [MOD m])).card =
      ((Finset.range X).filter (· ≡ (c + m - 1) % m [MOD m])).card := by
  let b := (c + m - 1) % m
  apply Finset.card_bij (fun n _ ↦ n - 1)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hn ⊢
    refine ⟨by omega, ?_⟩
    have hnSucc : n - 1 + 1 = n := by omega
    rw [← hnSucc] at hn
    exact (btModEq_succ_iff m c (n - 1) hm).mp hn.2
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn₁ hn₂
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨n + 1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨by omega, (btModEq_succ_iff m c n hm).mpr hn.2⟩
    · omega

private theorem btCardIocModSubDivAbsLe (X m c : ℕ) (hm : 0 < m) :
    |(((Finset.Ioc 0 X).filter (· ≡ c [MOD m])).card : ℝ) - (X : ℝ) / m| ≤ 1 := by
  let b := (c + m - 1) % m
  have hb : b < m := Nat.mod_lt _ hm
  have hcard := btCardIocModEq_eq_rangeShift X m c hm
  have hfilter :
      (Finset.range X).filter (· ≡ b [MOD m]) =
        (Finset.range X).filter (fun n ↦ n % m = b) := by
    ext n
    simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hb]
  rw [hcard, hfilter]
  exact btCardRangeModSubDivAbsLe X m b hm hb

private theorem btCardIocModEqDvdSubDivAbsLe (X q a d : ℕ)
    (hq : 0 < q) (hd : 0 < d) (hcop : d.Coprime q) :
    |(((Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q] ∧ d ∣ n)).card : ℝ) -
        (X : ℝ) / (d * q)| ≤ 1 := by
  let c := Nat.chineseRemainder hcop 0 a
  have hcd : c ≡ 0 [MOD d] := c.prop.1
  have hcq : c ≡ a [MOD q] := c.prop.2
  have hfilter :
      (Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q] ∧ d ∣ n) =
        (Finset.Ioc 0 X).filter (· ≡ (c : ℕ) [MOD d * q]) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hn, hnq, hdn⟩
      refine ⟨hn, ?_⟩
      have hnd : n ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hdn
      change n ≡ c [MOD d * q]
      exact Nat.chineseRemainder_modEq_unique hcop hnd hnq
    · rintro ⟨hn, hnc⟩
      refine ⟨hn, ?_, ?_⟩
      · have hncq : n ≡ c [MOD q] := hnc.of_dvd ⟨d, by simp [mul_comm]⟩
        exact hncq.trans hcq
      · have hncd : n ≡ c [MOD d] := hnc.of_dvd ⟨q, rfl⟩
        exact Nat.modEq_zero_iff_dvd.mp (hncd.trans hcd)
  rw [hfilter]
  simpa only [Nat.cast_mul] using
    btCardIocModSubDivAbsLe X (d * q) c (Nat.mul_pos hd hq)

private noncomputable def btInvNat : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp only [Nat.cast_mul, mul_inv]

private noncomputable def btInv : ArithmeticFunction ℝ :=
  ⟨btInvNat, by simp [btInvNat]⟩

@[simp] private theorem btInv_apply (n : ℕ) : btInv n = (n : ℝ)⁻¹ := rfl

private theorem btInv_mult : btInv.IsMultiplicative := by
  constructor
  · simp
  · intro m n _
    simp only [btInv_apply, Nat.cast_mul, mul_inv]

private theorem btMobiusDivisorMain {P : ℕ} (hP : Squarefree P) :
    (∑ d ∈ P.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d) =
      ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    btInv btInv_mult hP
  symm
  simpa only [btInv_apply, div_eq_mul_inv, one_mul] using h

private theorem btCardDivisorsOfSquarefree {P : ℕ} (hP0 : P ≠ 0)
    (hP : Squarefree P) : P.divisors.card = 2 ^ P.primeFactors.card := by
  rw [Nat.card_divisors hP0]
  have hfactor : ∀ p ∈ P.primeFactors, P.factorization p + 1 = 2 := by
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hP
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
  calc
    (∏ p ∈ P.primeFactors, (P.factorization p + 1)) =
        ∏ _p ∈ P.primeFactors, 2 := Finset.prod_congr rfl hfactor
    _ = 2 ^ P.primeFactors.card := Finset.prod_const 2

private theorem btSiftedCardEqMobiusSum (X q a P : ℕ) (hP0 : P ≠ 0) :
    ((((Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q])).filter
        (Nat.Coprime P)).card : ℝ) =
      ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (((Finset.Ioc 0 X).filter
          (fun n ↦ n ≡ a [MOD q] ∧ d ∣ n)).card : ℝ) := by
  let A := (Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q])
  calc
    (((A.filter (Nat.Coprime P)).card : ℕ) : ℝ) =
        ∑ n ∈ A, if Nat.Coprime P n then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole]
    _ = ∑ n ∈ A, ∑ d ∈ P.divisors,
        if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      have h := btMobiusCoprimeIndicator P n hP0
      exact_mod_cast h.symm
    _ = ∑ d ∈ P.divisors, ∑ n ∈ A,
        if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ((A.filter (fun n ↦ d ∣ n)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (((Finset.Ioc 0 X).filter
          (fun n ↦ n ≡ a [MOD q] ∧ d ∣ n)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro d _
      have hfilter : A.filter (fun n ↦ d ∣ n) =
          (Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q] ∧ d ∣ n) := by
        ext n
        simp only [A, Finset.mem_filter]
        tauto
      rw [hfilter]

private theorem btEratosthenesSiftedBound (X q a P : ℕ) (hq : 0 < q)
    (hP0 : P ≠ 0) (hPq : P.Coprime q) (hPsq : Squarefree P) :
    ((((Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q])).filter
        (Nat.Coprime P)).card : ℝ) ≤
      (X : ℝ) / q * ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ)) +
        (2 : ℝ) ^ P.primeFactors.card := by
  let C : ℕ → ℝ := fun d ↦
    (((Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q] ∧ d ∣ n)).card : ℝ)
  let r : ℕ → ℝ := fun d ↦ C d - (X : ℝ) / (d * q)
  have hrem : ∀ d ∈ P.divisors, |r d| ≤ 1 := by
    intro d hdP
    have hdP' := (Nat.mem_divisors.mp hdP).1
    have hd0 : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hdP')
    have hdq : d.Coprime q := hPq.of_dvd_left hdP'
    exact btCardIocModEqDvdSubDivAbsLe X q a d hq hd0 hdq
  have hdecomp :
      (∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * C d) =
        (X : ℝ) / q *
            (∑ d ∈ P.divisors,
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d) +
          ∑ d ∈ P.divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * r d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hdP
    have hdP' := (Nat.mem_divisors.mp hdP).1
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hP0 hdP'
    have hq0 : q ≠ 0 := hq.ne'
    dsimp only [r]
    field_simp [hd0, hq0]
    ring
  have herr :
      (∑ d ∈ P.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * r d) ≤
          (P.divisors.card : ℝ) := by
    calc
      (∑ d ∈ P.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * r d) ≤
          |∑ d ∈ P.divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * r d| := le_abs_self _
      _ ≤ ∑ d ∈ P.divisors,
          |((ArithmeticFunction.moebius d : ℤ) : ℝ) * r d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ P.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hdP
        have hr := hrem d hdP
        rcases ArithmeticFunction.moebius_eq_or d with hmu | hmu | hmu
        · simp [hmu]
        · simpa [hmu] using hr
        · simpa [hmu] using hr
      _ = (P.divisors.card : ℝ) := by simp
  have hcard := btSiftedCardEqMobiusSum X q a P hP0
  change _ = ∑ d ∈ P.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * C d at hcard
  rw [hcard, hdecomp, btMobiusDivisorMain hPsq]
  calc
    (X : ℝ) / q * ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ)) +
        ∑ d ∈ P.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * r d ≤
      (X : ℝ) / q * ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ)) +
        (P.divisors.card : ℝ) := add_le_add (le_refl _) herr
    _ = (X : ℝ) / q * ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ)) +
        (2 : ℝ) ^ P.primeFactors.card := by
      rw [btCardDivisorsOfSquarefree hP0 hPsq]
      norm_num

private def btPrimes (z q : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter fun p ↦ p.Prime ∧ ¬p ∣ q

private def btPrimeProduct (z q : ℕ) : ℕ :=
  ∏ p ∈ btPrimes z q, p

private theorem btPrimes_eq_filter (z q : ℕ) :
    btPrimes z q = z.primesLE.filter (fun p ↦ ¬p ∣ q) := by
  ext p
  simp only [btPrimes, Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE,
    Nat.lt_succ_iff]
  tauto

private theorem btPrimeProduct_squarefree (z q : ℕ) :
    Squarefree (btPrimeProduct z q) := by
  unfold btPrimeProduct btPrimes
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp r hr hpr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hr
    exact (Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hp.2.1 hr.2.1).mpr hpr))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1.prime.squarefree

private theorem btPrimeProduct_ne_zero (z q : ℕ) : btPrimeProduct z q ≠ 0 := by
  unfold btPrimeProduct
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  simp only [btPrimes, Finset.mem_filter, Finset.mem_range] at hp
  exact hp.2.1.ne_zero

private theorem btPrime_dvd_product (z q p : ℕ) (hp : p.Prime) :
    p ∣ btPrimeProduct z q ↔ p ≤ z ∧ ¬p ∣ q := by
  constructor
  · intro hdiv
    rw [btPrimeProduct, Prime.dvd_finsetProd_iff hp.prime] at hdiv
    obtain ⟨r, hr, hpr⟩ := hdiv
    simp only [btPrimes, Finset.mem_filter, Finset.mem_range] at hr
    have hpr' : p = r := (Nat.prime_dvd_prime_iff_eq hp hr.2.1).mp hpr
    subst r
    exact ⟨Nat.lt_succ_iff.mp hr.1, hr.2.2⟩
  · rintro ⟨hpz, hpq⟩
    unfold btPrimeProduct
    apply Finset.dvd_prod_of_mem
    simp only [btPrimes, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr hpz, hp, hpq⟩

private theorem btPrimeProduct_coprime (z q : ℕ) : (btPrimeProduct z q).Coprime q := by
  apply Nat.coprime_of_dvd
  intro p hp hpP hpq
  exact (btPrime_dvd_product z q p hp).mp hpP |>.2 hpq

private theorem btPrimeFactors_product (z q : ℕ) :
    (btPrimeProduct z q).primeFactors = btPrimes z q := by
  ext p
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpP, -⟩
    exact (btPrime_dvd_product z q p hp).mp hpP |>
      fun h ↦ by
        simp only [btPrimes, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_iff.mpr h.1, hp, h.2⟩
  · intro hp
    simp only [btPrimes, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.2.1, (btPrime_dvd_product z q p hp.2.1).mpr
      ⟨Nat.lt_succ_iff.mp hp.1, hp.2.2⟩, btPrimeProduct_ne_zero z q⟩

private theorem btPrimeCount_le_small_add_sifted (X q a z : ℕ) :
    (Nat.primeCountingMod X q a : ℝ) ≤ (Nat.primeCounting z : ℝ) +
      ((((Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q])).filter
        (Nat.Coprime (btPrimeProduct z q))).card : ℝ) := by
  let T := (Finset.range (X + 1)).filter fun p ↦ p.Prime ∧ p ≡ a [MOD q]
  have hTcard : T.card = Nat.primeCountingMod X q a := by
    simpa only [T] using (Nat.primeCountingMod_eq_card_filter_range X q a).symm
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun p ↦ p ≤ z)
  have hsmall : ((T.filter fun p ↦ p ≤ z).card : ℝ) ≤ Nat.primeCounting z := by
    have hsub : T.filter (fun p ↦ p ≤ z) ⊆ z.primesLE := by
      intro p hp
      simp only [T, Finset.mem_filter, Finset.mem_range] at hp
      exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.2.1⟩
    calc
      ((T.filter fun p ↦ p ≤ z).card : ℝ) ≤ (z.primesLE.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = Nat.primeCounting z := by rw [Nat.primesLE_card_eq_primeCounting]
  have hlargeSub : T.filter (fun p ↦ ¬p ≤ z) ⊆
      ((Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q])).filter
        (Nat.Coprime (btPrimeProduct z q)) := by
    intro p hp
    simp only [T, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp ⊢
    refine ⟨⟨⟨hp.1.2.1.pos, Nat.lt_succ_iff.mp hp.1.1⟩, hp.1.2.2⟩, ?_⟩
    apply Nat.coprime_of_dvd
    intro r hr hrP hrp
    have hrz := (btPrime_dvd_product z q r hr).mp hrP |>.1
    have hrpEq := (Nat.prime_dvd_prime_iff_eq hr hp.1.2.1).mp hrp
    omega
  have hlarge : ((T.filter fun p ↦ ¬p ≤ z).card : ℝ) ≤
      ((((Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q])).filter
        (Nat.Coprime (btPrimeProduct z q))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hlargeSub
  have hcast : ((T.filter (fun p ↦ p ≤ z)).card : ℝ) +
      ((T.filter fun p ↦ ¬p ≤ z).card : ℝ) = T.card := by
    exact_mod_cast hsplit
  rw [hTcard] at hcast
  linarith

private theorem btEratosthenesBound (X q a z : ℕ) (hq : 0 < q) :
    (Nat.primeCountingMod X q a : ℝ) ≤
      (X : ℝ) / q * ∏ p ∈ btPrimes z q, (1 - 1 / (p : ℝ)) +
        (2 : ℝ) ^ Nat.primeCounting z + Nat.primeCounting z := by
  have hsmall := btPrimeCount_le_small_add_sifted X q a z
  have hsift := btEratosthenesSiftedBound X q a (btPrimeProduct z q) hq
    (btPrimeProduct_ne_zero z q) (btPrimeProduct_coprime z q)
    (btPrimeProduct_squarefree z q)
  rw [btPrimeFactors_product] at hsift
  have hcard : (btPrimes z q).card ≤ Nat.primeCounting z := by
    have hsub : btPrimes z q ⊆ z.primesLE := by
      intro p hp
      simp only [btPrimes, Finset.mem_filter, Finset.mem_range] at hp
      exact Nat.mem_primesLE.mpr ⟨Nat.lt_succ_iff.mp hp.1, hp.2.1⟩
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card hsub
  have hpow : (2 : ℝ) ^ (btPrimes z q).card ≤
      (2 : ℝ) ^ Nat.primeCounting z :=
    pow_le_pow_right₀ (by norm_num) hcard
  calc
    (Nat.primeCountingMod X q a : ℝ) ≤ Nat.primeCounting z +
        ((((Finset.Ioc 0 X).filter (fun n ↦ n ≡ a [MOD q])).filter
          (Nat.Coprime (btPrimeProduct z q))).card : ℝ) := hsmall
    _ ≤ Nat.primeCounting z +
        ((X : ℝ) / q * ∏ p ∈ btPrimes z q, (1 - 1 / (p : ℝ)) +
          (2 : ℝ) ^ (btPrimes z q).card) := add_le_add (le_refl _) hsift
    _ ≤ Nat.primeCounting z +
        ((X : ℝ) / q * ∏ p ∈ btPrimes z q, (1 - 1 / (p : ℝ)) +
          (2 : ℝ) ^ Nat.primeCounting z) := by gcongr
    _ = (X : ℝ) / q * ∏ p ∈ btPrimes z q, (1 - 1 / (p : ℝ)) +
        (2 : ℝ) ^ Nat.primeCounting z + Nat.primeCounting z := by ring

private theorem btTotientMulSieveProduct_le (q z : ℕ) (hq : 0 < q) :
    (Nat.totient q : ℝ) / q *
        ∏ p ∈ btPrimes z q, (1 - 1 / (p : ℝ)) ≤
      ∏ p ∈ z.primesLE, (1 - 1 / (p : ℝ)) := by
  let D := z.primesLE.filter (fun p ↦ p ∣ q)
  let f : ℕ → ℝ := fun p ↦ 1 - 1 / (p : ℝ)
  have hfNonneg : ∀ p ∈ q.primeFactors, 0 ≤ f p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hinv : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast hp'.one_lt)
    dsimp only [f]
    rw [one_div]
    linarith
  have hfLeOne : ∀ p ∈ q.primeFactors, f p ≤ 1 := by
    intro p _
    have hinv : 0 ≤ (p : ℝ)⁻¹ := by positivity
    dsimp only [f]
    rw [one_div]
    linarith
  have hDsub : D ⊆ q.primeFactors := by
    intro p hp
    simp only [D, Finset.mem_filter, Nat.mem_primesLE] at hp
    exact Nat.mem_primeFactors.mpr ⟨hp.1.2, hp.2, hq.ne'⟩
  have hprodQ : (∏ p ∈ q.primeFactors, f p) ≤ ∏ p ∈ D, f p :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hDsub hfNonneg
      (fun p hp _ ↦ hfLeOne p hp)
  have hawayNonneg : 0 ≤ ∏ p ∈ btPrimes z q, f p := by
    apply Finset.prod_nonneg
    intro p hp
    simp only [btPrimes, Finset.mem_filter, Finset.mem_range] at hp
    have hinv : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.2.1.one_lt)
    dsimp only [f]
    rw [one_div]
    linarith
  have htot : (Nat.totient q : ℝ) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, f p := by
    have htotQ := Nat.totient_eq_mul_prod_factors q
    have htotR := congrArg (fun x : ℚ ↦ (x : ℝ)) htotQ
    simpa [f] using htotR
  have hratio : (Nat.totient q : ℝ) / q = ∏ p ∈ q.primeFactors, f p := by
    rw [htot]
    field_simp [hq.ne']
  rw [hratio]
  calc
    (∏ p ∈ q.primeFactors, f p) * ∏ p ∈ btPrimes z q, f p ≤
        (∏ p ∈ D, f p) * ∏ p ∈ btPrimes z q, f p :=
      mul_le_mul_of_nonneg_right hprodQ hawayNonneg
    _ = ∏ p ∈ z.primesLE, f p := by
      rw [btPrimes_eq_filter]
      exact Finset.prod_filter_mul_prod_filter_not z.primesLE (fun p ↦ p ∣ q) f

private theorem btSmallRangeFromSieve (X q a z : ℕ) (α β : ℝ)
    (hq : 0 < q) (hqX : q < X)
    (hprod : (∏ p ∈ z.primesLE, (1 - 1 / (p : ℝ))) = 2 * α)
    (herr : (2 : ℝ) ^ Nat.primeCounting z + Nat.primeCounting z = 2 * β)
    (hf : btSieveFunction α β ((X : ℝ) / q) < 1) :
    (Nat.primeCountingMod X q a : ℝ) ≤
      2 * (X : ℝ) /
        ((Nat.totient q : ℝ) * Real.log ((X : ℝ) / q)) := by
  let v := (X : ℝ) / q
  let C := (Nat.primeCountingMod X q a : ℝ)
  let A := ∏ p ∈ btPrimes z q, (1 - 1 / (p : ℝ))
  let B := ∏ p ∈ z.primesLE, (1 - 1 / (p : ℝ))
  let E := (2 : ℝ) ^ Nat.primeCounting z + Nat.primeCounting z
  let ρ := (Nat.totient q : ℝ) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hXR : (0 : ℝ) < X := by exact_mod_cast hqX.trans' hq
  have hv : 1 < v := by
    dsimp only [v]
    rw [one_lt_div hqR]
    exact_mod_cast hqX
  have hv0 : 0 < v := zero_lt_one.trans hv
  have hlog : 0 < Real.log v := Real.log_pos hv
  have hphi : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hρ0 : 0 ≤ ρ := by
    dsimp only [ρ]
    positivity
  have hρ1 : ρ ≤ 1 := by
    dsimp only [ρ]
    rw [div_le_one hqR]
    exact_mod_cast Nat.totient_le q
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hAprod : ρ * A ≤ B := by
    simpa only [ρ, A, B] using btTotientMulSieveProduct_le q z hq
  have herat : C ≤ v * A + E := by
    simpa only [C, v, A, E, add_assoc] using btEratosthenesBound X q a z hq
  have hnormalized : ρ * C ≤ v * B + E := by
    calc
      ρ * C ≤ ρ * (v * A + E) := mul_le_mul_of_nonneg_left herat hρ0
      _ = v * (ρ * A) + ρ * E := by ring
      _ ≤ v * B + E := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hAprod hv0.le
        · nlinarith
  have hsieveScaled : (α * v + β) * Real.log v < v := by
    have hmul := mul_lt_mul_of_pos_left hf hv0
    have heq : v * btSieveFunction α β v =
        (α * v + β) * Real.log v := by
      dsimp only [btSieveFunction]
      field_simp
    rw [heq] at hmul
    simpa using hmul
  have hnormalized' : ρ * C ≤ 2 * (α * v + β) := by
    rw [show B = 2 * α by simpa only [B] using hprod,
      show E = 2 * β by simpa only [E] using herr] at hnormalized
    linarith
  have hlogBound : ρ * C * Real.log v < 2 * v := by
    have hmul := mul_le_mul_of_nonneg_right hnormalized' hlog.le
    nlinarith
  have hden : 0 < (Nat.totient q : ℝ) * Real.log v := mul_pos hphi hlog
  apply le_of_lt
  rw [lt_div_iff₀ hden]
  have hscaled := mul_lt_mul_of_pos_left hlogBound hqR
  have hleft : (q : ℝ) * (ρ * C * Real.log v) =
      C * ((Nat.totient q : ℝ) * Real.log v) := by
    dsimp only [ρ]
    field_simp
  have hright : (q : ℝ) * (2 * v) = 2 * X := by
    dsimp only [v]
    field_simp
  rw [hleft, hright] at hscaled
  simpa only [C, v] using hscaled

private theorem btPrimeData_two :
    (∏ p ∈ (2 : ℕ).primesLE, (1 - 1 / (p : ℝ))) = 2 * (1 / 4 : ℝ) ∧
      (2 : ℝ) ^ Nat.primeCounting 2 + Nat.primeCounting 2 = 2 * (3 / 2 : ℝ) := by
  have h : (2 : ℕ).primesLE = {2} := by decide
  constructor
  · rw [h]
    norm_num
  · rw [← Nat.primesLE_card_eq_primeCounting, h]
    norm_num

private theorem btPrimeData_three :
    (∏ p ∈ (3 : ℕ).primesLE, (1 - 1 / (p : ℝ))) = 2 * (1 / 6 : ℝ) ∧
      (2 : ℝ) ^ Nat.primeCounting 3 + Nat.primeCounting 3 = 2 * (3 : ℝ) := by
  have h : (3 : ℕ).primesLE = {2, 3} := by decide
  constructor
  · rw [h]
    norm_num
  · rw [← Nat.primesLE_card_eq_primeCounting, h]
    norm_num

private theorem btPrimeData_five :
    (∏ p ∈ (5 : ℕ).primesLE, (1 - 1 / (p : ℝ))) = 2 * (2 / 15 : ℝ) ∧
      (2 : ℝ) ^ Nat.primeCounting 5 + Nat.primeCounting 5 = 2 * (11 / 2 : ℝ) := by
  have h : (5 : ℕ).primesLE = {2, 3, 5} := by decide
  constructor
  · rw [h]
    norm_num
  · rw [← Nat.primesLE_card_eq_primeCounting, h]
    norm_num

private theorem btPrimeData_thirteen :
    (∏ p ∈ (13 : ℕ).primesLE, (1 - 1 / (p : ℝ))) = 2 * (96 / 1001 : ℝ) ∧
      (2 : ℝ) ^ Nat.primeCounting 13 + Nat.primeCounting 13 = 2 * (35 : ℝ) := by
  have h : (13 : ℕ).primesLE = {2, 3, 5, 7, 11, 13} := by decide
  constructor
  · rw [h]
    norm_num
  · rw [← Nat.primesLE_card_eq_primeCounting, h]
    norm_num

private theorem btBrunTitchmarsh_smallRange (X q a : ℕ) (hq : 0 < q)
    (hqX : q < X) (hX : X ≤ 20000 * q) :
    (Nat.primeCountingMod X q a : ℝ) ≤
      2 * (X : ℝ) /
        ((Nat.totient q : ℝ) * Real.log ((X : ℝ) / q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hv : 1 < (X : ℝ) / q := by
    rw [one_lt_div hqR]
    exact_mod_cast hqX
  have hv20000 : (X : ℝ) / q ≤ 20000 := by
    rw [div_le_iff₀ hqR]
    exact_mod_cast hX
  rcases btSieveFunction_smallRange ((X : ℝ) / q) hv hv20000 with
    hf | hf | hf | hf
  · exact btSmallRangeFromSieve X q a 2 (1 / 4) (3 / 2) hq hqX
      btPrimeData_two.1 btPrimeData_two.2 hf
  · exact btSmallRangeFromSieve X q a 3 (1 / 6) 3 hq hqX
      btPrimeData_three.1 btPrimeData_three.2 hf
  · exact btSmallRangeFromSieve X q a 5 (2 / 15) (11 / 2) hq hqX
      btPrimeData_five.1 btPrimeData_five.2 hf
  · exact btSmallRangeFromSieve X q a 13 (96 / 1001) 35 hq hqX
      btPrimeData_thirteen.1 btPrimeData_thirteen.2 hf

private theorem btLogNatLower (N : ℕ) (hN : 15000 ≤ N) :
    (48 / 5 : ℝ) < Real.log N := by
  have h15000 : (48 / 5 : ℝ) < Real.log 15000 := by
    have hfactor : Real.log (15000 : ℝ) =
        3 * Real.log 2 + Real.log 3 + 4 * Real.log 5 := by
      rw [show (15000 : ℝ) = 2 ^ 3 * 3 * 5 ^ 4 by norm_num,
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      norm_num
    rw [hfactor]
    have h2 := Real.log_two_gt_d9
    have h3 := Real.log_three_gt_d9
    have h5 := Real.log_five_gt_d9
    norm_num at h2 h3 h5 ⊢
    linarith
  refine h15000.trans_le (Real.log_le_log ?_ ?_)
  · norm_num
  · exact_mod_cast hN

private theorem btLogBoundaryUpper : Real.log 15000 < (481 / 50 : ℝ) := by
  have hfactor : Real.log (15000 : ℝ) =
      3 * Real.log 2 + Real.log 3 + 4 * Real.log 5 := by
    rw [show (15000 : ℝ) = 2 ^ 3 * 3 * 5 ^ 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [hfactor]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num at h2 h3 h5 ⊢
  linarith

private theorem btExpFourLeBoundary : Real.exp 4 ≤ (15000 : ℝ) := by
  apply (Real.le_log_iff_exp_le (by norm_num)).mp
  linarith [btLogNatLower 15000 (by norm_num)]

private theorem btLogSqBound (N : ℕ) (hN : 15000 ≤ N) :
    25 * Real.log N ^ 2 < 19 * Real.sqrt N := by
  have hmono := Real.log_div_self_rpow_antitoneOn (a := (1 / 4 : ℝ)) (by norm_num)
  have hratio : Real.log N / (N : ℝ) ^ (1 / 4 : ℝ) ≤
      Real.log 15000 / (15000 : ℝ) ^ (1 / 4 : ℝ) := by
    apply hmono
    · simpa using btExpFourLeBoundary
    · simpa using btExpFourLeBoundary.trans (by exact_mod_cast hN)
    · exact_mod_cast hN
  have hleftnonneg : 0 ≤ Real.log N / (N : ℝ) ^ (1 / 4 : ℝ) := by
    positivity
  have hrightnonneg : 0 ≤ Real.log 15000 / (15000 : ℝ) ^ (1 / 4 : ℝ) := by
    positivity
  have hsq := sq_le_sq₀ hleftnonneg hrightnonneg |>.mpr hratio
  have hboundarySqrt : (122 : ℝ) < Real.sqrt 15000 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hboundary :
      25 * Real.log 15000 ^ 2 < 19 * Real.sqrt 15000 := by
    have hlogpos : 0 ≤ Real.log 15000 := Real.log_nonneg (by norm_num)
    have hlogsq : Real.log 15000 ^ 2 < (481 / 50 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hlogpos (by norm_num)).mpr btLogBoundaryUpper
    nlinarith
  have hNroot : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt N := by
    rw [← Real.rpow_mul_natCast (by positivity), Real.sqrt_eq_rpow]
    norm_num
  have h15000root :
      ((15000 : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt 15000 := by
    rw [← Real.rpow_mul_natCast (by positivity), Real.sqrt_eq_rpow]
    norm_num
  rw [div_pow, hNroot, div_pow, h15000root] at hsq
  have hsqrtN : 0 < Real.sqrt N :=
    Real.sqrt_pos.2 (by exact_mod_cast hN.trans' (by norm_num))
  have hsqrt15000 : 0 < Real.sqrt 15000 := by positivity
  rw [div_le_div_iff₀ hsqrtN hsqrt15000] at hsq
  nlinarith

private theorem btSieveLevelData (N : ℕ) (hN : 15000 ≤ N) :
    let z := Nat.sqrt (2 * N / 3)
    100 ≤ z ∧ (4 / 5 : ℝ) * Real.sqrt N < z ∧
      (Nat.primeCounting z : ℝ) ≤ Real.sqrt N / 2 + 1 := by
  let z := Nat.sqrt (2 * N / 3)
  have harg : 100 ^ 2 ≤ 2 * N / 3 := by omega
  have hz100 : 100 ≤ z := Nat.le_sqrt'.mpr harg
  have hsquareUpper : 2 * N < 3 * (z + 1) ^ 2 := by
    have hsqrtlt : 2 * N / 3 < (z + 1) ^ 2 := by
      exact Nat.lt_succ_sqrt' (2 * N / 3)
    omega
  have hquad : 24 * (z + 1) ^ 2 ≤ 25 * z ^ 2 := by
    nlinarith
  have hNZ : 16 * N < 25 * z ^ 2 := by
    nlinarith
  have hNZR : 16 * (N : ℝ) < 25 * (z : ℝ) ^ 2 := by
    exact_mod_cast hNZ
  have hsqrtSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hscaledSq : (4 * Real.sqrt N) ^ 2 < (5 * (z : ℝ)) ^ 2 := by
    nlinarith
  have hscaled : 4 * Real.sqrt N < 5 * (z : ℝ) :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mp hscaledSq
  have hzsq : z ^ 2 ≤ N := by
    calc
      z ^ 2 ≤ 2 * N / 3 := by simpa only [z] using Nat.sqrt_le' (2 * N / 3)
      _ ≤ N := by omega
  have hzsqR : (z : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hzsq
  have hzSqrt : (z : ℝ) ≤ Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hpcAdd := Nat.primeCounting_add_le (a := 2) (k := 2)
    (by norm_num) (by norm_num) (z - 2)
  have hzRewrite : 2 + (z - 2) = z := by omega
  rw [hzRewrite] at hpcAdd
  have hpcTwo : Nat.primeCounting 2 = 1 := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    have h : (2 : ℕ).primesLE = {2} := by decide
    rw [h]
    norm_num
  rw [hpcTwo] at hpcAdd
  norm_num at hpcAdd
  have hpcNat : 2 * Nat.primeCounting z ≤ z + 2 := by omega
  have hpcReal : 2 * (Nat.primeCounting z : ℝ) ≤ (z : ℝ) + 2 := by
    exact_mod_cast hpcNat
  refine ⟨hz100, ?_, ?_⟩
  · norm_num at hscaled ⊢
    linarith
  · linarith

private theorem btSieveDensityLower (N : ℕ) (hN : 15000 ≤ N) :
    let z := Nat.sqrt (2 * N / 3)
    (Real.log N + 13 / 50) / (2 * N) <
      ∑ r ∈ Finset.Icc 1 z,
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
          (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) := by
  let z := Nat.sqrt (2 * N / 3)
  rcases btSieveLevelData N hN with ⟨hz100, hscale, hprime⟩
  have hNpos : (0 : ℝ) < N := by positivity
  have hzpos : (0 : ℝ) < z := by positivity
  have hlogFourFifths : (-23 / 100 : ℝ) < Real.log (4 / 5 : ℝ) := by
    have hlog : Real.log (4 / 5 : ℝ) = 2 * Real.log 2 - Real.log 5 := by
      rw [show (4 / 5 : ℝ) = 2 ^ 2 / 5 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    rw [hlog]
    have h2 := Real.log_two_gt_d9
    have h5 := Real.log_five_lt_d9
    norm_num at h2 h5 ⊢
    linarith
  have hlogScale : Real.log ((4 / 5 : ℝ) * Real.sqrt N) < Real.log z := by
    apply Real.strictMonoOn_log
    · exact mul_pos (by norm_num) (Real.sqrt_pos.2 (by positivity))
    · exact hzpos
    · exact hscale
  have hlogSqrt : Real.log (Real.sqrt N) = Real.log N / 2 := by
    exact Real.log_sqrt (by positivity)
  have hlogz : Real.log N / 2 - 23 / 100 < Real.log z := by
    rw [Real.log_mul (by norm_num : (4 / 5 : ℝ) ≠ 0) (by positivity), hlogSqrt]
      at hlogScale
    linarith
  have hweighted := squarefreeTotientWeightedLower z hz100
  have hW : Real.log N / 2 + 13 / 100 <
      ∑ r ∈ Finset.Icc 1 z, (1 + (r : ℝ) / z)⁻¹ *
        (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) := by
    linarith
  have hzsqNat : 3 * z ^ 2 ≤ 2 * N := by
    have hzsq : z ^ 2 ≤ 2 * N / 3 := by
      simpa only [z] using Nat.sqrt_le' (2 * N / 3)
    omega
  have hzsq : 3 * (z : ℝ) ^ 2 / 2 ≤ (N : ℝ) := by
    have hzsqReal : 3 * (z : ℝ) ^ 2 ≤ 2 * (N : ℝ) := by
      exact_mod_cast hzsqNat
    linarith
  have hterm (r : ℕ) (hr : r ∈ Finset.Icc 1 z) :
      (N : ℝ)⁻¹ * (1 + (r : ℝ) / z)⁻¹ *
          (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) ≤
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
          (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) := by
    have hrnonneg : (0 : ℝ) ≤ r := by positivity
    have hmul : 3 * (r : ℝ) * z / 2 ≤ (N : ℝ) * ((r : ℝ) / z) := by
      calc
        3 * (r : ℝ) * z / 2 = ((r : ℝ) / z) * (3 * z ^ 2 / 2) := by
          field_simp
        _ ≤ ((r : ℝ) / z) * N := mul_le_mul_of_nonneg_left hzsq (by positivity)
        _ = (N : ℝ) * ((r : ℝ) / z) := by ring
    have hden : (N : ℝ) + 3 * (r : ℝ) * z / 2 ≤
        (N : ℝ) * (1 + (r : ℝ) / z) := by
      nlinarith
    have hinv : ((N : ℝ) * (1 + (r : ℝ) / z))⁻¹ ≤
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ := by
      apply inv_anti₀
      · positivity
      · exact hden
    have hphi : (0 : ℝ) < Nat.totient r := by
      have hrpos : 0 < r := by
        have hrone : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        omega
      exact_mod_cast Nat.totient_pos.mpr hrpos
    have hcoef : 0 ≤
        (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) := by
      positivity
    rw [mul_inv] at hinv
    exact mul_le_mul_of_nonneg_right hinv hcoef
  have hsum :
      (N : ℝ)⁻¹ *
          (∑ r ∈ Finset.Icc 1 z, (1 + (r : ℝ) / z)⁻¹ *
            (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) ≤
        ∑ r ∈ Finset.Icc 1 z,
          ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
            (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    convert hterm r hr using 1
    ring
  calc
    (Real.log N + 13 / 50) / (2 * N) =
        (N : ℝ)⁻¹ * (Real.log N / 2 + 13 / 100) := by
      field_simp
      ring
    _ < (N : ℝ)⁻¹ *
        (∑ r ∈ Finset.Icc 1 z, (1 + (r : ℝ) / z)⁻¹ *
          (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) := by
      exact mul_lt_mul_of_pos_left hW (by positivity)
    _ ≤ _ := hsum

private theorem btNumericalDenominator (N : ℕ) (hN : 15000 ≤ N) :
    Real.sqrt N / 2 + 1 + 2 * N / (Real.log N + 13 / 50) <
      (2 * N - 2) / Real.log N := by
  let L := Real.log N
  let s := Real.sqrt N
  have hL : (48 / 5 : ℝ) < L := btLogNatLower N hN
  have hLpos : 0 < L := by linarith
  have hdenpos : 0 < L + 13 / 50 := by positivity
  have hspos : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hN.trans' (by norm_num))
  have hsSq : s ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hlogsq : 25 * L ^ 2 < 19 * s := btLogSqBound N hN
  have hfactor : L + 13 / 50 < (493 / 480 : ℝ) * L := by
    nlinarith
  have hprod : L * (L + 13 / 50) < (493 / 480 : ℝ) * L ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left hfactor hLpos]
  have hlogsq' : L ^ 2 < (19 / 25 : ℝ) * s := by nlinarith
  have hscaledProd :
      (3 / 5 : ℝ) * s * (L * (L + 13 / 50)) <
        (3 / 5 : ℝ) * s * ((493 / 480 : ℝ) * L ^ 2) := by
    exact mul_lt_mul_of_pos_left hprod (mul_pos (by norm_num) hspos)
  have hscaledLog :
      (3 / 5 : ℝ) * s * ((493 / 480 : ℝ) * L ^ 2) <
        (3 / 5 : ℝ) * s * ((493 / 480 : ℝ) * ((19 / 25 : ℝ) * s)) := by
    gcongr
  have hmargin :
      (3 / 5 : ℝ) * s * (L * (L + 13 / 50)) < (13 / 25 : ℝ) * N := by
    calc
      (3 / 5 : ℝ) * s * (L * (L + 13 / 50)) <
          (3 / 5 : ℝ) * s * ((493 / 480 : ℝ) * L ^ 2) := hscaledProd
      _ < (3 / 5 : ℝ) * s * ((493 / 480 : ℝ) * ((19 / 25 : ℝ) * s)) :=
        hscaledLog
      _ < (13 / 25 : ℝ) * N := by
        rw [← hsSq]
        norm_num
        nlinarith [sq_nonneg s]
  have hprodpos : 0 < L * (L + 13 / 50) := mul_pos hLpos hdenpos
  have hdiff : (3 / 5 : ℝ) * s <
      2 * N / L - 2 * N / (L + 13 / 50) := by
    calc
      (3 / 5 : ℝ) * s <
          ((13 / 25 : ℝ) * N) / (L * (L + 13 / 50)) :=
        (lt_div_iff₀ hprodpos).2 hmargin
      _ = 2 * N / L - 2 * N / (L + 13 / 50) := by
        field_simp
        ring
  have hs120 : (120 : ℝ) < s := by
    dsimp only [s]
    rw [Real.lt_sqrt (by positivity)]
    exact_mod_cast (show 120 ^ 2 < N by omega)
  have htwoLog : 2 / L < (5 / 24 : ℝ) := by
    rw [div_lt_iff₀ hLpos]
    nlinarith
  have hsmall : s / 2 + 1 + 2 / L < (3 / 5 : ℝ) * s := by
    nlinarith
  have hrhs : (2 * (N : ℝ) - 2) / L = 2 * N / L - 2 / L := by
    field_simp
  dsimp only [L, s] at hdiff hsmall hrhs ⊢
  rw [hrhs]
  linarith

private theorem btLargeSieveDenominator (N : ℕ) (hN : 15000 ≤ N) :
    let z := Nat.sqrt (2 * N / 3)
    (Nat.primeCounting z : ℝ) +
        (∑ r ∈ Finset.Icc 1 z,
          ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
            (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 /
              Nat.totient r))⁻¹ <
      (2 * N - 2) / Real.log N := by
  let z := Nat.sqrt (2 * N / 3)
  let D : ℝ := ∑ r ∈ Finset.Icc 1 z,
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)
  let b := (Real.log N + 13 / 50) / (2 * N)
  have hDensity : b < D := btSieveDensityLower N hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogpos : 0 < Real.log N := by linarith [btLogNatLower N hN]
  have hbpos : 0 < b := div_pos (by positivity) (by positivity)
  have hDpos : 0 < D := hbpos.trans hDensity
  have hInv : D⁻¹ < 2 * N / (Real.log N + 13 / 50) := by
    have hinv := (inv_lt_inv₀ hDpos hbpos).2 hDensity
    calc
      D⁻¹ < b⁻¹ := hinv
      _ = 2 * N / (Real.log N + 13 / 50) := by
        dsimp only [b]
        field_simp
  have hprime := (btSieveLevelData N hN).2.2
  have hnum := btNumericalDenominator N hN
  dsimp only [D, z] at hInv hprime ⊢
  linarith

private theorem btLargeRange (X q a : ℕ) (haq : Nat.Coprime a q)
    (hq : 0 < q) (hlargeX : 20000 * q < X) :
    (Nat.primeCountingMod X q a : ℝ) ≤
      2 * (X : ℝ) /
        ((Nat.totient q : ℝ) * Real.log ((X : ℝ) / q)) := by
  let a0 := a % q
  let N := X / q + 1
  let z := Nat.sqrt (2 * N / 3)
  let T := (Finset.range (X + 1)).filter fun p ↦ p.Prime ∧ p ≡ a [MOD q]
  let Tsmall := T.filter fun p ↦ p ≤ z
  let Tlarge := T.filter fun p ↦ ¬p ≤ z
  let S := (Finset.range N).filter fun n ↦
    (q * n + a0).Prime ∧ z < q * n + a0 ∧ Nat.Coprime a0 q
  have ha0q : Nat.Coprime a0 q := by
    rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec]
    exact haq.symm
  have hfloor : 20000 ≤ X / q := by
    exact (Nat.le_div_iff_mul_le hq).2 hlargeX.le
  have hN : 15000 ≤ N := by
    dsimp only [N]
    omega
  have hz : 0 < z := by
    have hz100 := (btSieveLevelData N hN).1
    omega
  have hTcard : T.card = Nat.primeCountingMod X q a := by
    simpa only [T] using (Nat.primeCountingMod_eq_card_filter_range X q a).symm
  have hsplit : Tsmall.card + Tlarge.card = T.card := by
    simpa only [Tsmall, Tlarge] using
      Finset.card_filter_add_card_filter_not (s := T) (fun p ↦ p ≤ z)
  have hsmall : Tsmall.card ≤ Nat.primeCounting z := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    simp only [Tsmall, T, Finset.mem_filter, Finset.mem_range] at hp
    exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.2.1⟩
  have hreconstruct {p : ℕ} (hp : p ≡ a [MOD q]) : q * (p / q) + a0 = p := by
    have hmod : p % q = a % q := hp
    dsimp only [a0]
    rw [← hmod, add_comm]
    exact Nat.mod_add_div p q
  have hlargeMap : Set.MapsTo (fun p ↦ p / q) Tlarge S := by
    intro p hp
    simp only [Finset.mem_coe, Tlarge, T, Finset.mem_filter, Finset.mem_range] at hp
    simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_range]
    have hpLeX : p ≤ X := by omega
    have hdivLe : p / q ≤ X / q := Nat.div_le_div_right hpLeX
    have hpEq := hreconstruct hp.1.2.2
    refine ⟨by dsimp only [N]; omega, ?_, ?_, ha0q⟩
    · simpa only [hpEq] using hp.1.2.1
    · rw [hpEq]
      omega
  have hlargeInj : Set.InjOn (fun p ↦ p / q) Tlarge := by
    intro p hp r hr hpr
    simp only [Finset.mem_coe, Tlarge, T, Finset.mem_filter, Finset.mem_range] at hp hr
    have hpEq := hreconstruct hp.1.2.2
    have hrEq := hreconstruct hr.1.2.2
    change p / q = r / q at hpr
    calc
      p = q * (p / q) + a0 := hpEq.symm
      _ = q * (r / q) + a0 := by rw [hpr]
      _ = r := hrEq
  have hlarge : Tlarge.card ≤ S.card :=
    Finset.card_le_card_of_injOn (fun p ↦ p / q) hlargeMap hlargeInj
  have hcountNat : Nat.primeCountingMod X q a ≤ Nat.primeCounting z + S.card := by
    rw [← hTcard]
    omega
  have hcount : (Nat.primeCountingMod X q a : ℝ) ≤
      Nat.primeCounting z + S.card := by exact_mod_cast hcountNat
  have hS : S ⊆ Finset.range N := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hSprime : ∀ n ∈ S, (q * n + a0).Prime := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2.1
  have hSlarge : ∀ n ∈ S, z < q * n + a0 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2.2.1
  let D : ℝ := ∑ r ∈ Finset.Icc 1 z,
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)
  have hsieve : D * S.card ^ 2 ≤ ((q : ℝ) / Nat.totient q) * S.card := by
    simpa only [D] using
      arithmeticLargeSieve_progression N z q a0 hz hq S hS hSprime hSlarge
  have hDensity : (Real.log N + 13 / 50) / (2 * N) < D :=
    btSieveDensityLower N hN
  have hDensityBase : 0 < (Real.log N + 13 / 50) / (2 * N) := by
    have hlog := btLogNatLower N hN
    positivity
  have hDpos : 0 < D := hDensityBase.trans hDensity
  have hphi : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hratioNonneg : 0 ≤ (q : ℝ) / Nat.totient q := by positivity
  have hScard : (S.card : ℝ) ≤ ((q : ℝ) / Nat.totient q) * D⁻¹ := by
    by_cases hSzero : S.card = 0
    · rw [hSzero]
      norm_num
      positivity
    · have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hSzero
      have hcancel : D * S.card ≤ (q : ℝ) / Nat.totient q := by
        apply le_of_mul_le_mul_right ?_ hSpos
        convert hsieve using 1
        ring
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ hDpos).2
      simpa only [mul_comm] using hcancel
  have hratioOne : (1 : ℝ) ≤ (q : ℝ) / Nat.totient q := by
    rw [one_le_div hphi]
    exact_mod_cast Nat.totient_le q
  have hden : (Nat.primeCounting z : ℝ) + D⁻¹ <
      (2 * N - 2) / Real.log N := by
    simpa only [D, z] using btLargeSieveDenominator N hN
  have hcountRatio : (Nat.primeCountingMod X q a : ℝ) <
      ((q : ℝ) / Nat.totient q) * ((2 * N - 2) / Real.log N) := by
    calc
      (Nat.primeCountingMod X q a : ℝ) ≤ Nat.primeCounting z + S.card := hcount
      _ ≤ ((q : ℝ) / Nat.totient q) *
          ((Nat.primeCounting z : ℝ) + D⁻¹) := by
        calc
          (Nat.primeCounting z : ℝ) + S.card ≤
              ((q : ℝ) / Nat.totient q) * Nat.primeCounting z +
                ((q : ℝ) / Nat.totient q) * D⁻¹ := by
            apply add_le_add
            · calc
                (Nat.primeCounting z : ℝ) = 1 * Nat.primeCounting z := by ring
                _ ≤ ((q : ℝ) / Nat.totient q) * Nat.primeCounting z := by
                  exact mul_le_mul_of_nonneg_right hratioOne (by positivity)
            · exact hScard
          _ = _ := by ring
      _ < ((q : ℝ) / Nat.totient q) * ((2 * N - 2) / Real.log N) := by
        exact mul_lt_mul_of_pos_left hden (by positivity)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqX : q < X := by omega
  have hv : 1 < (X : ℝ) / q := by
    rw [one_lt_div hqR]
    exact_mod_cast hqX
  have hlogv : 0 < Real.log ((X : ℝ) / q) := Real.log_pos hv
  have hNv : (X : ℝ) / q < N := by
    rw [div_lt_iff₀ hqR]
    have hdivlt : X / q < N := by simp [N]
    have hnat : X < N * q := (Nat.div_lt_iff_lt_mul hq).mp hdivlt
    exact_mod_cast hnat
  have hlogLe : Real.log ((X : ℝ) / q) ≤ Real.log N := by
    exact Real.log_le_log (by positivity) hNv.le
  have hNsub : N - 1 = X / q := by simp [N]
  have hqFloor : q * (N - 1) ≤ X := by
    rw [hNsub]
    exact Nat.mul_div_le X q
  have hqFloorR : (q : ℝ) * ((N - 1 : ℕ) : ℝ) ≤ X := by
    exact_mod_cast hqFloor
  have hlogN : 0 < Real.log N := hlogv.trans_le hlogLe
  have hfinalCompare :
      ((q : ℝ) / Nat.totient q) * ((2 * N - 2) / Real.log N) ≤
        2 * (X : ℝ) / ((Nat.totient q : ℝ) * Real.log ((X : ℝ) / q)) := by
    have hleft :
        ((q : ℝ) / Nat.totient q) * ((2 * N - 2) / Real.log N) =
          ((q : ℝ) * (2 * N - 2)) /
            ((Nat.totient q : ℝ) * Real.log N) := by
      field_simp
    rw [hleft]
    rw [div_le_div_iff₀ (mul_pos hphi hlogN) (mul_pos hphi hlogv)]
    have hcastSub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by dsimp only [N]; omega)]
      norm_num
    have hproduct := mul_le_mul hqFloorR hlogLe hlogv.le
      (by positivity : (0 : ℝ) ≤ X)
    rw [hcastSub] at hproduct
    have hscaled := mul_le_mul_of_nonneg_left hproduct
      (mul_nonneg (by norm_num) hphi.le : 0 ≤ 2 * (Nat.totient q : ℝ))
    convert hscaled using 1 <;> ring
  exact hcountRatio.le.trans hfinalCompare

/-- **Brun–Titchmarsh inequality.** Let $X$, $q$ and $a$ be natural numbers such that $a$ and $q$
are coprime and $1 \le q < X$. Write $\pi(X; q, a)$ for the number of primes $p \le X$ with
$p \equiv a \pmod{q}$, and $\varphi$ for Euler's totient function. Then
$$
\pi(X; q, a) \le \frac{2X}{\varphi(q) \log(X/q)}.
$$

The proof uses an elementary Eratosthenes sieve when $X \le 20000q$. For larger $X$ it combines
the weighted arithmetic large sieve with explicit lower bounds for the squarefree-totient sum and
the choice $z = \lfloor \sqrt{2N/3} \rfloor$, where $N = \lfloor X/q \rfloor + 1$.

Proves `Wanted` entry `brun_titchmarsh`.

Source: H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium
Publications 53, 2004, Theorem 6.6; quoted as equation (1) in Y. Wang and
X. Zhang, arXiv:2608.19262v1.
-/
public theorem brun_titchmarsh (X q a : ℕ) (haq : Nat.Coprime a q)
    (hq : 1 ≤ q) (hqX : q < X) :
    (Nat.primeCountingMod X q a : ℝ) ≤
      2 * (X : ℝ) / ((Nat.totient q : ℝ) * Real.log ((X : ℝ) / (q : ℝ))) := by
  have hqpos : 0 < q := by omega
  by_cases hsmall : X ≤ 20000 * q
  · exact btBrunTitchmarsh_smallRange X q a hqpos hqX hsmall
  · exact btLargeRange X q a haq hqpos (lt_of_not_ge hsmall)

end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted
