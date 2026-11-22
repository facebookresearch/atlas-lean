/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.Float.Model
public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
public import Mathlib.Data.Rat.Floor
import all MathlibExt.Data.Float.Model

/-!
# Core binary64 operations and rational nearest-even rounding

`Float.Model.toRat?_add` and `Float.Model.toRat?_mul` bind both actual operands to rational
witnesses and prove agreement with Atlas `fl 53` when the exact result's absolute value lies
in the inclusive interval from the smallest normal number to the largest finite number.
All finite input encodings are admitted; output finiteness follows from the value equation.

The private proof chain relates residual bits to `rne`, handles the exact carry and finite
packing, and derives the required representation bounds from actual decoded operands.
-/

namespace Cslib.Algorithms.Lean.FloatingPoint

open Float.Model Float.Model.UnpackedFloat

private theorem roundedMantissa_eq_rne {x : Rat} {em : ExtendedMantissa}
    (h : HasResidual x em) : (em.roundedMantissa : Int) = rne x := by
  have hf : Int.floor x = em.mantissa :=
    Int.floor_eq_iff.mpr (by simpa using And.intro h.1 h.2.1)
  obtain ⟨m, r, s⟩ := em
  obtain ⟨hlo, hhi, hr, hs⟩ := h
  simp only at hf hr hs
  rw [rne, hf]
  simp only [Int.cast_natCast]
  cases r <;> cases s <;>
    simp only [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven, Nat.cast_add, Nat.cast_one]
  · have hlt := lt_of_not_ge (of_decide_eq_false hr.symm)
    rw [ite_eq_left hlt]
  · have hlt := lt_of_not_ge (of_decide_eq_false hr.symm)
    rw [ite_eq_left hlt]
  · have hge := of_decide_eq_true hr.symm
    have hnot := of_decide_eq_false hs.symm
    have hh : x - m = 1 / 2 := by
      by_contra hn
      exact hnot ⟨by linarith, hn⟩
    rw [hh, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
    simp only [Int.even_coe_nat, Nat.even_iff]
    split_ifs with he
    · simp [he]
    · have he' : m % 2 = 1 := by omega
      simp [he']
  · have hge := of_decide_eq_true hr.symm
    have hne := (of_decide_eq_true hs.symm).2
    rw [ite_eq_right (by linarith), ite_eq_left (by exact lt_of_le_of_ne hge (Ne.symm hne))]

private theorem rounded_shift_eq_rne (m n : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy m .exact >>> n).roundedMantissa : Int) =
      rne ((m : Rat) / 2 ^ n) :=
  roundedMantissa_eq_rne (hasResidual_shiftRight m n)

private theorem rne_unique {x : Rat} {k : Int}
    (hk : |(k : Rat) - x| ≤ 1 / 2)
    (he : |(k : Rat) - x| = 1 / 2 → Even k) : rne x = k := by
  have hr := abs_rne_sub_le_half x
  obtain ⟨hk₁, hk₂⟩ := abs_le.mp hk
  obtain ⟨hr₁, hr₂⟩ := abs_le.mp hr
  rcases lt_trichotomy (rne x) k with hlt | heq | hgt
  · have hgap : (rne x : Rat) + 1 ≤ k := by exact_mod_cast hlt
    have hdist : |(rne x : Rat) - x| = 1 / 2 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hkdist : |(k : Rat) - x| = 1 / 2 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have he₁ := Int.even_iff.mp (even_rne_of_abs_sub_eq_half hdist)
    have he₂ := Int.even_iff.mp (he hkdist)
    have hdiff : (k : Rat) = rne x + 1 := by linarith
    have hdiff' : k = rne x + 1 := by exact_mod_cast hdiff
    omega
  · exact heq
  · have hgap : (k : Rat) + 1 ≤ rne x := by exact_mod_cast hgt
    have hdist : |(rne x : Rat) - x| = 1 / 2 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hkdist : |(k : Rat) - x| = 1 / 2 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have he₁ := Int.even_iff.mp (even_rne_of_abs_sub_eq_half hdist)
    have he₂ := Int.even_iff.mp (he hkdist)
    have hdiff : (rne x : Rat) = k + 1 := by linarith
    have hdiff' : rne x = k + 1 := by exact_mod_cast hdiff
    omega

private theorem rne_neg (x : Rat) : rne (-x) = -rne x := by
  have hd : |((-rne x : Int) : Rat) - -x| = |(rne x : Rat) - x| := by
    rw [Int.cast_neg, neg_sub_neg, abs_sub_comm]
  apply rne_unique
  · rw [hd]
    exact abs_rne_sub_le_half x
  · intro h
    exact (even_rne_of_abs_sub_eq_half (hd ▸ h)).neg


private theorem fl_neg (p : Nat) (x : Rat) : fl p (-x) = -fl p x := by
  simp [fl, ulpExp, neg_div, rne_neg]

private theorem normal_exponent_bounds (m : Nat) (hm : 0 < m) (e : Int)
    (hlo : (2 : Rat) ^ (-1022 : Int) ≤ m * (2 : Rat) ^ e)
    (hhi : (m : Rat) * 2 ^ e ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int)) :
    -1074 ≤ (m.log2 : Int) + e - 52 ∧ (m.log2 : Int) + e - 52 ≤ 971 := by
  have hp : (0 : Rat) < m * (2 : Rat) ^ e :=
    mul_pos (by exact_mod_cast hm) (two_zpow_pos e)
  have hlog := log_nat_mul_two_zpow m hm e
  have h₁ := (Int.zpow_le_iff_le_log (by decide : 1 < 2) hp).mp hlo
  have hbound : (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int) < (2 : Rat) ^ (1024 : Int) := by
    calc (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int) <
        2 ^ (53 : Nat) * (2 : Rat) ^ (971 : Int) :=
          mul_lt_mul_of_pos_right (by norm_num) (two_zpow_pos _)
      _ = (2 : Rat) ^ (1024 : Int) := by
        rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
        rfl
  have h₂ := (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hp).mp (hhi.trans_lt hbound)
  rw [hlog] at h₁ h₂
  omega

private theorem roundWithAccuracy_toRat?_of_shift (s : Sign) (m : Nat) (e : Int)
    (em : ExtendedMantissa) (t : Int)
    (hshift : shiftToTargetExponent Format.binary64 m e .exact = (em, t))
    (hrlo : 2 ^ 52 ≤ em.roundedMantissa) (hrhi : em.roundedMantissa ≤ 2 ^ 53)
    (htlo : -1074 ≤ t) (hthi : t ≤ 971)
    (hcarry : em.roundedMantissa = 2 ^ 53 → t < 971) :
    (Float.Model.pack (roundWithAccuracy Format.binary64 s m e .exact)).toRat? =
      some ((s.apply em.roundedMantissa : Rat) * 2 ^ t) := by
  by_cases hc : em.roundedMantissa = 2 ^ 53
  · have ht : t + 1 ≤ 971 := by have := hcarry hc; omega
    have htarget : Format.binary64.targetExponent (totalExponent (2 ^ 53) t) = t + 1 := by
      norm_num [Format.targetExponent, Format.mantissaBits, Format.minExponent, totalExponent]
      omega
    have hsecond : shiftToTargetExponent Format.binary64 em.roundedMantissa t .exact =
        (ExtendedMantissa.ofMantissaAndAccuracy (2 ^ 52) .exact, t + 1) := by
      simp only [hc, shiftToTargetExponent, htarget, shiftToExponent]
      have hsub : (t + 1 - t).toNat = 1 := by omega
      rw [hsub]
      rfl
    have hnz : (2 ^ 52 : Nat) ≠ 0 := pow_ne_zero _ (by decide)
    simp only [roundWithAccuracy, hshift, hsecond, ExtendedMantissa.ofMantissaAndAccuracy,
      hnz, dite_false]
    trans some ((s.apply (2 ^ 52) : Rat) * 2 ^ (t + 1))
    · exact toRat?_pack_normal s (2 ^ 52) (t + 1) (by decide) (by decide) (by decide)
        (by omega) ht
    rw [hc]
    cases s <;> simp [Sign.apply, zpow_add₀ (by decide : (2 : Rat) ≠ 0)] <;> ring
  · have hrlt : em.roundedMantissa < 2 ^ 53 := by omega
    have hrpos : 0 < em.roundedMantissa := by omega
    have hlog : em.roundedMantissa.log2 = 52 := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_eq_of_pow_le_of_lt_pow hrlo hrlt
    have htarget : Format.binary64.targetExponent (totalExponent em.roundedMantissa t) = t := by
      norm_num [Format.targetExponent, Format.mantissaBits, Format.minExponent, totalExponent, hlog]
      omega
    have hsecond : shiftToTargetExponent Format.binary64 em.roundedMantissa t .exact =
        (ExtendedMantissa.ofMantissaAndAccuracy em.roundedMantissa .exact, t) := by
      simp only [shiftToTargetExponent, htarget, shiftToExponent, sub_self, Int.toNat_zero]
      change (Nat.repeat ExtendedMantissa.shiftRightOne 0 _, t + 0) = _
      simp only [Nat.repeat, add_zero]
    simp only [roundWithAccuracy, hshift, hsecond, ExtendedMantissa.ofMantissaAndAccuracy,
      hrpos.ne', dite_false]
    exact toRat?_pack_normal s _ t hrpos hrlo hrlt htlo hthi

private theorem roundWithAccuracy_normal (s : Sign) (m : Nat) (e : Int)
    (hm : 2 ^ 52 ≤ m)
    (hlo : (2 : Rat) ^ (-1022 : Int) ≤ m * (2 : Rat) ^ e)
    (hhi : (m : Rat) * 2 ^ e ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int)) :
    (Float.Model.pack (roundWithAccuracy Format.binary64 s m e .exact)).toRat? =
      some (fl 53 ((s.apply m : Rat) * 2 ^ e)) := by
  have hmpos : 0 < m := by omega
  have hlogge : 52 ≤ m.log2 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by decide) hm
  let n := m.log2 - 52
  let t : Int := e + n
  let em := ExtendedMantissa.ofMantissaAndAccuracy m .exact >>> n
  let x : Rat := m * (2 : Rat) ^ e
  have hxpos : 0 < x := mul_pos (by exact_mod_cast hmpos) (two_zpow_pos e)
  have htexp : t = (m.log2 : Int) + e - 52 := by dsimp [t, n]; omega
  obtain ⟨htlo, hthi⟩ := normal_exponent_bounds m hmpos e hlo hhi
  rw [← htexp] at htlo hthi
  have htarget : Format.binary64.targetExponent (totalExponent m e) = t := by
    norm_num [Format.targetExponent, Format.mantissaBits, Format.minExponent, totalExponent]
    omega
  have hshift : shiftToTargetExponent Format.binary64 m e .exact = (em, t) := by
    simp only [shiftToTargetExponent, htarget, shiftToExponent]
    have hn : (t - e).toNat = n := by dsimp [t]; omega
    rw [hn]
  have hscale : x / 2 ^ t = (m : Rat) / 2 ^ n := by
    dsimp [x, t]
    rw [zpow_add₀ two_ne_zero, zpow_natCast]
    field_simp
  have hulp : ulpExp 53 x = t := by
    rw [ulpExp, abs_of_pos hxpos, log_nat_mul_two_zpow m hmpos e]
    norm_num
    omega
  have hr : (em.roundedMantissa : Int) = rne (x / 2 ^ t) := by
    rw [hscale]
    exact rounded_shift_eq_rne m n
  have hb := scaled_bounds (p := 53) (by decide) hxpos.ne'
  rw [hulp, abs_of_pos (div_pos hxpos (two_zpow_pos t))] at hb
  have hrlo : 2 ^ 52 ≤ em.roundedMantissa := by
    have h : ((2 ^ 52 : Nat) : Int) ≤ em.roundedMantissa := by
      rw [hr]
      apply le_rne_of_le
      exact_mod_cast hb.1
    exact_mod_cast h
  have hrhi : em.roundedMantissa ≤ 2 ^ 53 := by
    have h : (em.roundedMantissa : Int) ≤ ((2 ^ 53 : Nat) : Int) := by
      rw [hr]
      apply rne_le_of_le
      exact_mod_cast hb.2.le
    exact_mod_cast h
  have hcarry : em.roundedMantissa = 2 ^ 53 → t < 971 := by
    intro hc
    by_contra hn
    have ht : t = 971 := by omega
    have hs : x / 2 ^ t ≤ ((2 ^ 53 - 1 : Int) : Rat) := by
      rw [div_le_iff₀ (two_zpow_pos t), ht]
      simpa only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_one] using hhi
    have hh := rne_le_of_le hs
    rw [← hr, hc] at hh
    norm_num at hh
  rw [roundWithAccuracy_toRat?_of_shift s m e em t hshift hrlo hrhi htlo hthi hcarry]
  have hfl : fl 53 x = (em.roundedMantissa : Rat) * 2 ^ t := by
    rw [fl, hulp, ← hr]
    simp
  cases s <;> simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul, fl_neg]
  · rw [hfl]
  · rw [hfl]

private theorem round_normal (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hlo : (2 : Rat) ^ (-1022 : Int) ≤ m * (2 : Rat) ^ e)
    (hhi : (m : Rat) * 2 ^ e ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int)) :
    (Float.Model.pack (UnpackedFloat.round Format.binary64 s m e)).toRat? =
      some (fl 53 ((s.apply m : Rat) * 2 ^ e)) := by
  let t := Format.binary64.targetExponent (totalExponent m e)
  let dm := decreaseExponent m e t
  obtain ⟨he, -⟩ := normal_exponent_bounds m hm e hlo hhi
  have ht : t ≤ (m.log2 : Int) + e - 52 := by
    dsimp [t]
    norm_num [Format.targetExponent, Format.mantissaBits, Format.minExponent, totalExponent]
    omega
  have hm' : 2 ^ 52 ≤ dm.1 := decreaseExponent_mantissa_ge m e t hm ht
  have hv : (dm.1 : Rat) * 2 ^ dm.2 = (m : Rat) * 2 ^ e :=
    decreaseExponent_value m e t
  have hs : (s.apply dm.1 : Rat) * 2 ^ dm.2 = (s.apply m : Rat) * 2 ^ e := by
    cases s <;> simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul]
    · exact congrArg Neg.neg hv
    · exact hv
  have h := roundWithAccuracy_normal s dm.1 dm.2 hm'
    (by simpa only [hv] using hlo) (by simpa only [hv] using hhi)
  rw [hs] at h
  simpa only [UnpackedFloat.round, dm, t] using h

private theorem normalize_normal (m : Int) (e : Int) (zs : Sign)
    (hlo : (2 : Rat) ^ (-1022 : Int) ≤ |(m : Rat) * 2 ^ e|)
    (hhi : |(m : Rat) * 2 ^ e| ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int)) :
    (Float.Model.pack (normalize Format.binary64 m e zs)).toRat? =
      some (fl 53 ((m : Rat) * 2 ^ e)) := by
  rcases lt_trichotomy m 0 with hn | hz | hp
  · have hm : 0 < (-m).toNat := by omega
    have hc : ((-m).toNat : Rat) = -(m : Rat) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ -m))
    have hv : |(m : Rat) * 2 ^ e| = ((-m).toNat : Rat) * 2 ^ e := by
      rw [hc, abs_of_neg (mul_neg_of_neg_of_pos (by exact_mod_cast hn) (two_zpow_pos e))]
      ring
    have hs : (Sign.negative.apply (-m).toNat : Rat) * 2 ^ e = (m : Rat) * 2 ^ e := by
      simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, hc, neg_neg]
    have hr := round_normal .negative (-m).toNat e hm (by rwa [← hv]) (by rwa [← hv])
    rw [hs] at hr
    simpa only [normalize, Int.compare_eq_lt.mpr hn] using hr
  · subst m
    simp only [Int.cast_zero, zero_mul, abs_zero] at hlo
    exact False.elim ((not_le_of_gt (two_zpow_pos _)) hlo)
  · have hm : 0 < m.toNat := by omega
    have hc : (m.toNat : Rat) = (m : Rat) := by
      exact_mod_cast (Int.toNat_of_nonneg hp.le)
    have hv : |(m : Rat) * 2 ^ e| = (m.toNat : Rat) * 2 ^ e := by
      rw [hc, abs_of_pos (mul_pos (by exact_mod_cast hp) (two_zpow_pos e))]
    have hr := round_normal .positive m.toNat e hm (by rwa [← hv]) (by rwa [← hv])
    simpa only [normalize, Int.compare_eq_gt.mpr hp, Sign.apply, Int.cast_natCast, hc] using hr

private theorem fl_decoded (f : Float.Model) (s : Sign) (m : Nat) (e : Int)
    (hm : 0 < m) (hu : f.unpack = .finite s m e hm) :
    fl 53 ((s.apply m : Rat) * 2 ^ e) = (s.apply m : Rat) * 2 ^ e := by
  have hb := (unpack_finite_bounds f s m e hm hu).1
  apply fl_eq_self (by decide)
  refine ⟨s.apply m, e, ?_, rfl⟩
  cases s <;> simpa [Sign.apply] using (show (m : Int) < 2 ^ 53 by exact_mod_cast hb)

/-- In the frozen exact-result normal range, core binary64 addition agrees with Atlas `fl 53`.
The operand equations admit every finite encoding, including subnormals and signed zeros. -/
public theorem _root_.Float.Model.toRat?_add (a b : Float.Model) (x y : Rat)
    (hx : a.toRat? = some x) (hy : b.toRat? = some y)
    (hlo : (2 : Rat) ^ (-1022 : Int) ≤ |x + y|)
    (hhi : |x + y| ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int)) :
    (Float.Model.add a b).toRat? = some (fl 53 (x + y)) := by
  rw [toRat?_eq] at hx hy
  cases ha : a.unpack <;> cases hb : b.unpack <;>
    simp only [ha, hb] at hx hy <;> try contradiction
  all_goals
    simp only [Option.some.injEq] at hx hy
    subst x
    subst y
  case zero.zero s₁ s₂ =>
    simp only [zero_add, abs_zero] at hlo
    exact False.elim ((not_le_of_gt (two_zpow_pos _)) hlo)
  case zero.finite s₁ s₂ m e hm =>
    have hv := toRat?_pack_decoded b s₂ m e hm hb
    have hf := fl_decoded b s₂ m e hm hb
    simpa only [Float.Model.add, ha, hb, UnpackedFloat.add, zero_add, hf] using hv
  case finite.zero s₁ m e hm s₂ =>
    have hv := toRat?_pack_decoded a s₁ m e hm ha
    have hf := fl_decoded a s₁ m e hm ha
    simpa only [Float.Model.add, ha, hb, UnpackedFloat.add, add_zero, hf] using hv
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    let t := min e₁ e₂
    let M := s₁.apply (decreaseExponent m₁ e₁ t).1 + s₂.apply (decreaseExponent m₂ e₂ t).1
    have hv : (M : Rat) * 2 ^ t =
        (s₁.apply m₁ : Rat) * 2 ^ e₁ + (s₂.apply m₂ : Rat) * 2 ^ e₂ := by
      dsimp [M]
      rw [Int.cast_add, add_mul,
        decreaseExponent_signed_value s₁ m₁ e₁ t (min_le_left _ _),
        decreaseExponent_signed_value s₂ m₂ e₂ t (min_le_right _ _)]
    have h := normalize_normal M t .positive (by rwa [hv]) (by rwa [hv])
    rw [hv] at h
    simpa only [Float.Model.add, ha, hb, UnpackedFloat.add, M, t] using h

/-- In the frozen exact-result normal range, core binary64 multiplication agrees with Atlas
`fl 53`. The conclusion includes finiteness of the actual packed output. -/
public theorem _root_.Float.Model.toRat?_mul (a b : Float.Model) (x y : Rat)
    (hx : a.toRat? = some x) (hy : b.toRat? = some y)
    (hlo : (2 : Rat) ^ (-1022 : Int) ≤ |x * y|)
    (hhi : |x * y| ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int)) :
    (Float.Model.mul a b).toRat? = some (fl 53 (x * y)) := by
  rw [toRat?_eq] at hx hy
  cases ha : a.unpack <;> cases hb : b.unpack <;>
    simp only [ha, hb] at hx hy <;> try contradiction
  all_goals
    simp only [Option.some.injEq] at hx hy
    subst x
    subst y
  case zero.zero s₁ s₂ =>
    simp only [zero_mul, abs_zero] at hlo
    exact False.elim ((not_le_of_gt (two_zpow_pos _)) hlo)
  case zero.finite s₁ s₂ m e hm =>
    simp only [zero_mul, abs_zero] at hlo
    exact False.elim ((not_le_of_gt (two_zpow_pos _)) hlo)
  case finite.zero s₁ m e hm s₂ =>
    simp only [mul_zero, abs_zero] at hlo
    exact False.elim ((not_le_of_gt (two_zpow_pos _)) hlo)
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    have hv := mul_signed_value s₁ s₂ m₁ m₂ e₁ e₂
    have hl : (2 : Rat) ^ (-1022 : Int) ≤ (m₁ * m₂ : Nat) * (2 : Rat) ^ (e₁ + e₂) := by
      rw [← abs_sign_value (s₁ * s₂), hv]
      exact hlo
    have hh : ((m₁ * m₂ : Nat) : Rat) * (2 : Rat) ^ (e₁ + e₂) ≤
        (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int) := by
      rw [← abs_sign_value (s₁ * s₂), hv]
      exact hhi
    have hmlo : 2 ^ 52 ≤ m₁ * m₂ := by
      by_contra hsmall
      have hsmall' : m₁ * m₂ < 2 ^ 52 := by omega
      have h₁ := (unpack_finite_bounds a s₁ m₁ e₁ hm₁ ha).2.2.2
      have h₂ := (unpack_finite_bounds b s₂ m₂ e₂ hm₂ hb).2.2.2
      have hm₁le : m₁ ≤ m₁ * m₂ := Nat.le_mul_of_pos_right _ hm₂
      have hm₂le : m₂ ≤ m₁ * m₂ := Nat.le_mul_of_pos_left _ hm₁
      have he₁ : e₁ = -1074 := h₁.resolve_left (by omega)
      have he₂ : e₂ = -1074 := h₂.resolve_left (by omega)
      have hsmallRat : ((m₁ * m₂ : Nat) : Rat) < 2 ^ (52 : Nat) := by exact_mod_cast hsmall'
      have hprod : ((m₁ * m₂ : Nat) : Rat) * (2 : Rat) ^ (-2148 : Int) <
          (2 : Rat) ^ (-1022 : Int) := by
        calc ((m₁ * m₂ : Nat) : Rat) * (2 : Rat) ^ (-2148 : Int) <
            (2 : Rat) ^ (52 : Nat) * (2 : Rat) ^ (-2148 : Int) :=
              mul_lt_mul_of_pos_right hsmallRat (two_zpow_pos _)
          _ = (2 : Rat) ^ (-2096 : Int) := by
            rw [← zpow_natCast, ← zpow_add₀ (by decide : (2 : Rat) ≠ 0)]
            rfl
          _ < (2 : Rat) ^ (-1022 : Int) :=
            zpow_right_strictMono₀ (by decide : (1 : Rat) < 2) (by decide)
      rw [he₁, he₂] at hl
      exact (not_lt_of_ge hl) hprod
    have h := roundWithAccuracy_normal (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) hmlo hl hh
    rw [hv] at h
    simpa only [Float.Model.mul, ha, hb, UnpackedFloat.mul] using h

end Cslib.Algorithms.Lean.FloatingPoint
