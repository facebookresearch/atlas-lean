/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Init.Data.Float.Model.Float
public import Init.Data.Dyadic.Basic
import Mathlib.Data.Int.Log
import Mathlib.Data.Rat.Floor

/-!
# Rational values of the core binary64 model

Finite values, including both signed zeros, have an exact rational value.
NaN and infinities have no rational value. This is a value interpretation,
not a specification of arithmetic or a claim about hardware conformance.
-/

@[expose] public section

namespace Float.Model

/-- The exact rational value, or `none` for NaN and either infinity. -/
def toRat? (f : Float.Model) : Option Rat :=
  match f.unpack with
  | .notANumber | .infinity _ => none
  | .zero _ => some 0
  | .finite s m e _ => some (Dyadic.ofIntWithPrec (s.apply m) (-e)).toRat

/-- Characterization by the actual unpacked sign, mantissa and exponent. -/
theorem toRat?_eq (f : Float.Model) :
    f.toRat? = match f.unpack with
      | .notANumber | .infinity _ => none
      | .zero _ => some 0
      | .finite s m e _ => some ((s.apply m : Rat) * 2 ^ e) := by
  cases h : f.unpack <;>
    simp [toRat?, h, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

/-- Definedness is exactly the core model's finiteness test. -/
@[simp] theorem isSome_toRat? (f : Float.Model) :
    f.toRat?.isSome = f.isFinite := by
  cases h : f.unpack <;> simp [toRat?, isFinite, UnpackedFloat.isFinite, h]

open UnpackedFloat

/-- The fractional residual after the integral mantissa is recorded by the two core bits. -/
private def HasResidual (x : Rat) (em : ExtendedMantissa) : Prop :=
  (em.mantissa : Rat) ≤ x ∧ x < em.mantissa + 1 ∧
  em.roundBit = decide ((1 : Rat) / 2 ≤ x - em.mantissa) ∧
  em.stickyBit = decide (x - em.mantissa ≠ 0 ∧ x - em.mantissa ≠ 1 / 2)

private theorem hasResidual_exact (m : Nat) :
    HasResidual (m : Rat) (ExtendedMantissa.ofMantissaAndAccuracy m .exact) := by
  simp [HasResidual, ExtendedMantissa.ofMantissaAndAccuracy]

private theorem hasResidual_bits {x : Rat} {em : ExtendedMantissa}
    (h : HasResidual x em) :
    (em.roundBit || em.stickyBit) = decide (x - em.mantissa ≠ 0) := by
  rw [h.2.2.1, h.2.2.2]
  by_cases hz : x - em.mantissa = 0
  · simp [hz]
  by_cases hh : x - em.mantissa = 1 / 2
  · simp [hh]
  simp only [ne_eq, hz, hh, not_false_eq_true, and_self, decide_true, Bool.or_true]

private theorem hasResidual_shiftRightOne {x : Rat} {em : ExtendedMantissa}
    (h : HasResidual x em) : HasResidual (x / 2) em.shiftRightOne := by
  have hb := hasResidual_bits h
  obtain ⟨m, r, s⟩ := em
  obtain ⟨hlo, hhi, hr, hs⟩ := h
  change (m : Rat) ≤ x at hlo
  change x < (m : Rat) + 1 at hhi
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm with hm | hm
  · have hd : (m : Rat) = 2 * (m / 2 : Nat) := by
      exact_mod_cast (show m = 2 * (m / 2) by omega)
    refine ⟨by dsimp [ExtendedMantissa.shiftRightOne]; linarith,
      by dsimp [ExtendedMantissa.shiftRightOne]; linarith, ?_, ?_⟩
    · have hlt : ¬(1 : Rat) / 2 ≤ x / 2 - (m / 2 : Nat) := by linarith
      simp only [ExtendedMantissa.shiftRightOne, hm, hlt, decide_false]
      decide
    · change (r || s) = decide (x / 2 - (m / 2 : Nat) ≠ 0 ∧
        x / 2 - (m / 2 : Nat) ≠ 1 / 2)
      rw [hb]
      congr 1
      apply propext
      constructor
      · intro hz
        constructor <;> intro he <;> apply hz <;> linarith
      · intro hz he
        apply hz.1
        linarith
  · have hd : (m : Rat) = 2 * (m / 2 : Nat) + 1 := by
      exact_mod_cast (show m = 2 * (m / 2) + 1 by omega)
    refine ⟨by dsimp [ExtendedMantissa.shiftRightOne]; linarith,
      by dsimp [ExtendedMantissa.shiftRightOne]; linarith, ?_, ?_⟩
    · have hle : (1 : Rat) / 2 ≤ x / 2 - (m / 2 : Nat) := by linarith
      simp only [ExtendedMantissa.shiftRightOne, hm, hle, decide_true]
      decide
    · change (r || s) = decide (x / 2 - (m / 2 : Nat) ≠ 0 ∧
        x / 2 - (m / 2 : Nat) ≠ 1 / 2)
      rw [hb]
      congr 1
      apply propext
      constructor
      · intro hz
        constructor <;> intro he <;> apply hz <;> linarith
      · intro hz he
        apply hz.2
        linarith

private theorem hasResidual_shiftRight (m n : Nat) :
    HasResidual ((m : Rat) / 2 ^ n)
      (ExtendedMantissa.ofMantissaAndAccuracy m .exact >>> n) := by
  change HasResidual _ (n.repeat ExtendedMantissa.shiftRightOne _)
  induction n with
  | zero => simpa [Nat.repeat] using hasResidual_exact m
  | succ n ih =>
    simpa [Nat.repeat, pow_succ, div_mul_eq_div_div] using
      hasResidual_shiftRightOne ih

private theorem log_nat_mul_two_zpow (m : Nat) (hm : 0 < m) (e : Int) :
    Int.log 2 ((m : Rat) * 2 ^ e) = (m.log2 : Int) + e := by
  have hm' : (0 : Rat) < m := by exact_mod_cast hm
  have hp := zpow_pos (by decide : (0 : Rat) < 2) e
  have hlo : (2 : Rat) ^ m.log2 ≤ m := by
    exact_mod_cast (Nat.log2_eq_log_two (n := m) ▸ Nat.pow_log_le_self 2 hm.ne')
  have hhi : (m : Rat) < 2 ^ (m.log2 + 1) := by
    exact_mod_cast (Nat.log2_eq_log_two (n := m) ▸ Nat.lt_pow_succ_log_self (by decide : 1 < 2) m)
  have hl : (2 : Rat) ^ ((m.log2 : Int) + e) ≤ m * 2 ^ e := by
    rw [zpow_add₀ two_ne_zero, zpow_natCast]
    exact mul_le_mul_of_nonneg_right hlo hp.le
  have hu : (m : Rat) * 2 ^ e < 2 ^ ((m.log2 : Int) + e + 1) := by
    calc (m : Rat) * 2 ^ e < 2 ^ (m.log2 + 1) * 2 ^ e := mul_lt_mul_of_pos_right hhi hp
      _ = 2 ^ ((m.log2 : Int) + e + 1) := by
        rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
        congr 1
        push_cast
        ring
  have hpos := mul_pos hm' hp
  have h₁ := (Int.zpow_le_iff_le_log (by decide : 1 < 2) hpos).mp hl
  have h₂ := (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hpos).mp hu
  omega


private theorem unpackSign_packComponents {spec : Format} {s ev mv} :
    UnpackedFloat.unpackSign (UnpackedFloat.packComponents spec s ev mv) = s.toBitVec := by
  ext i hi
  have hi' : i = 0 := by omega
  subst i
  simp [UnpackedFloat.unpackSign, UnpackedFloat.packComponents,
    BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getElem_append]

private theorem sign_ofBitVec_toBitVec (s : UnpackedFloat.Sign) :
    Sign.ofBitVec s.toBitVec = s := by
  cases s <;> decide

private theorem toRat?_pack_normal (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hlo : 2 ^ 52 ≤ m) (hhi : m < 2 ^ 53) (he₁ : -1074 ≤ e) (he₂ : e ≤ 971) :
    (Float.Model.pack (.finite s m e hm)).toRat? = some ((s.apply m : Rat) * 2 ^ e) := by
  have hlog : m.log2 = 52 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  have hb : 0 < (e + 1075).toNat ∧ (e + 1075).toNat < 2047 := by omega
  have hbmax : BitVec.ofNat 11 (e + 1023 + 52).toNat ≠ -1#11 := by
    intro h
    have ht := congrArg BitVec.toNat h
    norm_num at ht
    omega
  have hbzero : BitVec.ofNat 11 (e + 1023 + 52).toNat ≠ 0#11 := by
    intro h
    have ht := congrArg BitVec.toNat h
    norm_num at ht
    omega
  rw [toRat?_eq]
  simp only [Float.Model.unpack, Float.Model.pack, UInt64.toBitVec_ofBitVec,
    UnpackedFloat.pack, hlog, Format.binary64, Format.exponentBias, Format.mantissaBits]
  have hb' : ¬2047 ≤ (e + 1023 + 52).toNat := by omega
  norm_num [hb', UnpackedFloat.unpack, unpackSign_packComponents, sign_ofBitVec_toBitVec,
    hbmax, hbzero, Format.exponentBias]
  have hor : 4503599627370496 ||| m % 4503599627370496 =
      4503599627370496 + m % 4503599627370496 := by
    simpa using (Nat.two_pow_add_eq_or_of_lt
      (i := 52) (Nat.mod_lt m (by decide : 0 < 2 ^ 52)) 1).symm
  have hm' : 4503599627370496 ||| m % 4503599627370496 = m := by
    rw [hor]
    norm_num at hlo hhi
    omega
  have he' : max (e + 1023 + 52) 0 % 2048 - 1075 = e := by omega
  rw [hm', he']

private theorem decreaseExponent_value (m : Nat) (e target : Int) :
    ((decreaseExponent m e target).1 : Rat) * 2 ^ (decreaseExponent m e target).2 =
      (m : Rat) * 2 ^ e := by
  simp only [decreaseExponent, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [zpow_sub₀ (by decide : (2 : Rat) ≠ 0), zpow_natCast]
  field_simp

private theorem unpack_finite_bounds (f : Float.Model) (s : Sign) (m : Nat) (e : Int)
    (hm : 0 < m) (hu : f.unpack = .finite s m e hm) :
    m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (2 ^ 52 ≤ m ∨ e = -1074) := by
  have hmv : (UnpackedFloat.unpackMantissa (spec := Format.binary64) f.toBits.toBitVec).toNat <
      2 ^ 52 := BitVec.isLt _
  have hev : (UnpackedFloat.unpackExponent (spec := Format.binary64) f.toBits.toBitVec).toNat <
      2048 := BitVec.isLt _
  unfold Float.Model.unpack UnpackedFloat.unpack at hu
  dsimp only at hu
  split_ifs at hu <;> cases hu
  · rename_i hmax hz hn
    norm_num [hz, Format.exponentBias]
    omega
  · rename_i hmax hz
    rw [← BitVec.toNat_inj] at hmax hz
    norm_num at hmax hz
    have hor : 4503599627370496 |||
        (unpackMantissa (spec := Format.binary64) f.toBits.toBitVec).toNat =
        4503599627370496 +
          (unpackMantissa (spec := Format.binary64) f.toBits.toBitVec).toNat := by
      simpa using (Nat.two_pow_add_eq_or_of_lt (i := 52) hmv 1).symm
    norm_num [BitVec.toNat_append, Nat.shiftLeft_eq, Format.exponentBias, hor]
    omega

private theorem decreaseExponent_mantissa_ge (m : Nat) (e target : Int) (hm : 0 < m)
    (ht : target ≤ (m.log2 : Int) + e - 52) :
    2 ^ 52 ≤ (decreaseExponent m e target).1 := by
  have hn : 52 ≤ m.log2 + (e - target).toNat := by omega
  have hpow : 2 ^ 52 ≤ 2 ^ (m.log2 + (e - target).toNat) :=
    Nat.pow_le_pow_right (by decide) hn
  have hbase : 2 ^ m.log2 ≤ m := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hm.ne'
  simp only [decreaseExponent, Nat.shiftLeft_eq]
  rw [pow_add] at hpow
  exact hpow.trans (Nat.mul_le_mul_right _ hbase)

private theorem toRat?_pack_subnormal (s : Sign) (m : Nat) (hm : 0 < m) (hhi : m < 2 ^ 52) :
    (Float.Model.pack (.finite s m (-1074) hm)).toRat? =
      some ((s.apply m : Rat) * 2 ^ (-1074 : Int)) := by
  have hlog : m.log2 + 1 ≠ 53 := by
    have hh : m.log2 < 52 := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_of_lt_pow hm.ne' hhi
    omega
  have hz : BitVec.ofNat 52 m ≠ 0#52 := by
    intro h
    have hh := congrArg BitVec.toNat h
    have hmzero : m = 0 := by
      simpa only [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt hhi] using hh
    exact hm.ne' hmzero
  rw [toRat?_eq]
  norm_num [Float.Model.unpack, Float.Model.pack, UnpackedFloat.pack, UnpackedFloat.unpack,
    Format.exponentBias, Format.mantissaBits, hlog, hz, Nat.mod_eq_of_lt hhi,
    unpackSign_packComponents, sign_ofBitVec_toBitVec]
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg m) (by exact_mod_cast hhi)]

private theorem toRat?_pack_decoded (f : Float.Model) (s : Sign) (m : Nat) (e : Int)
    (hm : 0 < m) (hu : f.unpack = .finite s m e hm) :
    (Float.Model.pack (.finite s m e hm)).toRat? = some ((s.apply m : Rat) * 2 ^ e) := by
  obtain ⟨hmhi, helo, hehi, hn⟩ := unpack_finite_bounds f s m e hm hu
  by_cases hmlo : 2 ^ 52 ≤ m
  · exact toRat?_pack_normal s m e hm hmlo hmhi helo hehi
  · have he : e = -1074 := hn.resolve_left hmlo
    subst e
    exact toRat?_pack_subnormal s m hm (by omega)

private theorem decreaseExponent_signed_value (s : Sign) (m : Nat) (e target : Int)
    (ht : target ≤ e) :
    (s.apply (decreaseExponent m e target).1 : Rat) * 2 ^ target =
      (s.apply m : Rat) * 2 ^ e := by
  have he : (decreaseExponent m e target).2 = target := by
    dsimp [decreaseExponent]
    omega
  have hv := decreaseExponent_value m e target
  rw [he] at hv
  cases s <;> simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul]
  · exact congrArg Neg.neg hv
  · exact hv

private theorem abs_sign_value (s : Sign) (m : Nat) (e : Int) :
    |(s.apply m : Rat) * 2 ^ e| = (m : Rat) * 2 ^ e := by
  cases s <;>
    simp [Sign.apply, abs_mul, abs_of_pos (zpow_pos (by decide : (0 : Rat) < 2) e)]

private theorem mul_signed_value (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) :
    ((s₁ * s₂).apply (m₁ * m₂ : Nat) : Rat) * 2 ^ (e₁ + e₂) =
      ((s₁.apply m₁ : Rat) * 2 ^ e₁) * ((s₂.apply m₂ : Rat) * 2 ^ e₂) := by
  cases s₁ <;> cases s₂ <;>
    simp [Sign.apply, zpow_add₀ (by decide : (2 : Rat) ≠ 0)] <;> ring

end Float.Model
