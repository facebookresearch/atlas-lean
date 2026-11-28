/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Numerical.FixedPointFIR
public import MathlibExt.Analysis.Numerical.OrderedDotProductError
public import MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Fixed-point FIR filter on signed machine words

The integer fixed-point FIR filter of
`CSLibExt.Algorithms.Numerical.FixedPointFIR` is implemented on signed
two's complement words `BitVec w`, decoded by `BitVec.toInt`.

Taps, inputs and the accumulator are width-`w` words. Each product and
partial sum is formed exactly at the intermediate width `2 * w + s + 1`,
where no value can wrap, then narrowed back to width `w` by saturation.
Rounding adds `2 ^ s / 2` one bit wider than the intermediate width, so
the addition cannot wrap, and shifts right arithmetically by `s`. The
range test compares against the sign-extended `BitVec.intMin w` and
`BitVec.intMax w`. Scale, rounding, flag order and zero initialization
match the integer fold.

## Main results

* `toInt_wordRoundHalfUpShift`: word rounding decodes to the integer
  round half up for every intermediate word.
* `wordStep_refines`: one word step decodes to the integer step, with an
  equal overflow flag, for every accumulator, flag and operand pair.
* `outOfRange_add_eq_saddOverflow`: when the rounded product fits, the
  partial-sum range test is `BitVec.saddOverflow` at width `w`.
* `wordStep_eq_add_of_no_overflow`: a step with no overflow is the plain
  width-`w` sum.
* `wordFold_refines`, `wordCode_refines`: the fold and the filter output
  agree with the integer filter, flags included, on every trace,
  overflowing ones too.
* `wordFir_correct`: the refinement together with the integer filter's
  ordered dot-product error bound for the decoded word output.

The intermediate width is what makes overflowing traces agree: the
integer fold saturates the sum of the accumulator and the unsaturated
product, so a product that wrapped or saturated at width `w` would
disagree with it.
-/

@[expose] public section

namespace CSLibExt.Algorithms.Numerical.FixedPointFIRWordRefinement

open MathlibExt.Analysis.Numerical
open CSLibExt.Algorithms.Numerical.FixedPointFIR

/-- The intermediate width at which products and partial sums are
formed without wrapping. -/
def wideWidth (w s : ℕ) : ℕ :=
  2 * w + s + 1

/-- Sign-extend a width-`w` word to the intermediate width. -/
def widen (w s : ℕ) (v : BitVec w) : BitVec (wideWidth w s) :=
  v.signExtend (wideWidth w s)

/-- The exact signed product of two width-`w` words, at the intermediate
width. -/
def wordProduct (w s : ℕ) (hk xk : BitVec w) : BitVec (wideWidth w s) :=
  widen w s hk * widen w s xk

/-- Round half up on an intermediate word: add `2 ^ s / 2` one bit wider,
so the addition cannot wrap, shift right arithmetically by `s`, and narrow
back. The rounded value always fits the intermediate width. -/
def wordRoundHalfUpShift (w s : ℕ) (n : BitVec (wideWidth w s)) :
    BitVec (wideWidth w s) :=
  ((n.signExtend (wideWidth w s + 1)
      + BitVec.ofNat (wideWidth w s + 1) (2 ^ s / 2)).sshiftRight s).setWidth
    (wideWidth w s)

/-- The least signed width-`w` word at the intermediate width. -/
def wideMin (w s : ℕ) : BitVec (wideWidth w s) :=
  widen w s (BitVec.intMin w)

/-- The greatest signed width-`w` word at the intermediate width. -/
def wideMax (w s : ℕ) : BitVec (wideWidth w s) :=
  widen w s (BitVec.intMax w)

/-- An intermediate word lies outside the signed width-`w` range. -/
def outOfRange (w s : ℕ) (v : BitVec (wideWidth w s)) : Bool :=
  v.slt (wideMin w s) || (wideMax w s).slt v

/-- Saturating narrowing of an intermediate word to width `w`. -/
def saturateWord (w s : ℕ) (v : BitVec (wideWidth w s)) : BitVec w :=
  if v.slt (wideMin w s) then BitVec.intMin w
  else if (wideMax w s).slt v then BitVec.intMax w
  else v.setWidth w

/-- One word fold step: rounded exact product, exact accumulation,
saturating narrowing, and the overflow flag in the integer step's order
(previous flag, then the partial sum, then the product). -/
def wordStep (w s : ℕ) (acc : BitVec w) (flag : Bool) (hk xk : BitVec w) :
    BitVec w × Bool :=
  let prod := wordRoundHalfUpShift w s (wordProduct w s hk xk)
  let raw := widen w s acc + prod
  (saturateWord w s raw, flag || outOfRange w s raw || outOfRange w s prod)

/-- Zero-initialized left fold of word steps over the first `n` taps. -/
def wordFold (w s : ℕ) (h x : ℕ → BitVec w) : ℕ → BitVec w × Bool
  | 0 => (0#w, false)
  | n + 1 =>
    let prev := wordFold w s h x n
    wordStep w s prev.1 prev.2 (h n) (x n)

/-- Output word of the `m`-tap word filter. -/
def wordCode {m : ℕ} (w s : ℕ) (h x : Fin m → BitVec w) : BitVec w :=
  (wordFold w s (fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0#w)
    (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0#w) m).1

/-- Overflow flag of the `m`-tap word filter. -/
def wordOverflow {m : ℕ} (w s : ℕ) (h x : Fin m → BitVec w) : Bool :=
  (wordFold w s (fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0#w)
    (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0#w) m).2

/-- Decode a width-`w` word at scale `2 ^ s`: two's complement value,
then the integer decoding. -/
noncomputable def decodeWord {w : ℕ} (s : ℕ) (v : BitVec w) : ℝ :=
  decode s v.toInt

/-! ### Per-operation decoding -/

/-- `Int.bmod` is the identity on the signed range of width `W`. -/
private theorem bmod_eq_of_signed_range {W : ℕ} (hW : 1 ≤ W) {n : ℤ}
    (hlo : -(2 : ℤ) ^ (W - 1) ≤ n) (hhi : n < (2 : ℤ) ^ (W - 1)) :
    n.bmod ((2 : ℕ) ^ W) = n := by
  have hWeq : (2 : ℤ) ^ W = 2 * (2 : ℤ) ^ (W - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hW]
    rw [pow_succ]
    ring
  have hcast : (((2 : ℕ) ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by
    norm_cast
  apply Int.bmod_eq_of_le
  · rw [hcast, hWeq]
    omega
  · rw [hcast, hWeq]
    omega

private theorem wideWidth_ge_one (w s : ℕ) : 1 ≤ wideWidth w s := by
  unfold wideWidth
  omega

private theorem wideWidth_sub_one (w s : ℕ) :
    wideWidth w s - 1 = 2 * w + s := by
  unfold wideWidth
  omega

/-- Sign extension preserves the decoded value. -/
theorem toInt_widen (w s : ℕ) (v : BitVec w) :
    (widen w s v).toInt = v.toInt := by
  unfold widen
  apply BitVec.toInt_signExtend_of_le
  unfold wideWidth
  omega

/-- The wide bounds decode to the signed code range. -/
private theorem toInt_wideMin (w s : ℕ) (hw : 1 ≤ w) :
    (wideMin w s).toInt = SaturatingRoundHalfUp.signedMinCode w := by
  unfold wideMin SaturatingRoundHalfUp.signedMinCode
  rw [toInt_widen]
  exact BitVec.toInt_intMin_of_pos (by omega : 0 < w)

private theorem toInt_wideMax (w s : ℕ) (hw : 1 ≤ w) :
    (wideMax w s).toInt = SaturatingRoundHalfUp.signedMaxCode w := by
  have _ := hw
  unfold wideMax SaturatingRoundHalfUp.signedMaxCode
  rw [toInt_widen]
  exact BitVec.toInt_intMax

/-- Narrowing is exact when the value is in the signed width-`w` range. -/
private theorem toInt_setWidth_of_mem (w s : ℕ) (hw : 1 ≤ w)
    (v : BitVec (wideWidth w s))
    (h1 : SaturatingRoundHalfUp.signedMinCode w ≤ v.toInt)
    (h2 : v.toInt ≤ SaturatingRoundHalfUp.signedMaxCode w) :
    (v.setWidth w).toInt = v.toInt := by
  have hle : w ≤ wideWidth w s := by unfold wideWidth; omega
  have hdvd : (2 : ℕ) ^ w ∣ (2 : ℕ) ^ wideWidth w s :=
    Nat.pow_dvd_pow _ hle
  have h1' : -(2 : ℤ) ^ (w - 1) ≤ v.toInt := by
    unfold SaturatingRoundHalfUp.signedMinCode at h1; exact h1
  have h2' : v.toInt < (2 : ℤ) ^ (w - 1) := by
    unfold SaturatingRoundHalfUp.signedMaxCode at h2
    have : v.toInt ≤ (2 : ℤ) ^ (w - 1) - 1 := h2
    omega
  have hset : (v.setWidth w).toInt = ((v.toNat : ℕ) : ℤ).bmod ((2 : ℕ) ^ w) :=
    BitVec.toInt_setWidth v
  have hto : v.toInt = ((v.toNat : ℕ) : ℤ).bmod ((2 : ℕ) ^ wideWidth w s) :=
    BitVec.toInt_eq_toNat_bmod v
  have hbmod : (v.toInt).bmod ((2 : ℕ) ^ w) = v.toInt :=
    bmod_eq_of_signed_range hw h1' h2'
  rw [hset]
  have hbb : ((v.toNat : ℕ) : ℤ).bmod ((2 : ℕ) ^ w)
      = (v.toInt).bmod ((2 : ℕ) ^ w) := by
    rw [hto]
    exact (Int.bmod_bmod_of_dvd hdvd).symm
  rw [hbb, hbmod]

/-- Narrowing by one bit is exact when the value fits the narrower signed
range. -/
private theorem toInt_setWidth_succ {W : ℕ} (hW : 1 ≤ W) (v : BitVec (W + 1))
    (hlo : -(2 : ℤ) ^ (W - 1) ≤ v.toInt) (hhi : v.toInt < (2 : ℤ) ^ (W - 1)) :
    (v.setWidth W).toInt = v.toInt := by
  have hdvd : (2 : ℕ) ^ W ∣ (2 : ℕ) ^ (W + 1) := Nat.pow_dvd_pow _ (by omega)
  have hset : (v.setWidth W).toInt = ((v.toNat : ℕ) : ℤ).bmod ((2 : ℕ) ^ W) :=
    BitVec.toInt_setWidth v
  have hto : v.toInt = ((v.toNat : ℕ) : ℤ).bmod ((2 : ℕ) ^ (W + 1)) :=
    BitVec.toInt_eq_toNat_bmod v
  have hbb : ((v.toNat : ℕ) : ℤ).bmod ((2 : ℕ) ^ W)
      = (v.toInt).bmod ((2 : ℕ) ^ W) := by
    rw [hto]
    exact (Int.bmod_bmod_of_dvd hdvd).symm
  rw [hset, hbb]
  exact bmod_eq_of_signed_range hW hlo hhi

/-- The rounding offset word, one bit wider than the intermediate width,
decodes to `2 ^ s / 2`. -/
private theorem toInt_offset (w s : ℕ) :
    (BitVec.ofNat (wideWidth w s + 1) (2 ^ s / 2)).toInt
      = ((2 ^ s / 2 : ℕ) : ℤ) := by
  rw [BitVec.toInt_ofNat']
  apply bmod_eq_of_signed_range (by omega : 1 ≤ wideWidth w s + 1)
  · have hx : (0 : ℤ) ≤ ((2 ^ s / 2 : ℕ) : ℤ) := Nat.cast_nonneg _
    have hpos : (0 : ℤ) < (2 : ℤ) ^ (wideWidth w s + 1 - 1) := by positivity
    omega
  · have hle : ((2 ^ s / 2 : ℕ) : ℤ) ≤ ((2 ^ s : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_le_self _ _
    have hlt : (2 : ℤ) ^ s < (2 : ℤ) ^ (wideWidth w s + 1 - 1) := by
      apply pow_lt_pow_right₀ (by norm_num)
      unfold wideWidth
      omega
    have hcast : (((2 ^ s : ℕ)) : ℤ) = (2 : ℤ) ^ s := by norm_cast
    omega

/-- Rounding never exceeds a nonnegative upper bound of its input. -/
private theorem roundHalfUpShift_le_of_le (s : ℕ) (p M : ℤ) (hM : 0 ≤ M)
    (hp : p ≤ M) : roundHalfUpShift s p ≤ M := by
  unfold roundHalfUpShift
  set D : ℤ := (2 : ℤ) ^ s with hD
  set h : ℤ := D / 2 with hh
  set q : ℤ := (p + h) / D with hq
  set r : ℤ := (p + h) % D with hr
  have hDpos : (0 : ℤ) < D := by rw [hD]; positivity
  have hD1 : (1 : ℤ) ≤ D := by omega
  have hqr : D * q + r = p + h := Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hDpos)
  have hhD : h < D := by rw [hh]; omega
  by_contra hcon
  push Not at hcon
  have hDq : D * (M + 1) ≤ D * q := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hDpos)
    omega
  have hDM : M ≤ D * M := by
    have hnn : (0 : ℤ) ≤ M * (D - 1) := mul_nonneg hM (by omega)
    have hexp : M * (D - 1) = D * M - M := by ring
    omega
  have hexp2 : D * (M + 1) = D * M + D := by ring
  omega

/-- Rounding never goes below the negation of a nonnegative bound. -/
private theorem le_roundHalfUpShift_of_le (s : ℕ) (p M : ℤ) (hM : 0 ≤ M)
    (hp : -M ≤ p) : -M ≤ roundHalfUpShift s p := by
  unfold roundHalfUpShift
  set D : ℤ := (2 : ℤ) ^ s with hD
  set h : ℤ := D / 2 with hh
  set q : ℤ := (p + h) / D with hq
  set r : ℤ := (p + h) % D with hr
  have hDpos : (0 : ℤ) < D := by rw [hD]; positivity
  have hD1 : (1 : ℤ) ≤ D := by omega
  have hqr : D * q + r = p + h := Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hDpos)
  have hr1 : r < D := Int.emod_lt_of_pos _ hDpos
  have hh0 : 0 ≤ h := by rw [hh]; omega
  by_contra hcon
  push Not at hcon
  have hDq : D * q ≤ D * (-M - 1) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hDpos)
    omega
  have hDM : M ≤ D * M := by
    have hnn : (0 : ℤ) ≤ M * (D - 1) := mul_nonneg hM (by omega)
    have hexp : M * (D - 1) = D * M - M := by ring
    omega
  have hexp2 : D * (-M - 1) = -(D * M) - D := by ring
  omega

/-- Widened accumulation is exact when the sum is in the wide signed range. -/
private theorem toInt_widen_add (w s : ℕ) (acc : BitVec w)
    (prod : BitVec (wideWidth w s))
    (hlo : -(2 : ℤ) ^ (wideWidth w s - 1) ≤ acc.toInt + prod.toInt)
    (hhi : acc.toInt + prod.toInt < (2 : ℤ) ^ (wideWidth w s - 1)) :
    (widen w s acc + prod).toInt = acc.toInt + prod.toInt := by
  rw [BitVec.toInt_add, toInt_widen]
  exact bmod_eq_of_signed_range (wideWidth_ge_one w s) hlo hhi

/-- Narrowing a widened word back to `w` gives the original word. -/
private theorem setWidth_widen (w s : ℕ) (acc : BitVec w) :
    (widen w s acc).setWidth w = acc := by
  apply BitVec.eq_of_toNat_eq
  have hle : w ≤ wideWidth w s := by unfold wideWidth; omega
  have hset : (acc.setWidth (wideWidth w s)).toNat = acc.toNat :=
    BitVec.toNat_setWidth_of_le hle
  have hsign : (widen w s acc).toNat
      = acc.toNat
        + (if acc.msb = true then 2 ^ wideWidth w s - 2 ^ w else 0) := by
    unfold widen
    rw [BitVec.toNat_signExtend, hset]
  have hmod : ((widen w s acc).setWidth w).toNat
      = (widen w s acc).toNat % 2 ^ w := BitVec.toNat_setWidth _ _
  rw [hmod, hsign]
  by_cases hmsb : acc.msb = true
  · rw [ite_eq_left hmsb]
    have hdvd : 2 ^ w ∣ 2 ^ wideWidth w s - 2 ^ w :=
      Nat.dvd_sub (Nat.pow_dvd_pow _ hle) dvd_rfl
    have he0 : (2 ^ wideWidth w s - 2 ^ w) % 2 ^ w = 0 :=
      Nat.mod_eq_zero_of_dvd hdvd
    have hlt : acc.toNat % 2 ^ w = acc.toNat := Nat.mod_eq_of_lt acc.isLt
    calc (acc.toNat + (2 ^ wideWidth w s - 2 ^ w)) % 2 ^ w
        = (acc.toNat % 2 ^ w + (2 ^ wideWidth w s - 2 ^ w) % 2 ^ w) % 2 ^ w := by
          rw [Nat.add_mod]
      _ = acc.toNat := by rw [he0, hlt, Nat.add_zero, hlt]
  · rw [ite_eq_right hmsb, Nat.add_zero]
    exact Nat.mod_eq_of_lt acc.isLt

/-- The intermediate product is the exact integer product. -/
theorem toInt_wordProduct (w s : ℕ) (hw : 1 ≤ w) (hk xk : BitVec w) :
    (wordProduct w s hk xk).toInt = hk.toInt * xk.toInt := by
  unfold wordProduct
  rw [BitVec.toInt_mul, toInt_widen, toInt_widen]
  apply bmod_eq_of_signed_range (wideWidth_ge_one w s)
  · have hlo := BitVec.le_toInt_mul_toInt (x := hk) (y := xk)
    have hmono : (2 : ℤ) ^ (w * 2 - 2) ≤ (2 : ℤ) ^ (wideWidth w s - 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [wideWidth_sub_one]
      omega
    have hneg : -(2 : ℤ) ^ (wideWidth w s - 1) ≤ -(2 : ℤ) ^ (w * 2 - 2) :=
      neg_le_neg hmono
    exact le_trans hneg hlo
  · have hhi := BitVec.toInt_mul_toInt_le (x := hk) (y := xk)
    have hmono : (2 : ℤ) ^ (w * 2 - 2) < (2 : ℤ) ^ (wideWidth w s - 1) := by
      apply pow_lt_pow_right₀ (by norm_num)
      rw [wideWidth_sub_one]
      omega
    exact lt_of_le_of_lt hhi hmono

/-- Rounding decodes to the integer round half up of the decoded input, for
every intermediate word. -/
theorem toInt_wordRoundHalfUpShift (w s : ℕ) (n : BitVec (wideWidth w s)) :
    (wordRoundHalfUpShift w s n).toInt = roundHalfUpShift s n.toInt := by
  have hK : wideWidth w s - 1 = 2 * w + s := wideWidth_sub_one w s
  have hK1 : wideWidth w s + 1 - 1 = 2 * w + s + 1 := by unfold wideWidth; omega
  have hlo := BitVec.le_toInt n
  have hhi := BitVec.toInt_lt (x := n)
  rw [hK] at hlo hhi
  have hext : (n.signExtend (wideWidth w s + 1)).toInt = n.toInt :=
    BitVec.toInt_signExtend_of_le (by omega)
  have hoff := toInt_offset w s
  have hh0 : (0 : ℤ) ≤ ((2 ^ s / 2 : ℕ) : ℤ) := Nat.cast_nonneg _
  have hhK : ((2 ^ s / 2 : ℕ) : ℤ) ≤ (2 : ℤ) ^ (2 * w + s) := by
    have h1 : ((2 ^ s / 2 : ℕ) : ℤ) ≤ ((2 ^ s : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_le_self _ _
    have h2 : (((2 ^ s : ℕ)) : ℤ) = (2 : ℤ) ^ s := by norm_cast
    have h3 : (2 : ℤ) ^ s ≤ (2 : ℤ) ^ (2 * w + s) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  have hpow : (2 : ℤ) ^ (2 * w + s + 1) = 2 * (2 : ℤ) ^ (2 * w + s) := by
    rw [pow_succ]
    ring
  have hadd : (n.signExtend (wideWidth w s + 1)
      + BitVec.ofNat (wideWidth w s + 1) (2 ^ s / 2)).toInt
      = n.toInt + ((2 ^ s / 2 : ℕ) : ℤ) := by
    rw [BitVec.toInt_add, hext, hoff]
    apply bmod_eq_of_signed_range (by omega : 1 ≤ wideWidth w s + 1)
    · rw [hK1, hpow]
      omega
    · rw [hK1, hpow]
      omega
  have hshift : ((n.signExtend (wideWidth w s + 1)
      + BitVec.ofNat (wideWidth w s + 1) (2 ^ s / 2)).sshiftRight s).toInt
      = roundHalfUpShift s n.toInt := by
    rw [BitVec.toInt_sshiftRight, hadd, Int.shiftRight_eq_div_pow]
    have hx : (((2 ^ s / 2 : ℕ)) : ℤ) = (2 : ℤ) ^ s / 2 := by
      rw [Int.natCast_ediv]
      norm_cast
    have hD : (((2 ^ s : ℕ)) : ℤ) = (2 : ℤ) ^ s := by norm_cast
    rw [hx, hD]
    rfl
  have hM : (0 : ℤ) < (2 : ℤ) ^ (2 * w + s) := by positivity
  have hrhi : roundHalfUpShift s n.toInt ≤ (2 : ℤ) ^ (2 * w + s) - 1 :=
    roundHalfUpShift_le_of_le s n.toInt ((2 : ℤ) ^ (2 * w + s) - 1) (by omega)
      (by omega)
  have hrlo : -(2 : ℤ) ^ (2 * w + s) ≤ roundHalfUpShift s n.toInt :=
    le_roundHalfUpShift_of_le s n.toInt ((2 : ℤ) ^ (2 * w + s)) (le_of_lt hM) hlo
  unfold wordRoundHalfUpShift
  rw [toInt_setWidth_succ (wideWidth_ge_one w s) _
    (by rw [hK, hshift]; exact hrlo) (by rw [hK, hshift]; omega), hshift]

/-- Rounding the intermediate product decodes to the integer rounding of
the integer product. -/
theorem toInt_wordRoundHalfUpShift_wordProduct (w s : ℕ) (hw : 1 ≤ w)
    (hk xk : BitVec w) :
    (wordRoundHalfUpShift w s (wordProduct w s hk xk)).toInt
      = roundHalfUpShift s (hk.toInt * xk.toInt) := by
  rw [toInt_wordRoundHalfUpShift, toInt_wordProduct w s hw]

/-- The word range test is the integer range test against the signed
width-`w` code range. -/
theorem outOfRange_eq (w s : ℕ) (hw : 1 ≤ w) (v : BitVec (wideWidth w s)) :
    outOfRange w s v
      = (decide (v.toInt < SaturatingRoundHalfUp.signedMinCode w) ||
          decide (SaturatingRoundHalfUp.signedMaxCode w < v.toInt)) := by
  have hmin := toInt_wideMin w s hw
  have hmax := toInt_wideMax w s hw
  have e1 : v.slt (wideMin w s) = decide (v.toInt < (wideMin w s).toInt) := rfl
  have e2 : (wideMax w s).slt v = decide ((wideMax w s).toInt < v.toInt) := rfl
  unfold outOfRange
  rw [e1, e2, hmin, hmax]

/-- Saturating narrowing decodes to integer saturation into the signed
width-`w` code range, for every intermediate word. -/
theorem toInt_saturateWord (w s : ℕ) (hw : 1 ≤ w) (v : BitVec (wideWidth w s)) :
    (saturateWord w s v).toInt
      = saturate (SaturatingRoundHalfUp.signedMinCode w)
          (SaturatingRoundHalfUp.signedMaxCode w) v.toInt := by
  have hmin := toInt_wideMin w s hw
  have hmax := toInt_wideMax w s hw
  have e1 : v.slt (wideMin w s) = decide (v.toInt < (wideMin w s).toInt) := rfl
  have e2 : (wideMax w s).slt v = decide ((wideMax w s).toInt < v.toInt) := rfl
  have hkmm : SaturatingRoundHalfUp.signedMinCode w
      ≤ SaturatingRoundHalfUp.signedMaxCode w := by
    unfold SaturatingRoundHalfUp.signedMinCode SaturatingRoundHalfUp.signedMaxCode
    have h1 : (1 : ℤ) ≤ (2 : ℤ) ^ (w - 1) :=
      calc (1 : ℤ) = (2 : ℤ) ^ 0 := by norm_num
        _ ≤ (2 : ℤ) ^ (w - 1) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
    omega
  unfold saturateWord
  rw [e1, e2, hmin, hmax]
  split
  · rename_i hlo
    have hlo' : v.toInt < SaturatingRoundHalfUp.signedMinCode w :=
      of_decide_eq_true hlo
    have hsat : saturate (SaturatingRoundHalfUp.signedMinCode w)
        (SaturatingRoundHalfUp.signedMaxCode w) v.toInt
        = SaturatingRoundHalfUp.signedMinCode w := by
      unfold saturate
      have hle : v.toInt ≤ SaturatingRoundHalfUp.signedMaxCode w :=
        le_trans (le_of_lt hlo') hkmm
      rw [min_eq_right hle, max_eq_left (le_of_lt hlo')]
    rw [hsat]
    unfold SaturatingRoundHalfUp.signedMinCode
    exact BitVec.toInt_intMin_of_pos (by omega : 0 < w)
  · split
    · rename_i _ hhi
      have hhi' : SaturatingRoundHalfUp.signedMaxCode w < v.toInt :=
        of_decide_eq_true hhi
      have hsat : saturate (SaturatingRoundHalfUp.signedMinCode w)
          (SaturatingRoundHalfUp.signedMaxCode w) v.toInt
          = SaturatingRoundHalfUp.signedMaxCode w := by
        unfold saturate
        rw [min_eq_left (le_of_lt hhi'), max_eq_right hkmm]
      rw [hsat]
      unfold SaturatingRoundHalfUp.signedMaxCode
      exact BitVec.toInt_intMax
    · rename_i hlo hhi
      have hlo' : ¬ v.toInt < SaturatingRoundHalfUp.signedMinCode w := by
        rwa [decide_eq_true_eq] at hlo
      have hhi' : ¬ SaturatingRoundHalfUp.signedMaxCode w < v.toInt := by
        rwa [decide_eq_true_eq] at hhi
      have h1 : SaturatingRoundHalfUp.signedMinCode w ≤ v.toInt :=
        not_lt.mp hlo'
      have h2 : v.toInt ≤ SaturatingRoundHalfUp.signedMaxCode w :=
        not_lt.mp hhi'
      have hsat : saturate (SaturatingRoundHalfUp.signedMinCode w)
          (SaturatingRoundHalfUp.signedMaxCode w) v.toInt = v.toInt := by
        unfold saturate
        rw [min_eq_right h2, max_eq_right h1]
      rw [hsat]
      exact toInt_setWidth_of_mem w s hw v h1 h2

/-! ### Fold-step refinement -/

/-- **Step refinement.** For every accumulator word, flag and pair of
operand words, the word step decodes to the integer step on the decoded
operands, and the two overflow flags are equal. -/
theorem wordStep_refines (w s : ℕ) (hw : 1 ≤ w) (acc : BitVec w) (flag : Bool)
    (hk xk : BitVec w) :
    (wordStep w s acc flag hk xk).1.toInt
        = (firStep s (SaturatingRoundHalfUp.signedMinCode w)
            (SaturatingRoundHalfUp.signedMaxCode w) acc.toInt flag hk.toInt
            xk.toInt).1 ∧
      (wordStep w s acc flag hk xk).2
        = (firStep s (SaturatingRoundHalfUp.signedMinCode w)
            (SaturatingRoundHalfUp.signedMaxCode w) acc.toInt flag hk.toInt
            xk.toInt).2 := by
  have hRnd := toInt_wordRoundHalfUpShift_wordProduct w s hw hk xk
  have hM : (0 : ℤ) ≤ (2 : ℤ) ^ (w * 2 - 2) := by positivity
  have hRlo : -(2 : ℤ) ^ (w * 2 - 2)
      ≤ roundHalfUpShift s (hk.toInt * xk.toInt) :=
    le_roundHalfUpShift_of_le s _ _ hM (BitVec.le_toInt_mul_toInt)
  have hRhi : roundHalfUpShift s (hk.toInt * xk.toInt)
      ≤ (2 : ℤ) ^ (w * 2 - 2) :=
    roundHalfUpShift_le_of_le s _ _ hM (BitVec.toInt_mul_toInt_le)
  have hsum : (2 : ℤ) ^ (w - 1) + (2 : ℤ) ^ (w * 2 - 2)
      ≤ (2 : ℤ) ^ (2 * w + s) := by
    have h1 : (2 : ℤ) ^ (w - 1) ≤ (2 : ℤ) ^ (2 * w + s - 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    have h2 : (2 : ℤ) ^ (w * 2 - 2) ≤ (2 : ℤ) ^ (2 * w + s - 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    have hD : (2 : ℤ) ^ (2 * w + s) = 2 * (2 : ℤ) ^ (2 * w + s - 1) := by
      conv_lhs => rw [show 2 * w + s = (2 * w + s - 1) + 1 from by omega,
        pow_succ']
    omega
  have hraw : (widen w s acc
      + wordRoundHalfUpShift w s (wordProduct w s hk xk)).toInt
      = acc.toInt
        + (wordRoundHalfUpShift w s (wordProduct w s hk xk)).toInt := by
    apply toInt_widen_add
    · rw [hRnd, wideWidth_sub_one]
      have hacc := BitVec.le_toInt acc
      omega
    · rw [hRnd, wideWidth_sub_one]
      have hacc := BitVec.toInt_lt (x := acc)
      omega
  have wfst : (wordStep w s acc flag hk xk).1 = saturateWord w s
      (widen w s acc + wordRoundHalfUpShift w s (wordProduct w s hk xk)) := rfl
  have wsnd : (wordStep w s acc flag hk xk).2 = (flag
      || outOfRange w s
        (widen w s acc + wordRoundHalfUpShift w s (wordProduct w s hk xk))
      || outOfRange w s
        (wordRoundHalfUpShift w s (wordProduct w s hk xk))) := rfl
  have ffst : (firStep s (SaturatingRoundHalfUp.signedMinCode w)
      (SaturatingRoundHalfUp.signedMaxCode w) acc.toInt flag hk.toInt
      xk.toInt).1
      = saturate (SaturatingRoundHalfUp.signedMinCode w)
        (SaturatingRoundHalfUp.signedMaxCode w)
        (acc.toInt + roundHalfUpShift s (hk.toInt * xk.toInt)) := rfl
  have fsnd : (firStep s (SaturatingRoundHalfUp.signedMinCode w)
      (SaturatingRoundHalfUp.signedMaxCode w) acc.toInt flag hk.toInt
      xk.toInt).2
      = (flag
        || (decide (acc.toInt + roundHalfUpShift s (hk.toInt * xk.toInt)
            < SaturatingRoundHalfUp.signedMinCode w)
          || decide (SaturatingRoundHalfUp.signedMaxCode w < acc.toInt
            + roundHalfUpShift s (hk.toInt * xk.toInt)))
        || (decide (roundHalfUpShift s (hk.toInt * xk.toInt)
            < SaturatingRoundHalfUp.signedMinCode w)
          || decide (SaturatingRoundHalfUp.signedMaxCode w
            < roundHalfUpShift s (hk.toInt * xk.toInt)))) := rfl
  constructor
  · rw [wfst, ffst, toInt_saturateWord w s hw, hraw, hRnd]
  · rw [wsnd, fsnd, outOfRange_eq w s hw, outOfRange_eq w s hw, hraw, hRnd]

/-- **Agreement with the core signed-overflow predicate.** When the
rounded product fits in width `w`, the partial-sum range test is
`BitVec.saddOverflow` of the width-`w` accumulator and the narrowed
product. -/
theorem outOfRange_add_eq_saddOverflow (w s : ℕ) (hw : 1 ≤ w) (acc : BitVec w)
    (prod : BitVec (wideWidth w s)) (hprod : outOfRange w s prod = false) :
    outOfRange w s (widen w s acc + prod) = acc.saddOverflow (prod.setWidth w) := by
  have hrw := outOfRange_eq w s hw prod
  rw [hrw] at hprod
  rw [Bool.or_eq_false_iff] at hprod
  obtain ⟨d1, d2⟩ := hprod
  have n1 : ¬ prod.toInt < SaturatingRoundHalfUp.signedMinCode w :=
    of_decide_eq_false d1
  have n2 : ¬ SaturatingRoundHalfUp.signedMaxCode w < prod.toInt :=
    of_decide_eq_false d2
  have h1 : SaturatingRoundHalfUp.signedMinCode w ≤ prod.toInt := not_lt.mp n1
  have h2 : prod.toInt ≤ SaturatingRoundHalfUp.signedMaxCode w := not_lt.mp n2
  have hset : (prod.setWidth w).toInt = prod.toInt :=
    toInt_setWidth_of_mem w s hw prod h1 h2
  have hexact : (widen w s acc + prod).toInt = acc.toInt + prod.toInt := by
    apply toInt_widen_add
    · rw [wideWidth_sub_one]
      have hacc := BitVec.le_toInt acc
      have h1' : -(2 : ℤ) ^ (w - 1) ≤ prod.toInt := by
        unfold SaturatingRoundHalfUp.signedMinCode at h1; exact h1
      have hmono : (2 : ℤ) ^ w ≤ (2 : ℤ) ^ (2 * w + s) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      have hDbl : (2 : ℤ) ^ w = 2 * (2 : ℤ) ^ (w - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hw]
        rw [pow_succ]
        ring
      omega
    · rw [wideWidth_sub_one]
      have hacc := BitVec.toInt_lt (x := acc)
      have h2' : prod.toInt ≤ (2 : ℤ) ^ (w - 1) - 1 := by
        unfold SaturatingRoundHalfUp.signedMaxCode at h2; exact h2
      have hmono : (2 : ℤ) ^ w ≤ (2 : ℤ) ^ (2 * w + s) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      have hDbl : (2 : ℤ) ^ w = 2 * (2 : ℤ) ^ (w - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hw]
        rw [pow_succ]
        ring
      omega
  rw [outOfRange_eq w s hw, hexact]
  unfold BitVec.saddOverflow
  rw [hset]
  unfold SaturatingRoundHalfUp.signedMinCode SaturatingRoundHalfUp.signedMaxCode
  have hiff : acc.toInt + prod.toInt ≥ (2 : ℤ) ^ (w - 1)
      ↔ (2 : ℤ) ^ (w - 1) - 1 < acc.toInt + prod.toInt := by omega
  simp only [hiff, Bool.or_comm]

/-- **A clean step is the width-`w` word sum.** When neither the rounded
product nor the width-`w` accumulation overflows, the step's word is the
plain width-`w` sum of the accumulator and the narrowed rounded product,
and the flag is unchanged. -/
theorem wordStep_eq_add_of_no_overflow (w s : ℕ) (hw : 1 ≤ w) (acc : BitVec w)
    (flag : Bool) (hk xk : BitVec w)
    (hprod : outOfRange w s (wordRoundHalfUpShift w s (wordProduct w s hk xk)) = false)
    (hsum : acc.saddOverflow
      ((wordRoundHalfUpShift w s (wordProduct w s hk xk)).setWidth w) = false) :
    wordStep w s acc flag hk xk
      = (acc + (wordRoundHalfUpShift w s (wordProduct w s hk xk)).setWidth w, flag) := by
  have hraw : outOfRange w s
      (widen w s acc + wordRoundHalfUpShift w s (wordProduct w s hk xk)) = false := by
    rw [outOfRange_add_eq_saddOverflow w s hw acc _ hprod]
    exact hsum
  have hraw' := hraw
  unfold outOfRange at hraw'
  rw [Bool.or_eq_false_iff] at hraw'
  obtain ⟨r1, r2⟩ := hraw'
  have hsat : saturateWord w s
      (widen w s acc + wordRoundHalfUpShift w s (wordProduct w s hk xk))
      = acc + (wordRoundHalfUpShift w s (wordProduct w s hk xk)).setWidth w := by
    unfold saturateWord
    rw [r1, r2]
    simp only [Bool.false_eq_true, ite_false]
    have hle : w ≤ wideWidth w s := by unfold wideWidth; omega
    rw [BitVec.setWidth_add _ _ hle, setWidth_widen]
  have e : wordStep w s acc flag hk xk
      = (saturateWord w s
          (widen w s acc + wordRoundHalfUpShift w s (wordProduct w s hk xk)),
        flag
          || outOfRange w s
            (widen w s acc + wordRoundHalfUpShift w s (wordProduct w s hk xk))
          || outOfRange w s (wordRoundHalfUpShift w s (wordProduct w s hk xk))) := rfl
  rw [e, hsat, hraw, hprod, Bool.or_false, Bool.or_false]

/-! ### Full-fold refinement -/

/-- **Fold refinement.** At every prefix length the word fold decodes to
the integer fold on the decoded taps, and the overflow flags are equal. -/
theorem wordFold_refines (w s : ℕ) (hw : 1 ≤ w) (h x : ℕ → BitVec w) (n : ℕ) :
    (wordFold w s h x n).1.toInt
        = (firFold s (SaturatingRoundHalfUp.signedMinCode w)
            (SaturatingRoundHalfUp.signedMaxCode w) (fun i => (h i).toInt)
            (fun i => (x i).toInt) n).1 ∧
      (wordFold w s h x n).2
        = (firFold s (SaturatingRoundHalfUp.signedMinCode w)
            (SaturatingRoundHalfUp.signedMaxCode w) (fun i => (h i).toInt)
            (fun i => (x i).toInt) n).2 := by
  induction n with
  | zero =>
    exact ⟨BitVec.toInt_zero, rfl⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : wordFold w s h x (n + 1)
        = wordStep w s (wordFold w s h x n).1 (wordFold w s h x n).2 (h n) (x n) :=
      rfl
    rw [e, firFold_succ, ← ih1, ← ih2]
    exact wordStep_refines w s hw _ _ _ _

/-- **Filter refinement.** The `m`-tap word filter's output decodes to the
integer filter's output on the decoded taps, and the overflow flags are
equal. -/
theorem wordCode_refines {m : ℕ} (w s : ℕ) (hw : 1 ≤ w) (hc xc : Fin m → BitVec w) :
    (wordCode w s hc xc).toInt
        = firCode s (SaturatingRoundHalfUp.signedMinCode w)
            (SaturatingRoundHalfUp.signedMaxCode w) (fun k => (hc k).toInt)
            (fun k => (xc k).toInt) ∧
      wordOverflow w s hc xc
        = firOverflow s (SaturatingRoundHalfUp.signedMinCode w)
            (SaturatingRoundHalfUp.signedMaxCode w) (fun k => (hc k).toInt)
            (fun k => (xc k).toInt) := by
  have hfH : (fun i => (if hlt : i < m then hc ⟨i, hlt⟩ else 0#w).toInt)
      = fun i => if hlt : i < m then (hc ⟨i, hlt⟩).toInt else 0 := by
    funext i
    by_cases hlt : i < m
    · simp only [hlt, dite_true]
    · simp only [hlt, dite_false, BitVec.toInt_zero]
  have hfX : (fun i => (if hlt : i < m then xc ⟨i, hlt⟩ else 0#w).toInt)
      = fun i => if hlt : i < m then (xc ⟨i, hlt⟩).toInt else 0 := by
    funext i
    by_cases hlt : i < m
    · simp only [hlt, dite_true]
    · simp only [hlt, dite_false, BitVec.toInt_zero]
  obtain ⟨r1, r2⟩ := wordFold_refines w s hw
    (fun i => if hlt : i < m then hc ⟨i, hlt⟩ else 0#w)
    (fun i => if hlt : i < m then xc ⟨i, hlt⟩ else 0#w) m
  rw [hfH, hfX] at r1 r2
  exact ⟨r1, r2⟩

/-! ### Composed guarantee -/

/-- **Headline.** The word filter refines the integer filter (decoded
output and overflow flag), and when its flag is clear and the real
inputs and coefficients are within half a step of their decoded words,
its decoded output obeys the ordered dot-product bound with zero
initialization, the coefficient, input and product errors at half a
step, and no accumulation error, since a clean trace adds exactly. -/
theorem wordFir_correct (s w m : ℕ) (hw : 1 ≤ w)
    (h x : Fin m → ℝ) (hc xc : Fin m → BitVec w)
    (hdx : ∀ k : Fin m, |decodeWord s (xc k) - x k| ≤ (1 : ℝ) / (2 * (2 : ℝ) ^ s))
    (hdh : ∀ k : Fin m, |decodeWord s (hc k) - h k| ≤ (1 : ℝ) / (2 * (2 : ℝ) ^ s))
    (hno : wordOverflow w s hc xc = false) :
    ((wordCode w s hc xc).toInt
        = firCode s (SaturatingRoundHalfUp.signedMinCode w)
            (SaturatingRoundHalfUp.signedMaxCode w) (fun k => (hc k).toInt)
            (fun k => (xc k).toInt) ∧
      wordOverflow w s hc xc
        = firOverflow s (SaturatingRoundHalfUp.signedMinCode w)
            (SaturatingRoundHalfUp.signedMaxCode w) (fun k => (hc k).toInt)
            (fun k => (xc k).toInt)) ∧
    |decodeWord s (wordCode w s hc xc) - OrderedDotProductError.outputIdeal m h x|
      ≤ ((1 : ℝ) / (2 * (2 : ℝ) ^ s)) * (∑ k : Fin m, |h k|)
        + ((1 : ℝ) / (2 * (2 : ℝ) ^ s)) * (∑ k : Fin m, |x k|)
        + (m : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ s)) * ((1 : ℝ) / (2 * (2 : ℝ) ^ s))
        + (m : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ s)) := by
  have href := wordCode_refines w s hw hc xc
  refine ⟨href, ?_⟩
  obtain ⟨r1, r2⟩ := href
  have hno' : firOverflow s (SaturatingRoundHalfUp.signedMinCode w)
      (SaturatingRoundHalfUp.signedMaxCode w) (fun k => (hc k).toInt)
      (fun k => (xc k).toInt) = false := by
    rw [← r2]
    exact hno
  have hdec : decodeWord s (wordCode w s hc xc)
      = decode s (firCode s (SaturatingRoundHalfUp.signedMinCode w)
          (SaturatingRoundHalfUp.signedMaxCode w) (fun k => (hc k).toInt)
          (fun k => (xc k).toInt)) := by
    unfold decodeWord
    rw [r1]
  rw [hdec]
  exact fixed_point_fir_error_bound s w m hw h x (fun k => (hc k).toInt)
    (fun k => (xc k).toInt) hdx hdh hno'

end CSLibExt.Algorithms.Numerical.FixedPointFIRWordRefinement
