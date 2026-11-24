/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.CRC
public import Mathlib.Algebra.Field.ZMod
public import CSLibExt.Computability.Automata.Transducers.Sequential
public import MathlibExt.Algebra.Polynomial.BitVec
public import MathlibExt.Data.BitVec.BinaryPolynomialArithmetic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Unreflected serial CRC

The bit-level shift-register refinement of the polynomial CRC in
`CSLibExt.Coding.CRC`: an unreflected (non-reflected) serial LFSR
over `BitVec r`, driven by the canonical executable
`BitVec.mulXMod` step for the taps word (generator `X^r + taps`),
presented as a `Cslib.Automata.MealyMachine`. The register, read
through the canonical `BitVec.toPolynomial`, after the payload
plus `r` zero bits equals the shifted message polynomial
remainder `(m * X^r) %ₘ taps.monicModulus`, and for any monic
generator `g` of degree `r` the same statement holds with taps
`g.toBitVec r`. The CRC-3 generator `X^3 + X + 1` fixtures are
proved both as bit words (`0b100`, `0b001`, `0b101`) and as
polynomials, and reversing the payload changes the result, as
the unreflected convention requires.
-/

@[expose] public section

namespace CSLibExt.Coding.UnreflectedSerialCRC

/-- The field structure on `ZMod 2` used by `Cslib.CodingTheory.CRC.encode`,
registered only while this module is elaborated. -/
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩


/-- A payload bit as a polynomial over `ZMod 2`. -/
noncomputable def bitPoly (b : Bool) : Polynomial (ZMod 2) :=
  if b then 1 else 0

/-- The message polynomial of an MSB-first payload of declared length `l = bits.length`:
`m = ∑_j bit_j * X^(l-1-j)`. Leading zeros are counted in `l`. -/
noncomputable def messagePoly (bits : List Bool) : Polynomial (ZMod 2) :=
  ∑ j : Fin bits.length,
    bitPoly (bits.get j) * Polynomial.X ^ (bits.length - 1 - j.val)

/-- The input bit as a width-`r` word occupying bit `0` (the coefficient of `X ^ 0`). -/
def inputBit (r : ℕ) (b : Bool) : BitVec r :=
  if b then 1#r else 0#r

/-- One executable unreflected serial step: canonical shift/XOR reduction by the taps
(`BitVec.mulXMod`), then XOR of the input bit into bit `0`. -/
def stepRegister (r : ℕ) (taps w : BitVec r) (b : Bool) : BitVec r :=
  taps.mulXMod w ^^^ inputBit r b

/-- The zero-init unreflected serial LFSR as a canonical Mealy machine: state and output
are the register, input is the next payload bit, start is the zero register. -/
def serialLFSR (r : ℕ) (taps : BitVec r) :
    Cslib.Automata.MealyMachine (BitVec r) Bool (BitVec r) where
  step w b := let w' := stepRegister r taps w b; (w', w')
  start := 0#r

/-- The register after running `bits` from the zero register. -/
def runRegister (r : ℕ) (taps : BitVec r) (bits : List Bool) : BitVec r :=
  (serialLFSR r taps).runState (serialLFSR r taps).start bits

/-- The final register: the payload followed by exactly `r` zero bits. -/
def finalRegister (r : ℕ) (taps : BitVec r) (bits : List Bool) : BitVec r :=
  runRegister r taps (bits ++ List.replicate r false)

/-- The CRC-3 generator `X^3 + X + 1` of the Atlas CRC tests. -/
noncomputable def crc3Generator : Polynomial (ZMod 2) :=
  Polynomial.X ^ 3 + Polynomial.X + 1

/-- The CRC-3 taps word: the lower coefficients `X + 1` of `X^3 + X + 1`. -/
def crc3Taps : BitVec 3 :=
  0b011#3

/-! ### Private helpers -/

private theorem messagePoly_nil : messagePoly [] = 0 := by
  simp [messagePoly]

private theorem messagePoly_cons (b : Bool) (bits : List Bool) :
    messagePoly (b :: bits) = bitPoly b * Polynomial.X ^ bits.length + messagePoly bits := by
  unfold messagePoly
  simp only [List.length_cons, Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    have hexp : bits.length + 1 - 1 - (i.val + 1) = bits.length - 1 - i.val := by
      omega
    rw [List.get_cons_succ', Fin.val_succ, hexp]

private theorem messagePoly_append (a b : List Bool) :
    messagePoly (a ++ b) = messagePoly a * Polynomial.X ^ b.length + messagePoly b := by
  induction a generalizing b with
  | nil => simp [messagePoly_nil]
  | cons x a ih =>
    rw [List.cons_append, messagePoly_cons, ih, List.length_append, messagePoly_cons,
      pow_add]
    ring

private theorem messagePoly_replicate_false (n : ℕ) :
    messagePoly (List.replicate n false) = 0 := by
  induction n with
  | zero => exact messagePoly_nil
  | succ n ih => rw [List.replicate_succ, messagePoly_cons, ih]; simp [bitPoly]

private theorem degree_toPolynomial_lt (r : ℕ) (w : BitVec r) :
    w.toPolynomial.degree < r := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  simp [BitVec.coeff_toPolynomial, BitVec.getLsbD_of_ge w m hm]

private theorem degree_monicModulus (r : ℕ) (taps : BitVec r) :
    taps.monicModulus.degree = r := by
  rw [Polynomial.degree_eq_natDegree (BitVec.monicModulus_monic taps).ne_zero,
    BitVec.monicModulus_natDegree]

private theorem toPolynomial_shiftLeft (r : ℕ) (w : BitVec r) :
    (w.shiftLeft 1).toPolynomial =
      w.toPolynomial * Polynomial.X +
        (if w.getMsbD 0 then Polynomial.X ^ r else 0) := by
  rw [mul_comm, ← BitVec.toPolynomial_shiftLeft_add_high, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

private theorem toPolynomial_mulXMod (r : ℕ) (taps w : BitVec r) :
    (taps.mulXMod w).toPolynomial =
      w.toPolynomial * Polynomial.X +
        (if w.getMsbD 0 then taps.monicModulus else 0) := by
  cases hmsb : w.getMsbD 0
  · simp only [BitVec.mulXMod, hmsb, Bool.false_eq_true, ite_false]
    rw [toPolynomial_shiftLeft]
    simp [hmsb]
  · simp only [BitVec.mulXMod]
    simp [hmsb]
    rw [BitVec.toPolynomial_xor, ← BitVec.shiftLeft_eq, toPolynomial_shiftLeft]
    simp [hmsb, BitVec.monicModulus]
    ring

private theorem toPolynomial_inputBit (r : ℕ) (hr : 0 < r) (b : Bool) :
    (inputBit r b).toPolynomial = bitPoly b := by
  cases b with
  | false =>
    have h0 : inputBit r false = 0#r := rfl
    have hb0 : bitPoly false = 0 := rfl
    rw [h0, hb0]
    ext i
    simp [BitVec.coeff_toPolynomial]
  | true =>
    have h1 : inputBit r true = 1#r := rfl
    have hb : bitPoly true = 1 := rfl
    rw [h1, hb]
    ext i
    simp only [BitVec.coeff_toPolynomial, BitVec.getLsbD_one, Polynomial.coeff_one]
    by_cases h : i = 0 <;> simp [h, hr]

/-- The zero register represents the zero polynomial. -/
theorem toPolynomial_zero_register (r : ℕ) : (0#r).toPolynomial = 0 := by
  ext i
  simp [BitVec.coeff_toPolynomial]

/-- Bridge: one executable step is one long-division step,
`s ↦ (s * X + b) %ₘ (X ^ r + taps)`. -/
theorem toPolynomial_stepRegister (r : ℕ) (taps w : BitVec r) (b : Bool) :
    (stepRegister r taps w b).toPolynomial =
      (w.toPolynomial * Polynomial.X + bitPoly b) %ₘ taps.monicModulus := by
  cases r with
  | zero =>
    have h0 : ∀ (v : BitVec 0), v.toPolynomial = 0 := fun v => by
      ext i
      simp [BitVec.coeff_toPolynomial, BitVec.getLsbD_of_ge v i (Nat.zero_le i)]
    have hmod : taps.monicModulus = 1 := by
      unfold BitVec.monicModulus
      rw [h0 taps]
      simp
    rw [h0 (stepRegister 0 taps w b), hmod, Polynomial.modByMonic_one]
  | succ r =>
    have hr : 0 < r + 1 := Nat.zero_lt_succ r
    have hmod := BitVec.monicModulus_monic taps
    have hstep : (stepRegister (r + 1) taps w b).toPolynomial =
        w.toPolynomial * Polynomial.X + bitPoly b +
          (if w.getMsbD 0 then taps.monicModulus else 0) := by
      unfold stepRegister
      rw [BitVec.toPolynomial_xor, toPolynomial_mulXMod, toPolynomial_inputBit _ hr]
      cases hmsb : w.getMsbD 0 <;> simp [hmsb] <;> ring
    have hdeg : (stepRegister (r + 1) taps w b).toPolynomial.degree <
        taps.monicModulus.degree := by
      rw [degree_monicModulus]
      exact degree_toPolynomial_lt _ _
    have hself := (Polynomial.modByMonic_eq_self_iff hmod).mpr hdeg
    have hdvd : taps.monicModulus ∣ (stepRegister (r + 1) taps w b).toPolynomial -
        (w.toPolynomial * Polynomial.X + bitPoly b) := by
      have hring : (stepRegister (r + 1) taps w b).toPolynomial -
          (w.toPolynomial * Polynomial.X + bitPoly b) =
          (if w.getMsbD 0 then taps.monicModulus else 0) := by
        rw [hstep]; ring
      rw [hring]
      cases hmsb : w.getMsbD 0
      · simp [hmsb, dvd_zero]
      · simp [hmsb, dvd_refl]
    have heq := Polynomial.modByMonic_eq_of_dvd_sub hmod hdvd
    rw [hself] at heq
    exact heq

private theorem toPolynomial_runState_from (r : ℕ) (taps : BitVec r) (q : BitVec r)
    (bits : List Bool) :
    ((serialLFSR r taps).runState q bits).toPolynomial =
      (q.toPolynomial * Polynomial.X ^ bits.length + messagePoly bits) %ₘ taps.monicModulus := by
  induction bits generalizing q with
  | nil =>
    have hmod := BitVec.monicModulus_monic taps
    have hdeg : q.toPolynomial.degree < taps.monicModulus.degree := by
      rw [degree_monicModulus]
      exact degree_toPolynomial_lt _ _
    have hself := (Polynomial.modByMonic_eq_self_iff hmod).mpr hdeg
    have hnil : (serialLFSR r taps).runState q [] = q := rfl
    have hexp : ([] : List Bool).length = 0 := rfl
    rw [hnil, hexp, messagePoly_nil]
    simp [hself]
  | cons b bits ih =>
    have hmod := BitVec.monicModulus_monic taps
    rw [Cslib.Automata.MealyMachine.runState_cons]
    have hstep : ((serialLFSR r taps).step q b).1 = stepRegister r taps q b := rfl
    rw [hstep, ih, toPolynomial_stepRegister, messagePoly_cons, List.length_cons]
    refine Polynomial.modByMonic_eq_of_dvd_sub hmod ?_
    have hdiv : (q.toPolynomial * Polynomial.X + bitPoly b) %ₘ taps.monicModulus =
        (q.toPolynomial * Polynomial.X + bitPoly b) -
          taps.monicModulus * ((q.toPolynomial * Polynomial.X + bitPoly b) /ₘ taps.monicModulus) :=
      Polynomial.modByMonic_eq_sub_mul_div _ _
    have h1 : taps.monicModulus ∣
        ((q.toPolynomial * Polynomial.X + bitPoly b) %ₘ taps.monicModulus) -
          (q.toPolynomial * Polynomial.X + bitPoly b) :=
      ⟨-(((q.toPolynomial * Polynomial.X + bitPoly b) /ₘ taps.monicModulus)), by
        rw [hdiv]; ring⟩
    have h2 : taps.monicModulus ∣
        (((q.toPolynomial * Polynomial.X + bitPoly b) %ₘ taps.monicModulus) -
          (q.toPolynomial * Polynomial.X + bitPoly b)) * Polynomial.X ^ bits.length :=
      dvd_mul_of_dvd_left h1 _
    have h3 : (((q.toPolynomial * Polynomial.X + bitPoly b) %ₘ taps.monicModulus) *
          Polynomial.X ^ bits.length + messagePoly bits) -
          (q.toPolynomial * Polynomial.X ^ (bits.length + 1) +
            (bitPoly b * Polynomial.X ^ bits.length + messagePoly bits)) =
        (((q.toPolynomial * Polynomial.X + bitPoly b) %ₘ taps.monicModulus) -
          (q.toPolynomial * Polynomial.X + bitPoly b)) * Polynomial.X ^ bits.length := by
      rw [pow_succ]; ring
    rw [h3]
    exact h2

/-- Run invariant: after any MSB-first list from the zero register, the register
represents `messagePoly bits %ₘ (X ^ r + taps)`. -/
theorem toPolynomial_runRegister (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    (runRegister r taps bits).toPolynomial = messagePoly bits %ₘ taps.monicModulus := by
  have hstart : (serialLFSR r taps).start = 0#r := rfl
  unfold runRegister
  rw [toPolynomial_runState_from, hstart, toPolynomial_zero_register]
  simp

/-- Appending `r` zero bits multiplies the message polynomial by `X ^ r`. -/
theorem messagePoly_append_zeros (bits : List Bool) (r : ℕ) :
    messagePoly (bits ++ List.replicate r false) = messagePoly bits * Polynomial.X ^ r := by
  rw [messagePoly_append, messagePoly_replicate_false, List.length_replicate, add_zero]

/-- A leading zero leaves the message polynomial unchanged. -/
theorem messagePoly_cons_false (bits : List Bool) :
    messagePoly (false :: bits) = messagePoly bits := by
  rw [messagePoly_cons]; simp [bitPoly]

/-- A leading zero lengthens the declared length by one (`l` is not recomputed). -/
theorem messagePoly_cons_false_length (bits : List Bool) :
    (false :: bits).length = bits.length + 1 := by
  exact List.length_cons

private theorem getLsbD_toBitVec (g : Polynomial (ZMod 2)) (r i : ℕ) :
    (g.toBitVec r).getLsbD i = (if i < r then decide (g.coeff i = 1) else false) := by
  unfold Polynomial.toBitVec
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  by_cases hi : i < r
  · simp only [hi, ite_true]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi)]
    rw [List.getElem_ofFn (by rw [List.length_ofFn]; exact hi)]
  · simp only [hi, ite_false]
    rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact Nat.le_of_not_gt hi)]

/-- The CRC-3 taps word is the canonical modulus `X^3 + X + 1`. -/
theorem monicModulus_crc3Taps : crc3Taps.monicModulus = crc3Generator := by
  have h : crc3Taps.toBoolListLE = [true, true, false] := by decide
  simp only [BitVec.monicModulus, BitVec.toPolynomial, crc3Generator, h]
  simp [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil]
  ring

/-- A leading zero gives the same final register polynomial, after one extra step. -/
theorem final_register_cons_false (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    (finalRegister r taps (false :: bits)).toPolynomial =
      (finalRegister r taps bits).toPolynomial := by
  unfold finalRegister
  rw [toPolynomial_runRegister, toPolynomial_runRegister]
  have happ : (false :: bits) ++ List.replicate r false =
      false :: (bits ++ List.replicate r false) := rfl
  rw [happ, messagePoly_cons_false]

/-- An all-zero payload of any declared length gives the zero final register. -/
theorem final_register_all_zero (r : ℕ) (taps : BitVec r) (l : ℕ) :
    (finalRegister r taps (List.replicate l false)).toPolynomial = 0 := by
  unfold finalRegister
  rw [toPolynomial_runRegister]
  have happ : List.replicate l false ++ List.replicate r false =
      List.replicate (l + r) false :=
    (List.replicate_add l r false).symm
  rw [happ, messagePoly_replicate_false]
  exact Polynomial.zero_modByMonic _

/-- The final register represents `(m * X ^ r) %ₘ (X ^ r + taps)` (taps form). -/
theorem final_register_represents_shifted_message_remainder (r : ℕ) (taps : BitVec r)
    (bits : List Bool) :
    (finalRegister r taps bits).toPolynomial =
      (messagePoly bits * Polynomial.X ^ r) %ₘ taps.monicModulus := by
  unfold finalRegister
  rw [toPolynomial_runRegister, messagePoly_append_zeros]

/-- The leaf obligation at v2 strength: for any monic `g` of degree `r ≥ 1`, the register
run with taps `g.toBitVec r` represents `(m * X ^ r) %ₘ g`. -/
theorem final_register_represents_shifted_message_remainder_of_monic
    (g : Polynomial (ZMod 2)) (r : ℕ) (hg : g.Monic) (hr : g.natDegree = r) (hr1 : 1 ≤ r)
    (bits : List Bool) :
    (finalRegister r (g.toBitVec r) bits).toPolynomial =
      (messagePoly bits * Polynomial.X ^ r) %ₘ g := by
  have h := final_register_represents_shifted_message_remainder r (g.toBitVec r) bits
  rw [BitVec.monicModulus_toBitVec g hg hr] at h
  exact h

/-- The register computes exactly the check remainder that the polynomial
encoder `Cslib.CodingTheory.CRC.encode` appends: the codeword is the shifted
message plus the final register read as a polynomial (characteristic two, so
appending is addition). -/
theorem encode_eq_messagePoly_shift_add_finalRegister (g : Polynomial (ZMod 2)) (r : ℕ)
    (hg : g.Monic) (hr : g.natDegree = r) (hr1 : 1 ≤ r) (bits : List Bool) :
    @Cslib.CodingTheory.CRC.encode (ZMod 2) _ g (messagePoly bits) =
      messagePoly bits * Polynomial.X ^ r +
        (finalRegister r (g.toBitVec r) bits).toPolynomial := by
  rw [final_register_represents_shifted_message_remainder_of_monic g r hg hr hr1 bits,
    Polynomial.modByMonic_eq_mod _ hg, Cslib.CodingTheory.CRC.encode_eq_add, hr]



/-- CRC-3, payload `101`: executable final register `0b100`. -/
theorem final_register_crc3_payload_101_bits :
    finalRegister 3 crc3Taps [true, false, true] = 0b100#3 := by
  decide

/-- CRC-3, payload `101`: the final register represents `X ^ 2`. -/
theorem final_register_crc3_payload_101 :
    (finalRegister 3 crc3Taps [true, false, true]).toPolynomial = Polynomial.X ^ 2 := by
  rw [final_register_crc3_payload_101_bits]
  have h : (0b100#3).toBoolListLE = [false, false, true] := by decide
  simp only [BitVec.toPolynomial, h]
  simp [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil]
  ring

/-- CRC-3, payload `110`: executable final register `0b001`. -/
theorem final_register_crc3_payload_110_bits :
    finalRegister 3 crc3Taps [true, true, false] = 0b001#3 := by
  decide

/-- CRC-3, payload `110`: the final register represents `1`. -/
theorem final_register_crc3_payload_110 :
    (finalRegister 3 crc3Taps [true, true, false]).toPolynomial = 1 := by
  rw [final_register_crc3_payload_110_bits]
  have h : (0b001#3).toBoolListLE = [true, false, false] := by decide
  simp only [BitVec.toPolynomial, h]
  simp [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil]

/-- CRC-3, reversed payload `011`: executable final register `0b101`. -/
theorem final_register_crc3_payload_011_bits :
    finalRegister 3 crc3Taps [false, true, true] = 0b101#3 := by
  decide

/-- CRC-3, reversed payload `011`: the final register represents `X ^ 2 + 1`, unlike `110`. -/
theorem final_register_crc3_payload_011 :
    (finalRegister 3 crc3Taps [false, true, true]).toPolynomial = Polynomial.X ^ 2 + 1 := by
  rw [final_register_crc3_payload_011_bits]
  have h : (0b101#3).toBoolListLE = [true, false, true] := by decide
  simp only [BitVec.toPolynomial, h]
  simp [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil]
  ring

end CSLibExt.Coding.UnreflectedSerialCRC
