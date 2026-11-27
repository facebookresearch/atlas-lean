/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.FixedLengthCRCFrames

@[expose] public section

/-!
# Serial CRC burst detection

The fixed-length codeword of the unreflected serial CRC in
`CSLibExt.Coding.UnreflectedSerialCRC` is the frame body
`CSLibExt.Coding.FixedLengthCRCFrames.encodedBody`: the MSB-first payload
followed by its MSB-first check register. A nonzero error whose `true` bits lie in `L`
consecutive transmission positions is a polynomial burst of length at most
`L` (`isBurstLE_messagePoly_of_isBitBurstLE`), so the polynomial burst
detection theorem transfers through the serial bit order. The receiver runs
the serial register over the received word and accepts only the zero
register; it accepts every error-free codeword (`runRegister_encodedBody_eq_zero`).
When the generator has constant coefficient `1`, every nonzero nonwrapping
burst of length at most the register width `r` in the codeword is rejected
(`runRegister_ne_zero_of_isBitBurstLE`, and `serialCRC_rejects_burst` for a
monic generator); the augmented check over the received word followed by `r`
zero bits rejects it too (`finalRegister_ne_zero_of_isBitBurstLE`). The test module
validates the CRC-16/XMODEM convention (width `16`, taps `0x1021`, check value
`0x31C3` for the ASCII payload `"123456789"`), including leading zero bytes,
detection of a length-16 burst, and the length-17 generator pattern that is not
detected.

## References

* W. W. Peterson, D. T. Brown, "Cyclic codes for error detection", *Proceedings of the IRE* 49
  (1961), 228-235.
* G. Cook, *Catalogue of parametrised CRC algorithms* (CRC RevEng), entry CRC-16/XMODEM,
  https://reveng.sourceforge.io/crc-catalogue/16.htm#crc.cat.crc-16-xmodem
-/

namespace CSLibExt.Coding.SerialCRCBurstDetection

open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.FixedLengthCRCFrames

/-- **Nonwrapping bit burst.** A nonzero nonwrapping bit burst of length at most `L`: `e` has a
`true` bit, and all its `true` bits lie in the `L` consecutive positions `i, ..., i + L - 1`. -/
def IsBitBurstLE (e : List Bool) (L : ℕ) : Prop :=
  true ∈ e ∧ ∃ i : ℕ, ∀ j : ℕ, ∀ hj : j < e.length, e[j] = true → i ≤ j ∧ j < i + L


/-! #### Proof helpers

The polynomial side is the canonical one: a register `w` is read as `w.toPolynomial`, the
generator of the taps word is `taps.monicModulus`, the register after a run is the message
remainder by `toPolynomial_runRegister`, and the message polynomial recurrences are the base
module's `messagePoly_nil`, `messagePoly_cons` and `messagePoly_append`. The helpers below only
add XOR of received words and the coefficient bookkeeping of the bit-order transfer. -/

open Polynomial

private theorem bitPoly_xor (a b : Bool) :
    bitPoly (Bool.xor a b) = bitPoly a + bitPoly b := by
  cases a <;> cases b <;> simp [bitPoly, CharTwo.add_self_eq_zero]

private theorem messagePoly_zipWith_xor (a b : List Bool) (h : a.length = b.length) :
    messagePoly (List.zipWith Bool.xor a b) = messagePoly a + messagePoly b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [messagePoly_nil]
    | cons _ _ => simp at h
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zipWith_cons_cons, messagePoly_cons, messagePoly_cons, messagePoly_cons,
        ih b h, List.length_zipWith, h, Nat.min_self, bitPoly_xor]
      ring

private theorem coeff_bitPoly_mul_X_pow (b : Bool) (i k : ℕ) :
    (bitPoly b * X ^ i).coeff k = if b ∧ k = i then 1 else 0 := by
  cases b <;> simp [bitPoly, coeff_X_pow]

/-- A register is zero exactly when its canonical polynomial is: `toPolynomial` is inverted by
`Polynomial.toBitVec`. -/
private theorem eq_zero_of_toPolynomial_eq_zero {r : ℕ} (w : BitVec r)
    (h : w.toPolynomial = 0) : w = 0#r := by
  have hw := BitVec.toBitVec_toPolynomial w
  rw [h, ← BitVec.toPolynomial_zero r, BitVec.toBitVec_toPolynomial] at hw
  exact hw.symm

/-- The register after a run is zero exactly when the generator divides the message. -/
private theorem runRegister_eq_zero_iff {r : ℕ} (taps : BitVec r) (bits : List Bool) :
    runRegister r taps bits = 0#r ↔ taps.monicModulus ∣ messagePoly bits := by
  rw [← modByMonic_eq_zero_iff_dvd (BitVec.monicModulus_monic taps),
    ← toPolynomial_runRegister]
  constructor
  · intro h
    rw [h, BitVec.toPolynomial_zero]
  · exact eq_zero_of_toPolynomial_eq_zero _

/-- The register is zero exactly when the generator divides the shifted message. -/
private theorem finalRegister_eq_zero_iff {r : ℕ} (taps : BitVec r) (bits : List Bool) :
    finalRegister r taps bits = 0#r ↔ taps.monicModulus ∣ messagePoly bits * X ^ r := by
  rw [← modByMonic_eq_zero_iff_dvd (BitVec.monicModulus_monic taps),
    ← final_register_represents_shifted_message_remainder]
  constructor
  · intro h
    rw [h, BitVec.toPolynomial_zero]
  · exact eq_zero_of_toPolynomial_eq_zero _

private theorem exists_of_coeff_messagePoly_ne_zero (e : List Bool) (k : ℕ)
    (hk : (messagePoly e).coeff k ≠ 0) :
    ∃ j : ℕ, ∃ hj : j < e.length, e[j] = true ∧ k = e.length - 1 - j := by
  by_contra hne
  apply hk
  unfold messagePoly
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [coeff_bitPoly_mul_X_pow, ite_eq_right]
  rintro ⟨h1, h2⟩
  exact hne ⟨j.val, j.isLt, h1, h2⟩

private theorem messagePoly_ne_zero (e : List Bool) (he : true ∈ e) : messagePoly e ≠ 0 := by
  obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.mp he
  intro h0
  have hc := congrArg (fun p => p.coeff (e.length - 1 - j)) h0
  simp only [coeff_zero] at hc
  unfold messagePoly at hc
  rw [finsetSum_coeff, Finset.sum_eq_single ⟨j, hj⟩] at hc
  · rw [coeff_bitPoly_mul_X_pow, ite_eq_left ⟨by simpa using hej, rfl⟩] at hc
    exact one_ne_zero hc
  · intro j' _ hj'
    rw [coeff_bitPoly_mul_X_pow, ite_eq_right]
    rintro ⟨_, h2⟩
    apply hj'
    ext
    have := j'.isLt
    change (j' : ℕ) = j
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A bit burst has positive length: its window holds a `true` bit. -/
private theorem one_le_of_isBitBurstLE {e : List Bool} {L : ℕ} (he : IsBitBurstLE e L) :
    1 ≤ L := by
  obtain ⟨hmem, i, hi⟩ := he
  obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.mp hmem
  have := hi j hj hej
  omega

/-- The codeword has the fixed length `bits.length + r`. -/
private theorem length_encodedBody (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    (encodedBody r taps bits).length = bits.length + r := by
  simp [encodedBody, checkBits, Nat.length_toBitsBE]

/-- **Bit-order transfer.** Under the MSB-first order, a nonzero bit burst of length at most `L`
is a polynomial burst of length at most `L` in the sense of `Cslib.CodingTheory.CRC`. -/
theorem isBurstLE_messagePoly_of_isBitBurstLE (e : List Bool) (L : ℕ)
    (he : IsBitBurstLE e L) : Cslib.CodingTheory.CRC.IsBurstLE (messagePoly e) L := by
  obtain ⟨hmem, i, hi⟩ := he
  refine Cslib.CodingTheory.CRC.isBurstLE_of_support (messagePoly_ne_zero e hmem)
    (i := e.length - (i + L)) ?_
  intro k hk
  rw [mem_support_iff] at hk
  obtain ⟨j, hj, hej, rfl⟩ := exists_of_coeff_messagePoly_ne_zero e k hk
  have := hi j hj hej
  omega

/-- A nonzero nonwrapping burst of length at most `r`, shifted by any power of `X`, is not a
multiple of a generator `X ^ r + taps` with constant coefficient `1`. -/
private theorem not_dvd_messagePoly_mul_X_pow {r : ℕ} (taps : BitVec r)
    (h0 : taps.getLsbD 0 = true) (e : List Bool) (L : ℕ) (he : IsBitBurstLE e L) (hL : L ≤ r)
    (k : ℕ) : ¬taps.monicModulus ∣ messagePoly e * X ^ k := by
  have hr : 1 ≤ r := (one_le_of_isBitBurstLE he).trans hL
  have hburst : Cslib.CodingTheory.CRC.IsBurstLE (messagePoly e * X ^ k) L := by
    obtain ⟨i, b, heq, hb0, hbL⟩ := isBurstLE_messagePoly_of_isBitBurstLE e L he
    exact ⟨i + k, b, by rw [heq, pow_add]; ring, hb0, hbL⟩
  have hX : ¬X ∣ taps.monicModulus := by
    rw [X_dvd_iff, BitVec.monicModulus, coeff_add, BitVec.coeff_toPolynomial, h0, coeff_X_pow]
    have : (0 : ℕ) ≠ r := by omega
    simp [this]
  exact Cslib.CodingTheory.CRC.not_dvd_of_isBurstLE hX hburst
    (by rw [BitVec.monicModulus_natDegree]; exact hL)

/-- The taps word of a monic generator of degree `r ≥ 1` with `g(0) = 1` has bit `0` set
(for `r = 0` the taps word is empty). -/
private theorem getLsbD_toBitVec_zero (g : Polynomial (ZMod 2)) (r : ℕ) (hg : g.Monic)
    (hr : g.natDegree = r) (hr1 : 1 ≤ r) (hg0 : g.eval 0 = 1) :
    (g.toBitVec r).getLsbD 0 = true := by
  have hc : (g.toBitVec r).monicModulus.coeff 0 = g.coeff 0 := by
    rw [BitVec.monicModulus_toBitVec g hg hr]
  rw [BitVec.monicModulus, coeff_add, coeff_X_pow, BitVec.coeff_toPolynomial,
    coeff_zero_eq_eval_zero g, hg0, ite_eq_right (by omega), zero_add] at hc
  revert hc
  cases (g.toBitVec r).getLsbD 0 <;> decide

/-- **Augmented check of a codeword.** The augmented check of an error-free codeword (the
codeword followed by `r` zero bits) is also the zero register; a corollary of
`runRegister_encodedBody_eq_zero`. -/
theorem finalRegister_encodedBody_eq_zero (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    finalRegister r taps (encodedBody r taps bits) = 0#r := by
  rw [finalRegister_eq_zero_iff]
  exact dvd_mul_of_dvd_left
    ((runRegister_eq_zero_iff taps _).mp (runRegister_encodedBody_eq_zero r taps bits)) _

/-- **Burst detection, taps form.** For a taps word with bit `0` set (generator
`X ^ r + taps` with constant coefficient `1`), every nonzero nonwrapping burst of length at most
`r` in the codeword is rejected by the receiver: running the serial register over the received
word leaves a nonzero register. -/
theorem runRegister_ne_zero_of_isBitBurstLE (r : ℕ) (taps : BitVec r)
    (h0 : taps.getLsbD 0 = true) (bits e : List Bool) (hlen : e.length = bits.length + r)
    (L : ℕ) (he : IsBitBurstLE e L) (hL : L ≤ r) :
    runRegister r taps (List.zipWith Bool.xor (encodedBody r taps bits) e) ≠ 0#r := by
  intro hz
  have hc := (runRegister_eq_zero_iff taps _).mp (runRegister_encodedBody_eq_zero r taps bits)
  rw [runRegister_eq_zero_iff,
    messagePoly_zipWith_xor _ _ (by rw [length_encodedBody, hlen])] at hz
  refine not_dvd_messagePoly_mul_X_pow taps h0 e L he hL 0 ?_
  rw [pow_zero, mul_one]
  exact (dvd_add_right hc).mp hz

/-- **Burst detection, augmented check.** Under the hypotheses of
`runRegister_ne_zero_of_isBitBurstLE`, the register after the received word followed by `r` zero
bits is nonzero as well. -/
theorem finalRegister_ne_zero_of_isBitBurstLE (r : ℕ) (taps : BitVec r)
    (h0 : taps.getLsbD 0 = true) (bits e : List Bool) (hlen : e.length = bits.length + r)
    (L : ℕ) (he : IsBitBurstLE e L) (hL : L ≤ r) :
    finalRegister r taps (List.zipWith Bool.xor (encodedBody r taps bits) e) ≠ 0#r := by
  intro hz
  have hc := (finalRegister_eq_zero_iff taps _).mp (finalRegister_encodedBody_eq_zero r taps bits)
  rw [finalRegister_eq_zero_iff,
    messagePoly_zipWith_xor _ _ (by rw [length_encodedBody, hlen]), add_mul] at hz
  exact not_dvd_messagePoly_mul_X_pow taps h0 e L he hL r ((dvd_add_right hc).mp hz)

/-- **Serial CRC burst detection.** For a monic binary generator `g` of degree `r` with
`g(0) = 1`, run as the `UnreflectedSerialCRC` serial LFSR with taps `g.toBitVec r`, every nonzero
nonwrapping burst of length at most `r` in the fixed-length codeword is rejected: the register
after the received word is nonzero. -/
theorem serialCRC_rejects_burst (g : Polynomial (ZMod 2)) (r : ℕ) (hg : g.Monic)
    (hr : g.natDegree = r) (hg0 : g.eval 0 = 1) (bits e : List Bool)
    (hlen : e.length = bits.length + r) (L : ℕ) (he : IsBitBurstLE e L) (hL : L ≤ r) :
    runRegister r (g.toBitVec r)
      (List.zipWith Bool.xor (encodedBody r (g.toBitVec r) bits) e) ≠ 0#r :=
  runRegister_ne_zero_of_isBitBurstLE r _
    (getLsbD_toBitVec_zero g r hg hr ((one_le_of_isBitBurstLE he).trans hL) hg0) bits e
    hlen L he hL

/-- **Serial CRC burst detection, augmented check.** Under the hypotheses of
`serialCRC_rejects_burst`, the register after the received word followed by `r` zero bits is
nonzero as well. -/
theorem serialCRC_rejects_burst_finalRegister (g : Polynomial (ZMod 2)) (r : ℕ) (hg : g.Monic)
    (hr : g.natDegree = r) (hg0 : g.eval 0 = 1) (bits e : List Bool)
    (hlen : e.length = bits.length + r) (L : ℕ) (he : IsBitBurstLE e L) (hL : L ≤ r) :
    finalRegister r (g.toBitVec r)
      (List.zipWith Bool.xor (encodedBody r (g.toBitVec r) bits) e) ≠ 0#r :=
  finalRegister_ne_zero_of_isBitBurstLE r _
    (getLsbD_toBitVec_zero g r hg hr ((one_le_of_isBitBurstLE he).trans hL) hg0) bits e
    hlen L he hL

end CSLibExt.Coding.SerialCRCBurstDetection
