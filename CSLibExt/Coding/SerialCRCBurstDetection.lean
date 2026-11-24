/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.UnreflectedSerialCRC
public import MathlibExt.Data.BitEncoding

@[expose] public section

/-!
# Serial CRC burst detection

The fixed-length codeword of the unreflected serial CRC in
`CSLibExt.Coding.UnreflectedSerialCRC`: the MSB-first payload followed by its
MSB-first check register. A nonzero error whose `true` bits lie in `L`
consecutive transmission positions is a polynomial burst of length at most
`L` (`isBurstLE_messagePoly_of_isBitBurstLE`), so the polynomial burst
detection theorem transfers through the serial bit order. When the generator
has constant coefficient `1`, every nonzero nonwrapping burst of length at
most the register width `r` in the codeword is rejected by recomputing the
serial CRC over the received word (`finalRegister_ne_zero_of_isBitBurstLE`,
and `serialCRC_rejects_burst` for a monic generator). The CRC-16/XMODEM
convention (width `16`, taps `0x1021`, check value `0x31C3` for the ASCII
payload `"123456789"`) is validated, including leading zero bytes, detection
of a length-16 burst, and the length-17 generator pattern that is not
detected.
-/

namespace CSLibExt.Coding.SerialCRCBurstDetection

/-- The field structure on `ZMod 2` used by `Cslib.CodingTheory.CRC`,
registered only while this module is elaborated. -/
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

open CSLibExt.Coding.UnreflectedSerialCRC

/-- The check register sent MSB first: `r` bits, bit `r - 1` of the register first. -/
def registerBits (r : ℕ) (w : BitVec r) : List Bool :=
  Nat.toBitsBE r w.toNat

/-- The fixed-length serial codeword: the MSB-first payload followed by its MSB-first check
register. -/
def serialCodeword (r : ℕ) (taps : BitVec r) (bits : List Bool) : List Bool :=
  bits ++ registerBits r (finalRegister r taps bits)

/-- A nonzero nonwrapping bit burst of length at most `L`: `e` has a `true` bit, and all its
`true` bits lie in the `L` consecutive positions `i, ..., i + L - 1`. -/
def IsBitBurstLE (e : List Bool) (L : ℕ) : Prop :=
  true ∈ e ∧ ∃ i : ℕ, ∀ j : ℕ, ∀ hj : j < e.length, e[j] = true → i ≤ j ∧ j < i + L


/-! #### Proof helpers

The polynomial side is the canonical one: a register `w` is read as `w.toPolynomial`, the
generator of the taps word is `taps.monicModulus`, and the final register is the shifted
message remainder by `final_register_represents_shifted_message_remainder`. The helpers below
only add the `messagePoly` facts for concatenation and XOR that the base module keeps private,
and the MSB-first transmission of the register. -/

open Polynomial

private theorem bitPoly_xor (a b : Bool) :
    bitPoly (Bool.xor a b) = bitPoly a + bitPoly b := by
  cases a <;> cases b <;> simp [bitPoly, CharTwo.add_self_eq_zero]

private theorem messagePoly_nil' : messagePoly [] = 0 := by
  simp [messagePoly]

private theorem messagePoly_cons' (b : Bool) (bits : List Bool) :
    messagePoly (b :: bits) = bitPoly b * X ^ bits.length + messagePoly bits := by
  unfold messagePoly
  simp only [List.length_cons, Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    have hexp : bits.length + 1 - 1 - (i.val + 1) = bits.length - 1 - i.val := by
      omega
    rw [List.get_cons_succ', Fin.val_succ, hexp]

private theorem messagePoly_append' (a b : List Bool) :
    messagePoly (a ++ b) = messagePoly a * X ^ b.length + messagePoly b := by
  induction a generalizing b with
  | nil => simp [messagePoly_nil']
  | cons x a ih =>
    rw [List.cons_append, messagePoly_cons', ih, List.length_append, messagePoly_cons',
      pow_add]
    ring

private theorem messagePoly_zipWith_xor (a b : List Bool) (h : a.length = b.length) :
    messagePoly (List.zipWith Bool.xor a b) = messagePoly a + messagePoly b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [messagePoly_nil']
    | cons _ _ => simp at h
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zipWith_cons_cons, messagePoly_cons', messagePoly_cons', messagePoly_cons',
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

/-- The register is zero exactly when the generator divides the shifted message. -/
private theorem finalRegister_eq_zero_iff {r : ℕ} (taps : BitVec r) (bits : List Bool) :
    finalRegister r taps bits = 0#r ↔ taps.monicModulus ∣ messagePoly bits * X ^ r := by
  rw [← modByMonic_eq_zero_iff_dvd (BitVec.monicModulus_monic taps),
    ← final_register_represents_shifted_message_remainder]
  constructor
  · intro h
    rw [h, BitVec.toPolynomial_zero]
  · exact eq_zero_of_toPolynomial_eq_zero _

private theorem toBitsBE_succ (r n : ℕ) :
    Nat.toBitsBE (r + 1) n = n.testBit r :: Nat.toBitsBE r n := by
  unfold Nat.toBitsBE
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_sub_cancel, Nat.sub_zero, List.cons.injEq,
    true_and]
  congr 1
  funext i
  congr 1
  omega

private theorem messagePoly_toBitsBE (r n : ℕ) :
    messagePoly (Nat.toBitsBE r n) = ∑ i ∈ Finset.range r, bitPoly (n.testBit i) * X ^ i := by
  induction r with
  | zero => simp [Nat.toBitsBE, messagePoly_nil']
  | succ r ih =>
    rw [toBitsBE_succ, messagePoly_cons', ih, Nat.length_toBitsBE, Finset.sum_range_succ,
      add_comm]

/-- The register sent MSB first is the canonical register polynomial. -/
private theorem messagePoly_registerBits {r : ℕ} (w : BitVec r) :
    messagePoly (registerBits r w) = w.toPolynomial := by
  ext k
  rw [registerBits, messagePoly_toBitsBE, finsetSum_coeff, BitVec.coeff_toPolynomial]
  simp only [coeff_bitPoly_mul_X_pow, BitVec.testBit_toNat]
  by_cases hk : k < r
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hk'
      simp at hk'
      omega
  · rw [BitVec.getLsbD_of_ge w k (by omega)]
    apply Finset.sum_eq_zero
    intro j hj
    simp at hj
    have : k ≠ j := by omega
    simp [this]

private theorem length_registerBits {r : ℕ} (w : BitVec r) : (registerBits r w).length = r :=
  Nat.length_toBitsBE r _

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

/-- The canonical modulus determines its taps word. -/
private theorem eq_of_monicModulus_eq {r : ℕ} {a b : BitVec r}
    (h : a.monicModulus = b.monicModulus) : a = b := by
  unfold BitVec.monicModulus at h
  simpa using congrArg (Polynomial.toBitVec r) (add_left_cancel h)

/-- The codeword has the fixed length `bits.length + r`. -/
theorem length_serialCodeword (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    (serialCodeword r taps bits).length = bits.length + r := by
  simp [serialCodeword, length_registerBits]

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

/-- The receiver accepts every error-free codeword: the zero-init unreflected CRC of a
codeword is the zero register. -/
theorem finalRegister_serialCodeword (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    finalRegister r taps (serialCodeword r taps bits) = 0#r := by
  rw [finalRegister_eq_zero_iff, serialCodeword, messagePoly_append', length_registerBits,
    messagePoly_registerBits, final_register_represents_shifted_message_remainder,
    modByMonic_eq_mod _ (BitVec.monicModulus_monic taps)]
  apply dvd_mul_of_dvd_left
  have h := Cslib.CodingTheory.CRC.dvd_encode taps.monicModulus (messagePoly bits)
  rwa [Cslib.CodingTheory.CRC.encode_eq_add, BitVec.monicModulus_natDegree] at h

/-- **Burst detection, taps form.** For a taps word with bit `0` set (generator
`X ^ r + taps` with constant coefficient `1`), every nonzero nonwrapping burst of length at most
`r` in the codeword is rejected by the serial CRC check. -/
theorem finalRegister_ne_zero_of_isBitBurstLE (r : ℕ) (hr : 1 ≤ r) (taps : BitVec r)
    (h0 : taps.getLsbD 0 = true) (bits e : List Bool) (hlen : e.length = bits.length + r)
    (L : ℕ) (he : IsBitBurstLE e L) (hL : L ≤ r) :
    finalRegister r taps (List.zipWith Bool.xor (serialCodeword r taps bits) e) ≠ 0#r := by
  intro hz
  have hc := (finalRegister_eq_zero_iff taps _).mp (finalRegister_serialCodeword r taps bits)
  rw [finalRegister_eq_zero_iff,
    messagePoly_zipWith_xor _ _ (by rw [length_serialCodeword, hlen]), add_mul] at hz
  have hdvd : taps.monicModulus ∣ messagePoly e * X ^ r := (dvd_add_right hc).mp hz
  have hburst : Cslib.CodingTheory.CRC.IsBurstLE (messagePoly e * X ^ r) L := by
    obtain ⟨i, b, heq, hb0, hbL⟩ := isBurstLE_messagePoly_of_isBitBurstLE e L he
    exact ⟨i + r, b, by rw [heq, pow_add]; ring, hb0, hbL⟩
  have hX : ¬X ∣ taps.monicModulus := by
    rw [X_dvd_iff, BitVec.monicModulus, coeff_add, BitVec.coeff_toPolynomial, h0, coeff_X_pow]
    have : (0 : ℕ) ≠ r := by omega
    simp [this]
  exact Cslib.CodingTheory.CRC.not_dvd_of_isBurstLE hX hburst
    (by rw [BitVec.monicModulus_natDegree]; exact hL) hdvd

/-- **Serial CRC burst detection.** For a monic binary generator `g` of degree `r ≥ 1` with
`g(0) = 1`, run as the `UnreflectedSerialCRC` serial LFSR with taps `g.toBitVec r`, every nonzero
nonwrapping burst of length at most `r` in the fixed-length codeword is rejected. -/
theorem serialCRC_rejects_burst (g : Polynomial (ZMod 2)) (r : ℕ) (hg : g.Monic)
    (hr : g.natDegree = r) (hr1 : 1 ≤ r) (hg0 : g.eval 0 = 1) (bits e : List Bool)
    (hlen : e.length = bits.length + r) (L : ℕ) (he : IsBitBurstLE e L) (hL : L ≤ r) :
    finalRegister r (g.toBitVec r)
      (List.zipWith Bool.xor (serialCodeword r (g.toBitVec r) bits) e) ≠ 0#r := by
  refine finalRegister_ne_zero_of_isBitBurstLE r hr1 _ ?_ bits e hlen L he hL
  have hc : (g.toBitVec r).monicModulus.coeff 0 = g.coeff 0 := by
    rw [BitVec.monicModulus_toBitVec g hg hr]
  rw [BitVec.monicModulus, coeff_add, coeff_X_pow, BitVec.coeff_toPolynomial,
    coeff_zero_eq_eval_zero g, hg0, ite_eq_right (by omega), zero_add] at hc
  revert hc
  cases (g.toBitVec r).getLsbD 0 <;> decide

/-! ### Validation: CRC-16/XMODEM -/

/-- The CRC-16/XMODEM generator `X^16 + X^12 + X^5 + 1`. -/
noncomputable def xmodemGenerator : Polynomial (ZMod 2) :=
  Polynomial.X ^ 16 + Polynomial.X ^ 12 + Polynomial.X ^ 5 + 1

/-- The CRC-16/XMODEM taps word `0x1021`. -/
def xmodemTaps : BitVec 16 :=
  0x1021#16

/-- The standard CRC check payload, ASCII `"123456789"`, as MSB-first bits, eight bits per
character. Every character of the literal is ASCII, so its low eight bits are its byte. -/
def xmodemCheckPayload : List Bool :=
  "123456789".toList.flatMap fun c => Nat.toBitsBE 8 c.toNat

private theorem monicModulus_xmodemTaps : xmodemTaps.monicModulus = xmodemGenerator := by
  have h : xmodemTaps.toBoolListLE = [true, false, false, false, false, true, false, false,
      false, false, false, false, true, false, false, false] := by decide
  simp only [BitVec.monicModulus, BitVec.toPolynomial, xmodemGenerator, h]
  simp [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil]
  ring

/-- The XMODEM generator enters the serial register model through the taps word `0x1021`. -/
theorem toBitVec_xmodemGenerator : xmodemGenerator.toBitVec 16 = xmodemTaps := by
  apply eq_of_monicModulus_eq
  rw [← monicModulus_xmodemTaps, BitVec.monicModulus_toBitVec _
    (BitVec.monicModulus_monic _) (BitVec.monicModulus_natDegree _)]

/-- CRC-16/XMODEM check value: the serial register over `"123456789"` is `0x31C3`. -/
theorem finalRegister_xmodem_check :
    finalRegister 16 xmodemTaps xmodemCheckPayload = 0x31C3#16 := by
  decide +kernel

/-- The transmitted XMODEM check frame is the payload followed by `0x31C3`, MSB first. -/
theorem serialCodeword_xmodem_check :
    serialCodeword 16 xmodemTaps xmodemCheckPayload =
      xmodemCheckPayload ++ Nat.toBitsBE 16 0x31C3 := by
  decide +kernel

/-- Leading zeros: a leading zero byte lengthens the payload but leaves the zero-init
XMODEM check value unchanged. -/
theorem finalRegister_xmodem_leading_zero_byte :
    finalRegister 16 xmodemTaps (List.replicate 8 false ++ xmodemCheckPayload) = 0x31C3#16 := by
  decide +kernel

/-- A length-16 burst (sixteen flipped bits at positions `3, ..., 18` of the 88-bit check
frame) is detected. -/
theorem xmodem_detects_length_sixteen_burst :
    IsBitBurstLE (List.replicate 3 false ++ List.replicate 16 true ++ List.replicate 69 false) 16 ∧
      finalRegister 16 xmodemTaps
        (List.zipWith Bool.xor (serialCodeword 16 xmodemTaps xmodemCheckPayload)
          (List.replicate 3 false ++ List.replicate 16 true ++ List.replicate 69 false)) ≠
        0#16 := by
  refine ⟨⟨by decide, 3, by decide⟩, by decide +kernel⟩

/-- A too-long error that is a multiple of `g` need not be detected: the 17-bit burst equal to
the generator `0x11021` itself, at positions `3, ..., 19` of the check frame, passes the check. -/
theorem xmodem_misses_generator_burst :
    IsBitBurstLE (List.replicate 3 false ++ Nat.toBitsBE 17 0x11021 ++ List.replicate 68 false)
        17 ∧
      finalRegister 16 xmodemTaps
        (List.zipWith Bool.xor (serialCodeword 16 xmodemTaps xmodemCheckPayload)
          (List.replicate 3 false ++ Nat.toBitsBE 17 0x11021 ++ List.replicate 68 false)) =
        0#16 := by
  refine ⟨⟨by decide, 3, by decide +kernel⟩, by decide +kernel⟩

/-- Violated premise `g(0) = 1`: for `g = X^2 + X` (taps `0b10`), the length-2 burst `11` on
the empty-payload codeword passes the check. -/
theorem misses_burst_of_generator_divisible_by_X :
    IsBitBurstLE [true, true] 2 ∧
      finalRegister 2 0b10#2 (List.zipWith Bool.xor (serialCodeword 2 0b10#2 []) [true, true]) =
        0#2 := by
  refine ⟨⟨by decide, 0, by decide⟩, by decide⟩

end CSLibExt.Coding.SerialCRCBurstDetection
