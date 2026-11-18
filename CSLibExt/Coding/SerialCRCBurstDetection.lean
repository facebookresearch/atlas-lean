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


/-! #### Proof helpers -/

open Polynomial

private theorem bitPoly_xor (a b : Bool) :
    bitPoly (Bool.xor a b) = bitPoly a + bitPoly b := by
  cases a <;> cases b <;> simp [bitPoly]
  exact (CharTwo.add_self_eq_zero 1).symm

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

private theorem messagePoly_replicate_false' (n : ℕ) :
    messagePoly (List.replicate n false) = 0 := by
  induction n with
  | zero => exact messagePoly_nil'
  | succ n ih => rw [List.replicate_succ, messagePoly_cons', ih]; simp [bitPoly]

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

/-- The register word read as a polynomial, bit `i` the coefficient of `X ^ i`. -/
private noncomputable def regPoly {r : ℕ} (w : BitVec r) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range r, bitPoly (w.getLsbD i) * X ^ i

private theorem coeff_bitPoly_mul_X_pow (b : Bool) (i k : ℕ) :
    (bitPoly b * X ^ i).coeff k = if b ∧ k = i then 1 else 0 := by
  cases b <;> simp [bitPoly, coeff_X_pow]

private theorem coeff_regPoly {r : ℕ} (w : BitVec r) (k : ℕ) :
    (regPoly w).coeff k = if w.getLsbD k then 1 else 0 := by
  unfold regPoly
  rw [finsetSum_coeff]
  simp only [coeff_bitPoly_mul_X_pow]
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

private theorem degree_regPoly_lt {r : ℕ} (w : BitVec r) : (regPoly w).degree < r := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  simp [coeff_regPoly, BitVec.getLsbD_of_ge w m hm]

private theorem regPoly_xor {r : ℕ} (a b : BitVec r) :
    regPoly (a ^^^ b) = regPoly a + regPoly b := by
  ext k
  simp only [coeff_add, coeff_regPoly, BitVec.getLsbD_xor]
  cases a.getLsbD k <;> cases b.getLsbD k <;> simp
  decide

private theorem eq_zero_of_regPoly_eq_zero {r : ℕ} (w : BitVec r) (h : regPoly w = 0) :
    w = 0#r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have hc := congrArg (fun p => p.coeff i) h
  simp only [coeff_regPoly, coeff_zero] at hc
  cases hw : w.getLsbD i
  · simp
  · rw [hw] at hc
    simp at hc

private theorem regPoly_zero (r : ℕ) : regPoly (0#r) = 0 := by
  ext k
  simp [coeff_regPoly]


/-- The generator `X ^ r + taps` of the taps word. -/
private noncomputable def genPoly {r : ℕ} (taps : BitVec r) : (ZMod 2)[X] :=
  X ^ r + regPoly taps

private theorem genPoly_monic {r : ℕ} (taps : BitVec r) : (genPoly taps).Monic :=
  monic_X_pow_add (degree_regPoly_lt taps)

private theorem natDegree_genPoly {r : ℕ} (taps : BitVec r) : (genPoly taps).natDegree = r := by
  unfold genPoly
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_regPoly_lt taps

private theorem coeff_ite_X_pow (c : Bool) (r k : ℕ) :
    (if c then (X ^ r : (ZMod 2)[X]) else 0).coeff k = if c ∧ k = r then 1 else 0 := by
  cases c <;> simp [coeff_X_pow]

private theorem regPoly_shiftLeft_one {r : ℕ} (w : BitVec r) :
    regPoly (w.shiftLeft 1) + (if w.getMsbD 0 then X ^ r else 0) = regPoly w * X := by
  ext k
  rw [coeff_add, coeff_regPoly, coeff_ite_X_pow, BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft,
    BitVec.getMsbD_eq_getLsbD]
  rcases k with _ | k
  · rw [coeff_mul_X_zero]
    split_ifs <;> simp_all
    omega
  · rw [coeff_mul_X, coeff_regPoly]
    by_cases hk : k + 1 < r
    · split_ifs <;> simp_all
    by_cases hk1 : k + 1 = r
    · subst hk1
      simp only [Nat.add_sub_cancel]
      cases w.getLsbD k <;> simp
    · rw [BitVec.getLsbD_of_ge w k (by omega)]
      split_ifs <;> simp_all
      omega


private theorem regPoly_inputBit (r : ℕ) (hr : 0 < r) (b : Bool) :
    regPoly (inputBit r b) = bitPoly b := by
  ext k
  rw [coeff_regPoly]
  cases b <;> by_cases hk : k = 0 <;> simp [inputBit, bitPoly, coeff_one, hk, hr]

private theorem regPoly_of_width_zero (w : BitVec 0) : regPoly w = 0 := by
  simp [regPoly]

private theorem genPoly_dvd_step {r : ℕ} (taps w : BitVec r) (b : Bool) :
    genPoly taps ∣ regPoly (stepRegister r taps w b) - (regPoly w * X + bitPoly b) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h1 : genPoly taps = 1 := by simp [genPoly, regPoly_of_width_zero]
    rw [h1]
    exact one_dvd _
  · have hs := regPoly_shiftLeft_one w
    unfold stepRegister BitVec.mulXMod
    cases hmsb : w.getMsbD 0
    · simp only [hmsb, Bool.false_eq_true, ite_false, add_zero] at hs ⊢
      rw [regPoly_xor, regPoly_inputBit r hr, hs, sub_self]
      exact dvd_zero _
    · simp only [hmsb, ite_true] at hs ⊢
      rw [regPoly_xor, regPoly_xor, regPoly_inputBit r hr]
      refine ⟨1, sub_eq_zero.mp ?_⟩
      unfold genPoly
      rw [← hs]
      calc _ = -((X : (ZMod 2)[X]) ^ r + X ^ r) := by ring
        _ = 0 := by rw [CharTwo.add_self_eq_zero, neg_zero]

private theorem genPoly_dvd_runState {r : ℕ} (taps : BitVec r) (bits : List Bool)
    (q : BitVec r) :
    genPoly taps ∣ regPoly ((serialLFSR r taps).runState q bits) -
      (regPoly q * X ^ bits.length + messagePoly bits) := by
  induction bits generalizing q with
  | nil =>
    have hnil : (serialLFSR r taps).runState q [] = q := rfl
    rw [hnil, messagePoly_nil']
    simp
  | cons b bits ih =>
    have hcons : (serialLFSR r taps).runState q (b :: bits) =
        (serialLFSR r taps).runState (stepRegister r taps q b) bits := rfl
    rw [hcons, messagePoly_cons', List.length_cons]
    have h := dvd_add (ih (stepRegister r taps q b))
      (dvd_mul_of_dvd_left (genPoly_dvd_step taps q b) (X ^ bits.length))
    convert h using 1
    ring

private theorem genPoly_dvd_runRegister {r : ℕ} (taps : BitVec r) (bits : List Bool) :
    genPoly taps ∣ regPoly (runRegister r taps bits) - messagePoly bits := by
  have h := genPoly_dvd_runState taps bits (0#r)
  rw [regPoly_zero, zero_mul, zero_add] at h
  exact h

private theorem genPoly_dvd_finalRegister {r : ℕ} (taps : BitVec r) (bits : List Bool) :
    genPoly taps ∣ regPoly (finalRegister r taps bits) - messagePoly bits * X ^ r := by
  have h := genPoly_dvd_runRegister taps (bits ++ List.replicate r false)
  rw [messagePoly_append', messagePoly_replicate_false', List.length_replicate,
    add_zero] at h
  exact h

/-- The register is zero exactly when the generator divides the shifted message. -/
private theorem finalRegister_eq_zero_iff {r : ℕ} (taps : BitVec r) (bits : List Bool) :
    finalRegister r taps bits = 0#r ↔ genPoly taps ∣ messagePoly bits * X ^ r := by
  have h := genPoly_dvd_finalRegister taps bits
  constructor
  · intro h0
    rw [h0, regPoly_zero, zero_sub, dvd_neg] at h
    exact h
  · intro hd
    apply eq_zero_of_regPoly_eq_zero
    have hreg : genPoly taps ∣ regPoly (finalRegister r taps bits) := by
      have := dvd_add h hd
      rwa [sub_add_cancel] at this
    apply eq_zero_of_dvd_of_degree_lt hreg
    rw [degree_eq_natDegree (genPoly_monic taps).ne_zero, natDegree_genPoly]
    exact degree_regPoly_lt _


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

private theorem length_toBitsBE (r n : ℕ) : (Nat.toBitsBE r n).length = r := by
  simp [Nat.toBitsBE]

private theorem messagePoly_toBitsBE (r n : ℕ) :
    messagePoly (Nat.toBitsBE r n) = ∑ i ∈ Finset.range r, bitPoly (n.testBit i) * X ^ i := by
  induction r with
  | zero => simp [Nat.toBitsBE, messagePoly_nil']
  | succ r ih =>
    rw [toBitsBE_succ, messagePoly_cons', ih, length_toBitsBE, Finset.sum_range_succ,
      add_comm]

private theorem messagePoly_registerBits {r : ℕ} (w : BitVec r) :
    messagePoly (registerBits r w) = regPoly w := by
  rw [registerBits, messagePoly_toBitsBE]
  rfl

private theorem length_registerBits {r : ℕ} (w : BitVec r) : (registerBits r w).length = r :=
  length_toBitsBE r _

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

private theorem isBurstLE_of_support' {F : Type*} [Field F] {e : F[X]} (he : e ≠ 0) {i L : ℕ}
    (h : ∀ j ∈ e.support, i ≤ j ∧ j < i + L) : Cslib.CodingTheory.CRC.IsBurstLE e L := by
  set t := e.natTrailingDegree
  obtain ⟨b, hb⟩ : X ^ t ∣ e := by
    rw [X_pow_dvd_iff]
    exact fun d hd ↦ coeff_eq_zero_of_lt_natTrailingDegree hd
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact he hb
  refine ⟨t, b, hb, ?_, ?_⟩
  · have hcoeff : e.coeff t = b.coeff 0 := by
      have := coeff_X_pow_mul b t 0
      rw [zero_add] at this
      rw [hb, this]
    rw [← hcoeff]
    exact mt trailingCoeff_eq_zero.mp he
  · have hdeg : e.natDegree = t + b.natDegree := by
      rw [hb, natDegree_mul (pow_ne_zero _ X_ne_zero) hb0, natDegree_X_pow]
    have h1 := h _ (natDegree_mem_support_of_nonzero he)
    have h2 := h _ (natTrailingDegree_mem_support_of_nonzero he)
    omega

private theorem not_dvd_of_isBurstLE' {F : Type*} [Field F] {g e : F[X]} (hX : ¬X ∣ g) {L : ℕ}
    (he : Cslib.CodingTheory.CRC.IsBurstLE e L) (hL : L ≤ g.natDegree) : ¬g ∣ e := by
  obtain ⟨i, b, rfl, hb0, hbL⟩ := he
  intro h
  have hcop : IsCoprime g (X ^ i) :=
    (((irreducible_X : Irreducible (X : F[X])).coprime_iff_not_dvd).mpr hX).symm.pow_right
  have hgb : g ∣ b := hcop.dvd_of_dvd_mul_left h
  have hb : b ≠ 0 := fun h0 ↦ hb0 (by rw [h0, coeff_zero])
  have := natDegree_le_of_dvd hgb hb
  omega

private theorem getLsbD_toBitVec (g : (ZMod 2)[X]) (r i : ℕ) :
    (g.toBitVec r).getLsbD i = (if i < r then decide (g.coeff i = 1) else false) := by
  unfold Polynomial.toBitVec
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  by_cases hi : i < r
  · have hl : i < (List.ofFn fun j : Fin r => decide (g.coeff j.val = 1)).length := by
      rw [List.length_ofFn]; exact hi
    simp only [hi, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
      List.getElem_ofFn]
  · have hl : (List.ofFn fun j : Fin r => decide (g.coeff j.val = 1)).length ≤ i := by
      rw [List.length_ofFn]; omega
    simp only [hi, ite_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, Option.getD_none]

/-- The codeword has the fixed length `bits.length + r`. -/
theorem length_serialCodeword (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    (serialCodeword r taps bits).length = bits.length + r := by
  simp [serialCodeword, length_registerBits]

/-- **Bit-order transfer.** Under the MSB-first order, a nonzero bit burst of length at most `L`
is a polynomial burst of length at most `L` in the sense of `Cslib.CodingTheory.CRC`. -/
theorem isBurstLE_messagePoly_of_isBitBurstLE (e : List Bool) (L : ℕ)
    (he : IsBitBurstLE e L) : Cslib.CodingTheory.CRC.IsBurstLE (messagePoly e) L := by
  obtain ⟨hmem, i, hi⟩ := he
  refine isBurstLE_of_support' (messagePoly_ne_zero e hmem) (i := e.length - (i + L)) ?_
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
    messagePoly_registerBits]
  apply dvd_mul_of_dvd_left
  have h := genPoly_dvd_finalRegister taps bits
  rwa [CharTwo.sub_eq_add, add_comm] at h

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
  have hdvd : genPoly taps ∣ messagePoly e * X ^ r := (dvd_add_right hc).mp hz
  have hburst : Cslib.CodingTheory.CRC.IsBurstLE (messagePoly e * X ^ r) L := by
    obtain ⟨i, b, heq, hb0, hbL⟩ := isBurstLE_messagePoly_of_isBitBurstLE e L he
    exact ⟨i + r, b, by rw [heq, pow_add]; ring, hb0, hbL⟩
  have hX : ¬X ∣ genPoly taps := by
    rw [X_dvd_iff, genPoly, coeff_add, coeff_regPoly, h0, coeff_X_pow]
    have : (0 : ℕ) ≠ r := by omega
    simp [this]
  exact not_dvd_of_isBurstLE' hX hburst (by rw [natDegree_genPoly]; exact hL) hdvd

/-- **Serial CRC burst detection.** For a monic binary generator `g` of degree `r ≥ 1` with
`g(0) = 1`, run as the `UnreflectedSerialCRC` serial LFSR with taps `g.toBitVec r`, every nonzero
nonwrapping burst of length at most `r` in the fixed-length codeword is rejected. -/
theorem serialCRC_rejects_burst (g : Polynomial (ZMod 2)) (r : ℕ) (hg : g.Monic)
    (hr : g.natDegree = r) (hr1 : 1 ≤ r) (hg0 : g.eval 0 = 1) (bits e : List Bool)
    (hlen : e.length = bits.length + r) (L : ℕ) (he : IsBitBurstLE e L) (hL : L ≤ r) :
    finalRegister r (g.toBitVec r)
      (List.zipWith Bool.xor (serialCodeword r (g.toBitVec r) bits) e) ≠ 0#r := by
  have _ := hg
  have _ := hr
  refine finalRegister_ne_zero_of_isBitBurstLE r hr1 _ ?_ bits e hlen L he hL
  rw [getLsbD_toBitVec, ite_eq_left (by omega), coeff_zero_eq_eval_zero, hg0]
  rfl

/-! ### Validation: CRC-16/XMODEM -/

/-- The CRC-16/XMODEM generator `X^16 + X^12 + X^5 + 1`. -/
noncomputable def xmodemGenerator : Polynomial (ZMod 2) :=
  Polynomial.X ^ 16 + Polynomial.X ^ 12 + Polynomial.X ^ 5 + 1

/-- The CRC-16/XMODEM taps word `0x1021`. -/
def xmodemTaps : BitVec 16 :=
  0x1021#16

/-- ASCII text as MSB-first bits, eight bits per character. -/
def asciiBits (s : String) : List Bool :=
  s.toList.flatMap fun c => Nat.toBitsBE 8 c.toNat

/-- The standard CRC check payload, ASCII `"123456789"`. -/
def xmodemCheckPayload : List Bool :=
  asciiBits "123456789"

/-- The XMODEM generator enters the serial register model through the taps word `0x1021`. -/
theorem toBitVec_xmodemGenerator : xmodemGenerator.toBitVec 16 = xmodemTaps := by
  have hc : ∀ i, xmodemGenerator.coeff i =
      if i = 16 ∨ i = 12 ∨ i = 5 ∨ i = 0 then 1 else 0 := by
    intro i
    simp only [xmodemGenerator, coeff_add, coeff_X_pow, coeff_one]
    by_cases h16 : i = 16 <;> by_cases h12 : i = 12 <;> by_cases h5 : i = 5 <;>
      by_cases h0 : i = 0 <;> simp_all
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_toBitVec, ite_eq_left hi, hc]
  revert i
  decide

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
