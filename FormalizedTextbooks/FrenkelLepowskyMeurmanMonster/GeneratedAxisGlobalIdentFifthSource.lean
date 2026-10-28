/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairFast
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFifthRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue

/-! # The Fifth axis as an identification vector

`fifthSrcVec : IdentVec` represents the canonical Fifth axis `generatedFifthAxis` (family
representative `4`): its matrix block, all `552 + 56 * 64` packet short coordinates (from two
small packed tables, checked against the canonical tables) and its tensor block as packed
columns computed in the kernel from the `64` odd root records.  `fifthSrc_actual` binds the
representation to the genuine coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false

/-! ## Matrix block -/

/-- The unit vector `e_i`, materialized. -/
def unitList (i : ℕ) : List ℚ := (List.range 24).map (fun j => if j = i then 1 else 0)

/-- The matrix block of the Fifth axis: `(1/4) I + (1/4) Σ e_i e_iᵀ` over the coordinates of
`0x0f000f`. -/
def fifthSrcMat : MatRep :=
  ⟨1 / 4, [0, 1, 2, 3, 16, 17, 18, 19].map (fun i => (1 / 4, unitList i))⟩

set_option maxRecDepth 100000 in
/-- The matrix block is the canonical diagonal matrix. -/
theorem fifthSrcMat_toMat : fifthSrcMat.toMat =
    Matrix.diagonal (fun i : Fin 24 => if Nat.testBit 0x0f000f i.val then (1 / 2 : ℚ) else 1 / 4) := by
  ext i j
  rw [MatRep.toMat_apply, Matrix.diagonal_apply]
  revert i j
  decide +kernel

/-! ## Short block -/

/-- Packed pair numerators (`8`-bit fields, offset `64`): sixteen times the middle matrix entry at
each catalogue pair. -/
@[irreducible] def fifthPairTable : ℕ :=
    (0x42423e3e3e3e42404042423e4240404040423e42423e3e3e424242423e404040 <<< 0) |||
    (0x423e40404040423e42423e3e3e423e3e3e424042423e4240404040423e424242 <<< 256) |||
    (0x40404040404040403c4042423e42404040403e423e3e3e3e3e423e3e3e423e3e <<< 512) |||
    (0x4040404040404040403e42424240404040404040404440404040403e42424240 <<< 768) |||
    (0x403c4040404040403e424242404040404040404040404040423e3e3e40404040 <<< 1024) |||
    (0x423e4040404040404040404242423e404040404044404040404242423e404040 <<< 1280) |||
    (0x3e4040404040403e423e3e404044404040403e3e3e4240404040404040404242 <<< 1536) |||
    (0x40423e3e3e40404040404040423e4242404040403e423e3e3c404040403e423e <<< 1792) |||
    (0x403c40404440423e3e3e423e3e3e403e42424240 <<< 2048)

/-- The pair numerator of catalogue pair `p`. -/
def fifthPairNum (p : ℕ) : ℤ := ((fifthPairTable >>> (8 * p)) % 256 : ℕ) - 64

set_option maxRecDepth 100000 in
/-- The pair numerators are sixteen times the middle matrix entries. -/
theorem fifthPairNum_spec : ∀ p : Fin 276, (fifthPairNum p.val : ℚ) =
    16 * generatedAxisGlobalFifthMiddleMatrixQ (generatedAxisGlobalPairCoordinates p).1
      (generatedAxisGlobalPairCoordinates p).2 := by
  decide +kernel

/-- Packed octad records (`24`-bit fields): catalogue index, sign label, phase bit. -/
@[irreducible] def fifthOctTable : ℕ :=
    (0x79fe00a0a1010c9e008a1b01261e001ca001b09f00361c019a1d01ec06006001 <<< 0) |||
    (0x020164820041ff01e48500920101348300120001b4840191fd001c020175fa00 <<< 256) |||
    (0x00d8e00048e100da3f008a4100f0c500a0c300f25d00625e0121fb00c80700c2 <<< 512) |||
    (0x60ec008e3500623301e4b70108b901e66901f66701cceb01dced01ce34012236 <<< 768) |||
    (0xc40070c2000a40005a420108de0198df00a4b80048b6015a6a014a680170ea01 <<< 1024) |||
    (0x1225b01b25c0020 <<< 1280)

/-- The catalogue index of octad record `j`. -/
def fifthOctIdx (j : ℕ) : ℕ := (fifthOctTable >>> (24 * j)) % 1024

/-- The sign label of octad record `j`. -/
def fifthOctSign (j : ℕ) : ℕ := (fifthOctTable >>> (24 * j + 10)) % 64

/-- The phase bit of octad record `j`. -/
def fifthOctPhase (j : ℕ) : Bool := (fifthOctTable >>> (24 * j + 16)) % 2 == 1

set_option maxRecDepth 100000 in
/-- The octad records are the canonical octad data. -/
theorem fifthOct_spec : ∀ j : Fin 56,
    fifthOctIdx j.val < 759 ∧ identOctCode (fifthOctIdx j.val) = (generatedFifthEvenRootCode j).val ∧
    fifthOctSign j.val = (generatedFifthEvenRootSign j).val ∧
    fifthOctPhase j.val = decide (generatedAxisGlobalFifthShortOctadPhaseData j = 1) := by
  decide +kernel

/-- The recorded catalogue index is the canonical octad. -/
theorem fifthOctIdx_eq (j : Fin 56) : (generatedFifthEvenRootOctad j).val = fifthOctIdx j.val := by
  obtain ⟨h1, h2, -, -⟩ := fifthOct_spec j
  have h : generatedFifthEvenRootOctad j = ⟨fifthOctIdx j.val, h1⟩ := by
    apply golayOctadLabel_injective
    rw [generatedFifthEvenRootOctad_label, ← identOctCode_actual]
    apply Fin.ext
    simp only [identOctCodeFin]
    rw [h2]
  rw [h]

/-- The octad Fourier matrix from the packed tables, as an integer. -/
def octIntF (e s : ℕ) : ℤ :=
  (if identOctDiagTable.testBit e then -1 else 1) *
    (if identParityTable.testBit (identEvenMask e &&& identEvenMask s) then -1 else 1)

/-- The fast octad Fourier matrix is the original one. -/
theorem octIntF_eq (a b : Fin 64) : octIntF a.val b.val = trialityIntegerMatrix a b := by
  have hd := identOctDiagTable_spec a
  have hp := identParityTable_spec ⟨_, evenMask_and_lt a b⟩
  simp only at hp
  simp only [identEvenMask_actual] at hp
  rw [trialityIntegerMatrix, ← hd, trialityHadamard, octIntF]
  simp only [identEvenMask_actual]
  rw [hp]
  rcases Nat.mod_two_eq_zero_or_one
    (trialityBitWeight8 (trialityEvenMask a &&& trialityEvenMask b)) with h | h
  · simp [h]
  · simp [h]

/-- The octad numerator of record `j` at sign label `e`. -/
def fifthOctNum (j e : ℕ) : ℤ :=
  2 * octIntF e (fifthOctSign j) * (if fifthOctPhase j then -1 else 1)

/-- The pair terms of the Fifth axis. -/
@[irreducible] def fifthSrcPairs : List (ℕ × ℤ) :=
  (List.finRange 276).map (fun p => (p.val, fifthPairNum p.val)) ++
    (List.finRange 276).map (fun p => (276 + p.val, -fifthPairNum p.val))

/-- The octad blocks of the Fifth axis. -/
@[irreducible] def fifthSrcOct : List (ℕ × List (ℕ × ℤ)) :=
  (List.finRange 56).map (fun j => (fifthOctIdx j.val,
    (List.finRange 64).map (fun e => (e.val, fifthOctNum j.val e.val))))

/-- The sparse short block of the Fifth axis (scale `1/16`). -/
@[irreducible] def fifthSrcShort : ShortData := ⟨fifthSrcPairs, fifthSrcOct, []⟩

/-- Short coordinates of a mapped list over `Fin n`. -/
theorem shortFunQ_map_finRange {n : ℕ} (F : Fin n → ℕ × ℤ) (r : GriessShortIndex) :
    shortFunQ ((List.finRange n).map F) r =
      ∑ p : Fin n, if shortDecode (F p).1 = r then ((F p).2 : ℚ) else 0 := by
  rw [shortFunQ, List.map_map, Fin.sum_univ_def]
  rfl

/-- Short coordinates of the flat octad blocks of a mapped list. -/
theorem shortFunQ_octsFlat_map {α : Type*} (G : α → ℕ × List (ℕ × ℤ)) (r : GriessShortIndex) :
    ∀ L : List α, shortFunQ (octsFlat (L.map G)) r =
      (L.map (fun x => shortFunQ (octFlat (G x).1 (G x).2) r)).sum
  | [] => rfl
  | x :: L => by
    simp only [List.map_cons, octsFlat, List.sum_cons]
    rw [shortFunQ_append, shortFunQ_octsFlat_map G r L]

/-- Short coordinates of the empty list. -/
theorem shortFunQ_nil (r : GriessShortIndex) : shortFunQ [] r = 0 := rfl

/-- The short block is the canonical short block. -/
theorem fifthSrcShort_spec (r : GriessShortIndex) :
    (1 / 16 : ℚ) * shortFunQ fifthSrcShort.flat r = generatedAxisGlobalCanonicalFifthShortQ r := by
  simp only [ShortData.flat, fifthSrcShort, fifthSrcPairs, fifthSrcOct, shortFunQ_append,
    shortFunQ_nil, add_zero, shortFunQ_map_finRange, shortFunQ_octsFlat_map]
  rw [generatedAxisGlobalCanonicalFifthShortQ, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type, Fin.sum_univ_two, ← Fin.sum_univ_def, mul_add, mul_add,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    have hd : shortDecode p.val = Sum.inl (0, p) := by
      have h := shortDecode_encode (Sum.inl (0, p))
      simpa [shortEncode] using h
    rw [hd]
    simp only [generatedAxisGlobalFifthShortPacketLabel,
      generatedAxisGlobalFifthShortRationalCoefficient, ↓reduceIte]
    by_cases hr : (Sum.inl (0, p) : GriessShortIndex) = r
    · simp only [hr, ↓reduceIte]
      rw [fifthPairNum_spec, generatedAxisGlobalPairCoordinates_actual]; ring
    · simp only [hr, ↓reduceIte, mul_zero]
  · apply Finset.sum_congr rfl
    intro p _
    have hd : shortDecode (276 + p.val) = Sum.inl (1, p) := by
      have h := shortDecode_encode (Sum.inl (1, p))
      simpa [shortEncode] using h
    rw [hd]
    simp only [generatedAxisGlobalFifthShortPacketLabel,
      generatedAxisGlobalFifthShortRationalCoefficient, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      ↓reduceIte]
    by_cases hr : (Sum.inl (1, p) : GriessShortIndex) = r
    · simp only [hr, ↓reduceIte]
      push_cast
      rw [fifthPairNum_spec, generatedAxisGlobalPairCoordinates_actual]; ring
    · simp only [hr, ↓reduceIte, mul_zero]
  · apply Finset.sum_congr rfl
    intro j _
    rw [shortFunQ, octFlat, List.map_map, List.map_map, ← Fin.sum_univ_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    have hd : shortDecode (552 + 64 * fifthOctIdx j.val + e.val) =
        Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e)) := by
      have h := shortDecode_encode (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e)))
      simp only [shortEncode, fifthOctIdx_eq] at h
      exact h
    simp only [Function.comp_apply]
    rw [hd]
    simp only [generatedAxisGlobalFifthShortPacketLabel,
      generatedAxisGlobalFifthShortRationalCoefficient]
    obtain ⟨-, -, hs, hph⟩ := fifthOct_spec j
    by_cases hr : Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e)) = r
    · simp only [hr, ↓reduceIte]
      rw [fifthOctNum, hs, hph, octIntF_eq e (generatedFifthEvenRootSign j)]
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (generatedAxisGlobalFifthShortOctadPhaseData j)
        with hc | hc
      · simp only [hc, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte]
        push_cast; ring
      · simp only [hc, decide_true, ↓reduceIte, one_ne_zero]
        push_cast; ring
    · simp only [hr, ↓reduceIte, mul_zero]

/-! ## Tensor block -/

/-- A single signed entry: `v` at label `d` and `-v` at label `d + 2048`. -/
def unitVec (w d : ℕ) (v : ℤ) : SVec :=
  if 0 ≤ v then (v.toNat <<< (w * d), v.toNat <<< (w * (d + 2048)))
  else ((-v).toNat <<< (w * (d + 2048)), (-v).toNat <<< (w * d))

/-- Fields of a single small number shifted to field `d`. -/
theorem fld_single (w c d k : ℕ) (hc : c < 2 ^ w) :
    fld w (c <<< (w * d)) k = if k = d then c else 0 := by
  rw [fld_shiftLeft]
  by_cases hk : k = d
  · subst hk
    simp [fld_zero_right, Nat.mod_eq_of_lt hc]
  · simp only [hk, ↓reduceIte]
    split_ifs with hdk
    · obtain ⟨m, hm⟩ : ∃ m, k - d = m + 1 := ⟨k - d - 1, by omega⟩
      rw [hm, fld_succ, Nat.div_eq_of_lt hc, fld_zero_right_zero]
    · rfl

/-- A small number shifted to a field below `n` fits in `n` fields. -/
theorem single_lt (w c d n : ℕ) (hc : c < 2 ^ w) (hd : d < n) : c <<< (w * d) < 2 ^ (w * n) := by
  rw [Nat.shiftLeft_eq]
  calc c * 2 ^ (w * d) < 2 ^ w * 2 ^ (w * d) :=
        Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = 2 ^ (w * (d + 1)) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (w * n) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w hd)

/-- Bounds and values of a single signed entry. -/
theorem unitVec_spec (w d : ℕ) (v : ℤ) (hd : d < 2048) (hv : v.natAbs < 2 ^ w) :
    SBnd w (2 ^ 12) v.natAbs (unitVec w d v) ∧ ∀ k, sval w (unitVec w d v) k =
      if k = d then v else if k = d + 2048 then -v else 0 := by
  have hd1 : d < 2 ^ 12 := by omega
  have hd2 : d + 2048 < 2 ^ 12 := by omega
  by_cases h0 : 0 ≤ v
  · have hn : v.toNat < 2 ^ w := by omega
    have hn' : v.toNat = v.natAbs := by omega
    simp only [unitVec, h0, ↓reduceIte]
    refine ⟨⟨single_lt w _ d _ hn hd1, single_lt w _ _ _ hn hd2, fun k _ => ?_⟩, fun k => ?_⟩
    · rw [fld_single w _ _ _ hn, fld_single w _ _ _ hn]
      constructor <;> split_ifs <;> omega
    · simp only [sval]
      rw [fld_single w _ _ _ hn, fld_single w _ _ _ hn]
      by_cases h1 : k = d
      · simp [h1]; omega
      · by_cases h2 : k = d + 2048
        · simp [h2]; omega
        · simp [h1, h2]
  · have hn : (-v).toNat < 2 ^ w := by omega
    have hn' : (-v).toNat = v.natAbs := by omega
    simp only [unitVec, h0, ↓reduceIte]
    refine ⟨⟨single_lt w _ _ _ hn hd2, single_lt w _ d _ hn hd1, fun k _ => ?_⟩, fun k => ?_⟩
    · rw [fld_single w _ _ _ hn, fld_single w _ _ _ hn]
      constructor <;> split_ifs <;> omega
    · simp only [sval]
      rw [fld_single w _ _ _ hn, fld_single w _ _ _ hn]
      by_cases h1 : k = d
      · simp [h1]; omega
      · by_cases h2 : k = d + 2048
        · simp [h2]; omega
        · simp [h1, h2]

/-- The value of odd root record `r` of the Fifth tensor. -/
def fifthRootVal (r : Fin 64) : ℤ :=
  generatedAxisGlobalIntSign (generatedFifthOddCoefficientPhaseData r) *
    (if (golayEncodedMask (generatedFifthOddRootOutputData r).1.val).testBit
      (generatedFifthOddRootOutputData r).2.val then -1 else 1)

/-- Record values are signs. -/
theorem fifthRootVal_natAbs (r : Fin 64) : (fifthRootVal r).natAbs = 1 := by
  unfold fifthRootVal generatedAxisGlobalIntSign
  split_ifs <;> decide

/-- The contribution of record `r` to column `i`. -/
def fifthTerm (i : ℕ) (r : Fin 64) : SVec :=
  if (generatedFifthOddRootOutputData r).2.val = i then
    unitVec 128 (generatedFifthOddRootOutputData r).1.val (fifthRootVal r) else szero

/-- Column `i` of the Fifth tensor. -/
def fifthCol (i : ℕ) : SVec := ssum ((List.finRange 64).map (fifthTerm i))

/-- The packed Fifth tensor. -/
@[irreducible] def fifthSrcX : List SVec := (List.range 24).map fifthCol

/-- Bounds and values of one record contribution. -/
theorem fifthTerm_spec (i : ℕ) (r : Fin 64) :
    SBnd 128 (2 ^ 12) 1 (fifthTerm i r) ∧ ∀ k, sval 128 (fifthTerm i r) k =
      if (generatedFifthOddRootOutputData r).2.val = i then
        (if k = (generatedFifthOddRootOutputData r).1.val then fifthRootVal r
          else if k = (generatedFifthOddRootOutputData r).1.val + 2048 then -fifthRootVal r
          else 0) else 0 := by
  unfold fifthTerm
  split_ifs with h
  · have hu := unitVec_spec 128 (generatedFifthOddRootOutputData r).1.val (fifthRootVal r)
      (generatedFifthOddRootOutputData r).1.isLt (by rw [fifthRootVal_natAbs]; norm_num)
    rw [fifthRootVal_natAbs] at hu
    exact hu
  · exact ⟨SBnd_zero _ _ _, fun k => sval_zero _ _⟩

/-- Bounds and values of a column. -/
theorem fifthCol_spec (i : ℕ) :
    SBnd 128 (2 ^ 12) 64 (fifthCol i) ∧ ∀ k < 4096, sval 128 (fifthCol i) k =
      ∑ r : Fin 64, sval 128 (fifthTerm i r) k := by
  have h := ssum_spec (w := 128) (n := 2 ^ 12) (B := 1) ((List.finRange 64).map (fifthTerm i))
    (fun x hx => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact (fifthTerm_spec i r).1) (by simp)
  simp only [List.length_map, List.length_finRange, mul_one] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rw [fifthCol, h.2 k (by norm_num; exact hk), List.map_map, Fin.sum_univ_def]
  rfl

/-- Bounds of the packed Fifth tensor. -/
theorem fifthSrcX_bnd : TBnd 128 64 fifthSrcX := by
  intro i hi
  rw [fifthSrcX, tcol_range_map _ 24 i hi]
  exact (fifthCol_spec i).1

/-- Bit `11` of a label as a coefficient. -/
theorem coeff11_eq (k : Fin 4096) :
    golayLabelCoefficients k 11 = if k.val.testBit 11 then 1 else 0 := rfl

/-- One record of the Fifth tensor: the packed contribution is the canonical term. -/
theorem fifth_record_term (k : Fin 4096) (i : Fin 24) (d : Fin 2048) (j : Fin 24) (ph : ZMod 2) :
    (if j.val = i.val then
      (if k.val = d.val then generatedAxisGlobalIntSign ph *
          (if (golayEncodedMask d.val).testBit j.val then -1 else 1)
        else if k.val = d.val + 2048 then -(generatedAxisGlobalIntSign ph *
          (if (golayEncodedMask d.val).testBit j.val then -1 else 1))
        else 0) else 0) =
    generatedAxisGlobalIntSign (ph + golayLabelCoefficients k 11) *
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
      (if k.val % 2048 = d.val ∧ i = j then 1 else 0) := by
  have hd := d.isLt
  have hk := k.isLt
  rw [coeff11_eq]
  by_cases hij : j.val = i.val
  · have hji : i = j := Fin.ext hij.symm
    subst hji
    simp only [↓reduceIte, and_true]
    by_cases h1 : k.val = d.val
    · have hm : d.val % 2048 = d.val := Nat.mod_eq_of_lt hd
      have hb : d.val.testBit 11 = false := Nat.testBit_lt_two_pow (by omega)
      simp [h1, hm, hb]
    · by_cases h2 : k.val = d.val + 2048
      · have hm : (d.val + 2048) % 2048 = d.val := by omega
        have hne : ¬ d.val + 2048 = d.val := by omega
        have hb : (d.val + 2048).testBit 11 = true := by
          have e : d.val + 2048 = 2 ^ 11 + d.val := by omega
          rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]
          rfl
        simp only [h2, hm, hb, hne, ↓reduceIte, intSign_add, mul_one]
        rw [show generatedAxisGlobalIntSign 1 = -1 by rfl]
        ring
      · have hm : ¬ k.val % 2048 = d.val := by omega
        simp [h1, h2, hm]
  · have hji : ¬ i = j := fun h => hij (by rw [h])
    simp [hij, hji]

/-- The packed Fifth tensor is the canonical integer tensor. -/
theorem fifthSrcX_val (k : Fin 4096) (i : Fin 24) :
    sval 128 (tcol fifthSrcX i.val) k.val = generatedAxisGlobalFifthTensorInteger k i := by
  rw [fifthSrcX, tcol_range_map _ 24 i.val i.isLt, (fifthCol_spec i.val).2 k.val k.isLt,
    generatedAxisGlobalFifthTensorInteger]
  apply Finset.sum_congr rfl
  intro r _
  rw [(fifthTerm_spec i.val r).2 k.val, fifthRootVal]
  exact fifth_record_term k i _ _ _

/-! ## The identification vector -/

/-- The Fifth axis as an identification vector. -/
def fifthSrcVec : IdentVec := ⟨fifthSrcMat, fifthSrcShort, 1 / 16, tensorRat 128 fifthSrcX 1⟩

/-- The matrix block of the Fifth representation. -/
theorem fifthSrcVec_mat : fifthSrcVec.mat = fifthSrcMat := rfl

/-- The short block of the Fifth representation. -/
theorem fifthSrcVec_sh : fifthSrcVec.sh = fifthSrcShort := rfl

/-- The short scale of the Fifth representation. -/
theorem fifthSrcVec_sden : fifthSrcVec.sden = 1 / 16 := rfl

/-- The tensor block of the Fifth representation. -/
theorem fifthSrcVec_ten : fifthSrcVec.ten = tensorRat 128 fifthSrcX 1 := rfl

set_option maxRecDepth 20000 in
/-- The rational packet of the representation is the canonical Fifth packet. -/
theorem fifthSrcVec_packet : fifthSrcVec.packet = generatedAxisGlobalCanonicalFifthRationalPacket := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact fifthSrcMat_toMat
  · show (fun r => fifthSrcVec.sden * shortFunQ fifthSrcVec.sh.flat r) =
      generatedAxisGlobalCanonicalFifthShortQ
    funext r
    exact fifthSrcShort_spec r
  · show (fun t i => fifthSrcVec.ten (generatedAxisGlobalSpinLabel t) i) =
      fun t i => (generatedAxisGlobalFifthTensorInteger (generatedAxisGlobalSpinLabel t) i : ℚ)
    funext t i
    have h1 : fifthSrcVec.ten (generatedAxisGlobalSpinLabel t) i =
        tensorRat 128 fifthSrcX 1 (generatedAxisGlobalSpinLabel t) i := rfl
    have h2 : tensorRat 128 fifthSrcX 1 (generatedAxisGlobalSpinLabel t) i =
        (sval 128 (tcol fifthSrcX i.val) (generatedAxisGlobalSpinLabel t).val : ℚ) / 1 := rfl
    rw [h1, h2, div_one, fifthSrcX_val]

/-- The representation gives the genuine coordinates of the Fifth axis. -/
theorem fifthSrc_actual : griessConwayEncode generatedFifthAxis = fifthSrcVec.real := by
  rw [generatedAxisGlobalCanonicalFifthRationalPacket_actual, IdentVec.real, fifthSrcVec_packet]

/-- The representation of family representative `4`. -/
theorem fifthSrc_rep : griessConwayEncode (generatedAxisGlobalTwelveRepresentative 4) =
    fifthSrcVec.real := fifthSrc_actual

set_option maxRecDepth 100000 in
/-- The short block satisfies the range conditions. -/
theorem fifthSrcVec_ok : fifthSrcVec.sh.ok = true := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
