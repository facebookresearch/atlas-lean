/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthSparseShortPacket

/-! # The Fourth axis as an identification vector

`fourthSrcVec : IdentVec` represents the canonical Fourth axis `generatedFourthAxis` (family
representative `3`) in the format of the packed identification method (workers `gident`,
`gident2`), following `fifthSrcVec`: the matrix block `3/8 I` plus eight rank-one terms, all
`552 + 63 * 64` packet short coordinates (two small packed tables checked against the canonical
tables) and the tensor block as packed columns computed in the kernel from the `56` odd root
records.  `fourthSrc_rep` binds the representation to the genuine coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-! ## Matrix block -/

/-- The materialized vector `e_8 + s e_11`. -/
def fourthPairList (s : ℚ) : List ℚ :=
  (List.range 24).map (fun j => if j = 8 then 1 else if j = 11 then s else 0)

/-- The matrix block of the Fourth axis: `3/8 I`, minus `1/4` on six coordinates of the
octad block, and the rank-two block on the coordinates `8, 11`. -/
def fourthSrcMat : MatRep :=
  ⟨3 / 8, [4, 5, 6, 7, 9, 10].map (fun i => (-1 / 4, unitList i)) ++
    [(-1 / 8, fourthPairList 1), (3 / 8, fourthPairList (-1))]⟩

/-- The canonical Fourth matrix in computable form. -/
theorem fourth_matrix_eq (i j : Fin 24) :
    generatedAxisGlobalCanonicalFourthMatrixQ i j =
      if i = j then (generatedFourthProjectionDiagonal i : ℚ) / 16 else
        if (if i < j then (i, j) else (j, i)) = ((8 : Fin 24), (11 : Fin 24)) then -1 / 2
          else 0 := by
  unfold generatedAxisGlobalCanonicalFourthMatrixQ
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ↓reduceDIte, ↓reduceIte, griessPairIndex_coordinates]

set_option maxRecDepth 100000 in
/-- The matrix block is the canonical Fourth matrix. -/
theorem fourthSrcMat_toMat : fourthSrcMat.toMat = generatedAxisGlobalCanonicalFourthMatrixQ := by
  ext i j
  rw [MatRep.toMat_apply, fourth_matrix_eq]
  revert i j
  decide +kernel

/-! ## Short block -/

/-- Packed pair numerators (`8`-bit fields, offset `64`): eight times the canonical pair
coordinate at flat pair label `276 * s + p`. -/
@[irreducible] def fourthPairTable : ℕ :=
    (0x40404040404040414141413f414141413f413f414140404040404040403f3f41 <<< 0) |||
    (0x3f413f3f3f413f413f3f40404040404040403f41413f413f3f3f41413f414140 <<< 256) |||
    (0x404040413f3f3f3f3f3f3f3f413f3f3f3f41413f414140404040404040404141 <<< 512) |||
    (0x3f414141414040404040404040404040403f4141414141404040404040404040 <<< 768) |||
    (0x404741414040404040404040404040403f414141404040404040404040404040 <<< 1024) |||
    (0x4040404040403f4040404040404040404040403f414040404040404040404040 <<< 1280) |||
    (0x3f41413f3f3f413f413f3f3f3f41404040404040404040404040404040404040 <<< 1536) |||
    (0x3f413f3f3f413f3f4141413f413f41414141413f3f413f3f3f4141413f3f413f <<< 1792) |||
    (0x3f404040404040404041413f413f413f413f413f3f3f413f3f3f413f41414141 <<< 2048) |||
    (0x3f413f4141413f3f413f3f40404040404040403f3f3f3f413f3f3f3f413f413f <<< 2304) |||
    (0x3f3f40404040404040403f3f413f4141413f413f41414040404040404040413f <<< 2560) |||
    (0x3f3f3f4040404040404040404040403f41414141414141413f414141413f3f41 <<< 2816) |||
    (0x404040404040404040404040413f3f3f3f404040404040404040404040413f3f <<< 3072) |||
    (0x3f404040404040404040404040413f3f404040404040404040404040413f3f3f <<< 3328) |||
    (0x4040404040404040404040404040404040404140404040404040404040404041 <<< 3584) |||
    (0x413f4141413f3f3f41413f41413f3f4141413f413f414141413f404040404040 <<< 3840) |||
    (0x41413f4141413f413f3f3f3f413f4141413f41413f3f3f413f413f3f3f3f3f41 <<< 4096) |||
    (0x3f413f413f413f41 <<< 4352)

/-- The pair numerator at flat pair label `q`. -/
def fourthPairNum (q : ℕ) : ℤ := ((fourthPairTable >>> (8 * q)) % 256 : ℕ) - 64

/-- The canonical pair coordinate with the computable pair table. -/
def fourthPairQ (s : ℕ) (p : Fin 276) : ℚ :=
  let M := generatedAxisGlobalCanonicalFourthMiddleMatrixQ (generatedAxisGlobalPairCoordinates p).1
    (generatedAxisGlobalPairCoordinates p).2
  let z : ℚ := if generatedAxisGlobalPairCoordinates p = (8, 11) then 1 / 2 else 0
  if s = 0 then M + z else z - M

/-- The computable pair coordinate is the canonical one (first family). -/
theorem fourthPairQ_zero (p : Fin 276) :
    fourthPairQ 0 p = generatedAxisGlobalCanonicalFourthPairShortQ 0 p := by
  unfold fourthPairQ generatedAxisGlobalCanonicalFourthPairShortQ
  rw [generatedAxisGlobalPairCoordinates_actual]
  rfl

/-- The computable pair coordinate is the canonical one (second family). -/
theorem fourthPairQ_one (p : Fin 276) :
    fourthPairQ 1 p = generatedAxisGlobalCanonicalFourthPairShortQ 1 p := by
  unfold fourthPairQ generatedAxisGlobalCanonicalFourthPairShortQ
  rw [generatedAxisGlobalPairCoordinates_actual]
  rfl

set_option maxRecDepth 100000 in
/-- The pair numerators are eight times the canonical pair coordinates. -/
theorem fourthPairNum_spec : ∀ p : Fin 276,
    (fourthPairNum p.val : ℚ) = 8 * fourthPairQ 0 p ∧
      (fourthPairNum (276 + p.val) : ℚ) = 8 * fourthPairQ 1 p := by
  decide +kernel

/-- Packed octad records (`24`-bit fields): catalogue index, sign label, phase bit. -/
@[irreducible] def fourthOctTable : ℕ :=
    (0xd6270180ad00962a01c0aa01965200c0d201c6510090d30144050079fc00f809 <<< 0) |||
    (0x8301a1fd001c02005cab010a29001cac014a28011cd4004a50014cd5001a4f00 <<< 256) |||
    (0x17e0e0111fb00c8070141ff00e88501c20200688201120000b8840192010038 <<< 512) |||
    (0xccb700fcb700901b019c1b01320b00020b013a5b000a5b01b0df0080df004e0e <<< 768) |||
    (0x21007a33014a33008cb801bcb801c01c00cc1c014c1e00401e013a36000a3601 <<< 1024) |||
    (0x1349000049001c0e000f0e0014a5e007a5e00488f01788f001c210110 <<< 1280)

/-- The catalogue index of octad record `j`. -/
def fourthOctIdx (j : ℕ) : ℕ := (fourthOctTable >>> (24 * j)) % 1024

/-- The sign label of octad record `j`. -/
def fourthOctSign (j : ℕ) : ℕ := (fourthOctTable >>> (24 * j + 10)) % 64

/-- The phase bit of octad record `j`. -/
def fourthOctPhase (j : ℕ) : Bool := (fourthOctTable >>> (24 * j + 16)) % 2 == 1

set_option maxRecDepth 100000 in
/-- The octad records are the canonical octad data. -/
theorem fourthOct_spec : ∀ j : Fin 63,
    fourthOctIdx j.val < 759 ∧
    identOctCode (fourthOctIdx j.val) = (generatedFourthEvenRootCode j).val ∧
    fourthOctSign j.val = (generatedFourthEvenRootSign j).val ∧
    fourthOctPhase j.val = decide (generatedFourthEvenCoefficientCache j = 1) := by
  decide +kernel

/-- The recorded catalogue index is the canonical octad. -/
theorem fourthOctIdx_eq (j : Fin 63) :
    (generatedFourthEvenRootOctad j).val = fourthOctIdx j.val := by
  obtain ⟨h1, h2, -, -⟩ := fourthOct_spec j
  have h : generatedFourthEvenRootOctad j = ⟨fourthOctIdx j.val, h1⟩ := by
    apply golayOctadLabel_injective
    rw [generatedFourthEvenRootOctad_label, ← identOctCode_actual]
    apply Fin.ext
    simp only [identOctCodeFin]
    rw [h2]
  rw [h]

/-- The octad numerator of record `j` at sign label `e`. -/
def fourthOctNum (j e : ℕ) : ℤ := octIntF e (fourthOctSign j) * (if fourthOctPhase j then -1 else 1)

/-- The pair terms of the Fourth axis. -/
@[irreducible] def fourthSrcPairs : List (ℕ × ℤ) :=
  (List.finRange 276).map (fun p => (p.val, fourthPairNum p.val)) ++
    (List.finRange 276).map (fun p => (276 + p.val, fourthPairNum (276 + p.val)))

/-- The octad blocks of the Fourth axis. -/
@[irreducible] def fourthSrcOct : List (ℕ × List (ℕ × ℤ)) :=
  (List.finRange 63).map (fun j => (fourthOctIdx j.val,
    (List.finRange 64).map (fun e => (e.val, fourthOctNum j.val e.val))))

/-- The sparse short block of the Fourth axis (scale `1/8`). -/
@[irreducible] def fourthSrcShort : ShortData := ⟨fourthSrcPairs, fourthSrcOct, []⟩

/-- The short block is the canonical sparse short block. -/
theorem fourthSrcShort_spec (r : GriessShortIndex) :
    (1 / 8 : ℚ) * shortFunQ fourthSrcShort.flat r =
      generatedAxisGlobalCanonicalFourthSparseShortQ r := by
  simp only [ShortData.flat, fourthSrcShort, fourthSrcPairs, fourthSrcOct, shortFunQ_append,
    shortFunQ_nil, add_zero, shortFunQ_map_finRange, shortFunQ_octsFlat_map]
  rw [generatedAxisGlobalCanonicalFourthSparseShortQ, Fintype.sum_sum_type, Fintype.sum_prod_type,
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
    simp only [generatedAxisGlobalCanonicalFourthShortPacketLabel,
      generatedAxisGlobalCanonicalFourthShortPacketCoefficient]
    by_cases hr : (Sum.inl (0, p) : GriessShortIndex) = r
    · simp only [hr, ↓reduceIte]
      rw [(fourthPairNum_spec p).1, fourthPairQ_zero p]; ring
    · simp only [hr, ↓reduceIte, mul_zero]
  · apply Finset.sum_congr rfl
    intro p _
    have hd : shortDecode (276 + p.val) = Sum.inl (1, p) := by
      have h := shortDecode_encode (Sum.inl (1, p))
      simpa [shortEncode] using h
    rw [hd]
    simp only [generatedAxisGlobalCanonicalFourthShortPacketLabel,
      generatedAxisGlobalCanonicalFourthShortPacketCoefficient]
    by_cases hr : (Sum.inl (1, p) : GriessShortIndex) = r
    · simp only [hr, ↓reduceIte]
      rw [(fourthPairNum_spec p).2, fourthPairQ_one p]; ring
    · simp only [hr, ↓reduceIte, mul_zero]
  · apply Finset.sum_congr rfl
    intro j _
    rw [shortFunQ, octFlat, List.map_map, List.map_map, ← Fin.sum_univ_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    have hd : shortDecode (552 + 64 * fourthOctIdx j.val + e.val) =
        Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e)) := by
      have h := shortDecode_encode (Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e)))
      simp only [shortEncode, fourthOctIdx_eq] at h
      exact h
    simp only [Function.comp_apply]
    rw [hd]
    simp only [generatedAxisGlobalCanonicalFourthShortPacketLabel,
      generatedAxisGlobalCanonicalFourthShortPacketCoefficient]
    obtain ⟨-, -, hs, hph⟩ := fourthOct_spec j
    by_cases hr : Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e)) = r
    · simp only [hr, ↓reduceIte]
      rw [fourthOctNum, hs, hph, octIntF_eq e (generatedFourthEvenRootSign j)]
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (generatedFourthEvenCoefficientCache j)
        with hc | hc
      · simp only [hc, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte,
          generatedAxisGlobalIntSign]
        push_cast; ring
      · simp only [hc, decide_true, ↓reduceIte, one_ne_zero, generatedAxisGlobalIntSign]
        push_cast; ring
    · simp only [hr, ↓reduceIte, mul_zero]

/-! ## Tensor block -/

/-- The value of odd root record `r` of the Fourth tensor. -/
def fourthRootVal (r : Fin 56) : ℤ :=
  generatedAxisGlobalIntSign (generatedFourthOddCoefficientPhaseData r) *
    (if (golayEncodedMask (generatedFourthOddRootOutputData r).1.val).testBit
      (generatedFourthOddRootOutputData r).2.val then -1 else 1)

/-- Record values are signs. -/
theorem fourthRootVal_natAbs (r : Fin 56) : (fourthRootVal r).natAbs = 1 := by
  unfold fourthRootVal generatedAxisGlobalIntSign
  split_ifs <;> decide

/-- The contribution of record `r` to column `i`. -/
def fourthTerm (i : ℕ) (r : Fin 56) : SVec :=
  if (generatedFourthOddRootOutputData r).2.val = i then
    unitVec 128 (generatedFourthOddRootOutputData r).1.val (fourthRootVal r) else szero

/-- Column `i` of the Fourth tensor. -/
def fourthCol (i : ℕ) : SVec := ssum ((List.finRange 56).map (fourthTerm i))

/-- The packed Fourth tensor. -/
@[irreducible] def fourthSrcX : List SVec := (List.range 24).map fourthCol

/-- Bounds and values of one record contribution. -/
theorem fourthTerm_spec (i : ℕ) (r : Fin 56) :
    SBnd 128 (2 ^ 12) 1 (fourthTerm i r) ∧ ∀ k, sval 128 (fourthTerm i r) k =
      if (generatedFourthOddRootOutputData r).2.val = i then
        (if k = (generatedFourthOddRootOutputData r).1.val then fourthRootVal r
          else if k = (generatedFourthOddRootOutputData r).1.val + 2048 then -fourthRootVal r
          else 0) else 0 := by
  unfold fourthTerm
  split_ifs with h
  · have hu := unitVec_spec 128 (generatedFourthOddRootOutputData r).1.val (fourthRootVal r)
      (generatedFourthOddRootOutputData r).1.isLt (by rw [fourthRootVal_natAbs]; norm_num)
    rw [fourthRootVal_natAbs] at hu
    exact hu
  · exact ⟨SBnd_zero _ _ _, fun k => sval_zero _ _⟩

/-- Bounds and values of a column. -/
theorem fourthCol_spec (i : ℕ) :
    SBnd 128 (2 ^ 12) 56 (fourthCol i) ∧ ∀ k < 4096, sval 128 (fourthCol i) k =
      ∑ r : Fin 56, sval 128 (fourthTerm i r) k := by
  have h := ssum_spec (w := 128) (n := 2 ^ 12) (B := 1) ((List.finRange 56).map (fourthTerm i))
    (fun x hx => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact (fourthTerm_spec i r).1) (by simp)
  simp only [List.length_map, List.length_finRange, mul_one] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rw [fourthCol, h.2 k (by norm_num; exact hk), List.map_map, Fin.sum_univ_def]
  rfl

/-- Bounds of the packed Fourth tensor. -/
theorem fourthSrcX_bnd : TBnd 128 56 fourthSrcX := by
  intro i hi
  rw [fourthSrcX, tcol_range_map _ 24 i hi]
  exact (fourthCol_spec i).1

/-- The packed Fourth tensor is the canonical integer tensor. -/
theorem fourthSrcX_val (k : Fin 4096) (i : Fin 24) :
    sval 128 (tcol fourthSrcX i.val) k.val =
      generatedAxisGlobalCanonicalFourthTensorInteger k i := by
  rw [fourthSrcX, tcol_range_map _ 24 i.val i.isLt, (fourthCol_spec i.val).2 k.val k.isLt,
    generatedAxisGlobalCanonicalFourthTensorInteger]
  apply Finset.sum_congr rfl
  intro r _
  rw [(fourthTerm_spec i.val r).2 k.val, fourthRootVal]
  exact fifth_record_term k i _ _ _

/-! ## The identification vector -/

/-- The Fourth axis as an identification vector. -/
def fourthSrcVec : IdentVec := ⟨fourthSrcMat, fourthSrcShort, 1 / 8, tensorRat 128 fourthSrcX 1⟩

/-- The tensor block of the Fourth representation. -/
theorem fourthSrcVec_ten : fourthSrcVec.ten = tensorRat 128 fourthSrcX 1 := rfl

set_option maxRecDepth 20000 in
/-- The rational packet of the representation is the canonical Fourth packet. -/
theorem fourthSrcVec_packet :
    fourthSrcVec.packet = generatedAxisGlobalCanonicalFourthFastRationalPacket := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact fourthSrcMat_toMat
  · show (fun r => fourthSrcVec.sden * shortFunQ fourthSrcVec.sh.flat r) =
      generatedAxisGlobalCanonicalFourthFastShortQ
    funext r
    rw [← generatedAxisGlobalCanonicalFourthSparseShortQ_eq]
    exact fourthSrcShort_spec r
  · show (fun t i => fourthSrcVec.ten (generatedAxisGlobalSpinLabel t) i) =
      fun t i =>
        (generatedAxisGlobalCanonicalFourthTensorInteger (generatedAxisGlobalSpinLabel t) i : ℚ)
    funext t i
    have h1 : fourthSrcVec.ten (generatedAxisGlobalSpinLabel t) i =
        tensorRat 128 fourthSrcX 1 (generatedAxisGlobalSpinLabel t) i := rfl
    have h2 : tensorRat 128 fourthSrcX 1 (generatedAxisGlobalSpinLabel t) i =
        (sval 128 (tcol fourthSrcX i.val) (generatedAxisGlobalSpinLabel t).val : ℚ) / 1 := rfl
    rw [h1, h2, div_one, fourthSrcX_val]

/-- The representation gives the genuine coordinates of the Fourth axis. -/
theorem fourthSrc_actual : griessConwayEncode generatedFourthAxis = fourthSrcVec.real := by
  rw [generatedAxisGlobalCanonicalFourthFastRationalPacket_actual, IdentVec.real,
    fourthSrcVec_packet]

/-- The representation of family representative `3`. -/
theorem fourthSrc_rep : griessConwayEncode (generatedAxisGlobalTwelveRepresentative 3) =
    fourthSrcVec.real := fourthSrc_actual

set_option maxRecDepth 100000 in
/-- The short block satisfies the range conditions. -/
theorem fourthSrcVec_ok : fourthSrcVec.sh.ok = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
