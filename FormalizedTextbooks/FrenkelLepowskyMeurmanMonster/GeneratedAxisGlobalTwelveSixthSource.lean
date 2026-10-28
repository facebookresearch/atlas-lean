/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalTensorPacked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMatrix
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadCatalogue

/-! # The Sixth axis as an identification vector

`sixthSrcVec : IdentVec` represents the Sixth axis `generatedSixthAxis` (family representative
`5`) in the format of the packed identification method: its matrix block (a multiple of the
identity plus six rank-one terms), its sparse short block (all `552` pair coordinates, the `273`
middle octad records and the odd coordinates of the codewords with nonzero phase sum, scale
`1/32`) and its tensor block as packed columns with denominator `32`. Every entry is computed
from the executable integer numerators of the Sixth classification, and `sixthSrc_rep` binds the
representation to the genuine coordinates of family representative `5`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false

/-! ## Matrix block -/

/-- The indicator vector of two coordinates, materialized. -/
def sixthPairList (a b : ℕ) : List ℚ :=
  (List.range 24).map (fun j => if j = a ∨ j = b then 1 else 0)

/-- The matrix block of the Sixth axis: `(9/32) I` plus six rank-one terms on `16, 17, 19`. -/
def sixthSrcMat : MatRep :=
  ⟨9 / 32, [(1 / 2, unitList 16), (1 / 2, unitList 17), (3 / 2, unitList 19),
    (1 / 8, sixthPairList 16 17), (-3 / 8, sixthPairList 16 19), (-3 / 8, sixthPairList 17 19)]⟩

/-- The rational middle pair value of the Sixth matrix. -/
def sixthPairQ (a b : Fin 24) : ℚ :=
  if a = 16 ∧ b = 17 then 1 / 4 else if (a = 16 ∧ b = 19) ∨ (a = 17 ∧ b = 19) then -3 / 4 else 0

/-- The rational Sixth matrix, in the shape of `generatedSixthAxisMatrix`. -/
def sixthMatQ (i j : Fin 24) : ℚ :=
  if i = j then (if i = 19 then 33 / 32 else if i = 16 ∨ i = 17 then 17 / 32 else 9 / 32)
  else sixthPairQ (if i < j then i else j) (if i < j then j else i) / 2

set_option maxRecDepth 100000 in
/-- The matrix block is the rational Sixth matrix. -/
theorem sixthSrcMat_toMat : sixthSrcMat.toMat = Matrix.of sixthMatQ := by
  ext i j
  rw [MatRep.toMat_apply, Matrix.of_apply]
  revert i j
  decide +kernel

/-- The genuine Sixth matrix is the real image of the rational one. -/
theorem sixthMatQ_real : generatedSixthAxisMatrix = matR (Matrix.of sixthMatQ) := by
  ext i j
  simp only [generatedSixthAxisMatrix, matR, Matrix.map_apply, Matrix.of_apply, sixthMatQ,
    sixthPairQ, generatedSixthMiddlePairValue, Rat.coe_castHom, ite_true]
  split_ifs <;> push_cast <;> norm_num

/-! ## Short block -/

/-- Executable pair numerators (computable pair coordinates). -/
def sixthPairNum (s : Fin 2) (p : Fin 276) : ℤ :=
  (if s = 0 then 1 else -1) *
      generatedSixthNormEightVectorData 8 (generatedAxisGlobalPairCoordinates p).1 *
      generatedSixthNormEightVectorData 8 (generatedAxisGlobalPairCoordinates p).2 +
    4 * (generatedSixthMiddlePairNumerator 0 (generatedAxisGlobalPairCoordinates p).1
        (generatedAxisGlobalPairCoordinates p).2 -
      generatedSixthMiddlePairNumerator 1 (generatedAxisGlobalPairCoordinates p).1
        (generatedAxisGlobalPairCoordinates p).2)

/-- The executable pair numerators are the final pair numerators. -/
theorem sixthPairNum_eq (s : Fin 2) (p : Fin 276) :
    sixthPairNum s p = generatedSixthFinalPairNumerator s p := by
  simp only [sixthPairNum, generatedSixthFinalPairNumerator,
    generatedAxisGlobalPairCoordinates_actual]

/-- The pair terms of the Sixth axis. -/
def sixthSrcPairs : List (ℕ × ℤ) :=
  (List.finRange 276).map (fun p => (shortEncode (Sum.inl (0, p)), sixthPairNum 0 p)) ++
    (List.finRange 276).map (fun p => (shortEncode (Sum.inl (1, p)), sixthPairNum 1 p))

/-- Packed octad catalogue indices (`10`-bit fields) of the `273` middle octad records. -/
@[irreducible] def sixthOctTable : ℕ :=
    (0x02c65b1ef795a27f18401c01a0e8d4bd110094a732a85d5ac4fac45a5ed78c06 <<< 0) |||
    (0x06f964a6184ae97c9b0c9a47f98600c09a068f0193143c0801947726a55ddaa5 <<< 256) |||
    (0xed318cd7b1ed2c05f9849a1c4be960a725af223de47866e9cde3328c8789e330 <<< 512) |||
    (0xdb685c5b56b8b63c5a4e33756a5a4f9262460d4903be4823af425dee7ae769ad <<< 768) |||
    (0x4f53e0d8cc834f63262c4263bb16c31c05bb121789ac2b120e9b437912758506 <<< 1024) |||
    (0xa6e7275ab6ba57989ac304af6b5ac32c349b09938ad136d3f4f21a88d3e1a860 <<< 1280) |||
    (0x2a61746eaa225862a7aa2139d05ab706b5d9738fa2b5d4da395745d4f0246492 <<< 1536) |||
    (0x46522248654a1786c5254a272ed2a1c872e60969cc2c4bf729cc31e3d40e2ea9 <<< 1792) |||
    (0x544438685fb6080500284a30024b913689fc6100700683a352f44402372d3391 <<< 2048) |||
    (0x91e8ea2c39689fc6100700683a34eeb38f74c12d85a0b4bcf8b20f1441128321 <<< 2304) |||
    (0x2e50cedf68dfd615a07e9830124a3f245a0a8590cfe <<< 2560)

/-- The octad catalogue index of middle record `k`. -/
def sixthOctIdx (k : Fin 273) : ℕ := (sixthOctTable >>> (10 * k.val)) % 1024

set_option maxRecDepth 100000 in
/-- The octad indices carry the middle octad codes. -/
theorem sixthOctIdx_spec : ∀ k : Fin 273,
    sixthOctIdx k < 759 ∧ identOctCode (sixthOctIdx k) = (generatedSixthMiddleOctadCode k).val := by
  decide +kernel

/-- The recorded octad index is the middle octad. -/
theorem sixthOctIdx_eq (k : Fin 273) : (generatedSixthMiddleOctad k).val = sixthOctIdx k := by
  obtain ⟨h1, h2⟩ := sixthOctIdx_spec k
  have h : generatedSixthMiddleOctad k = ⟨sixthOctIdx k, h1⟩ := by
    apply golayOctadLabel_injective
    rw [generatedSixthMiddleOctad_label, ← identOctCode_actual]
    apply Fin.ext
    simp only [identOctCodeFin]
    rw [h2]
  rw [h]

/-- The octad numerator of middle record `k` at sign label `e`. -/
def sixthOctVal (k : Fin 273) (e : ℕ) : ℤ :=
  octIntF e (generatedSixthMiddleOctadSign k).val * generatedSixthMiddleOctadWeight k

/-- The octad blocks of the Sixth axis, one per middle record. -/
def sixthSrcOct : List (ℕ × List (ℕ × ℤ)) :=
  (List.finRange 273).map (fun k =>
    (sixthOctIdx k, (List.finRange 64).map (fun e => (e.val, sixthOctVal k e.val))))

/-- The codewords whose two spin phases do not cancel. -/
def sixthOddOn (d : Fin 2048) : Bool :=
  generatedSixthPackedSpinPhase ⟨d.val, by omega⟩ +
    generatedSixthPackedSpinPhase ⟨d.val + 2048, by omega⟩ != 0

/-- The odd terms of the Sixth axis. -/
def sixthSrcOdd : List (ℕ × ℤ) :=
  (List.finRange 2048).flatMap (fun d => if sixthOddOn d then
    (List.finRange 24).map (fun j => (shortEncode (Sum.inr (Sum.inr (d, j))),
      generatedSixthFinalOddNumerator d j)) else [])

/-- The sparse short block of the Sixth axis (scale `1/32`). -/
def sixthSrcShort : ShortData := ⟨sixthSrcPairs, sixthSrcOct, sixthSrcOdd⟩

/-! ## Short coordinates -/

/-- Short coordinates of a list of encoded terms. -/
theorem sixthShort_encode_map {α : Type*} (L : List α) (f : α → GriessShortIndex) (v : α → ℤ)
    (r : GriessShortIndex) :
    shortFunQ (L.map (fun x => (shortEncode (f x), v x))) r =
      (L.map (fun x => if f x = r then (v x : ℚ) else 0)).sum := by
  simp only [shortFunQ, List.map_map, Function.comp_def, shortDecode_encode]

/-- Short coordinates of a flat map. -/
theorem sixthShort_flatMap {α : Type*} (L : List α) (F : α → List (ℕ × ℤ))
    (r : GriessShortIndex) :
    shortFunQ (L.flatMap F) r = (L.map (fun x => shortFunQ (F x) r)).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [List.flatMap_cons, shortFunQ_append, ih, List.map_cons, List.sum_cons]

/-- The pair terms as a finite sum. -/
theorem sixthSrcPairs_sum (r : GriessShortIndex) :
    shortFunQ sixthSrcPairs r =
      (∑ p : Fin 276, if (Sum.inl (0, p) : GriessShortIndex) = r then
        (sixthPairNum 0 p : ℚ) else 0) +
      ∑ p : Fin 276, if (Sum.inl (1, p) : GriessShortIndex) = r then
        (sixthPairNum 1 p : ℚ) else 0 := by
  rw [sixthSrcPairs, shortFunQ_append, sixthShort_encode_map, sixthShort_encode_map,
    ← Fin.sum_univ_def, ← Fin.sum_univ_def]

/-- The octad terms as a finite sum. -/
theorem sixthSrcOct_sum (r : GriessShortIndex) :
    shortFunQ (octsFlat sixthSrcOct) r = ∑ k : Fin 273, ∑ e : Fin 64,
      if (Sum.inr (Sum.inl (generatedSixthMiddleOctad k, e)) : GriessShortIndex) = r then
        (sixthOctVal k e.val : ℚ) else 0 := by
  rw [sixthSrcOct, shortFunQ_octsFlat_map, ← Fin.sum_univ_def]
  apply Finset.sum_congr rfl
  intro k _
  have hl : octFlat (sixthOctIdx k)
      ((List.finRange 64).map (fun e => (e.val, sixthOctVal k e.val))) =
      (List.finRange 64).map (fun e =>
        (shortEncode (Sum.inr (Sum.inl (generatedSixthMiddleOctad k, e))),
          sixthOctVal k e.val)) := by
    rw [octFlat, List.map_map]
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_apply, shortEncode, sixthOctIdx_eq]
  rw [hl, sixthShort_encode_map, ← Fin.sum_univ_def]

/-- The odd terms as a finite sum. -/
theorem sixthSrcOdd_sum (r : GriessShortIndex) :
    shortFunQ sixthSrcOdd r = ∑ d : Fin 2048, if sixthOddOn d then ∑ j : Fin 24,
      (if (Sum.inr (Sum.inr (d, j)) : GriessShortIndex) = r then
        (generatedSixthFinalOddNumerator d j : ℚ) else 0) else 0 := by
  rw [sixthSrcOdd, sixthShort_flatMap, ← Fin.sum_univ_def]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs
  · rw [sixthShort_encode_map, ← Fin.sum_univ_def]
  · rfl

/-- Codewords with cancelling phases have zero odd numerators. -/
theorem sixthOdd_zero (d : Fin 2048) (j : Fin 24) (h : sixthOddOn d = false) :
    generatedSixthFinalOddNumerator d j = 0 := by
  simp only [sixthOddOn, bne_eq_false_iff_eq] at h
  simp only [generatedSixthFinalOddNumerator, h, mul_zero]

/-- The short block of the Sixth axis has the final integer numerators. -/
theorem sixthSrcShort_spec (r : GriessShortIndex) :
    shortFunQ sixthSrcShort.flat r = (generatedSixthFinalShortNumerator r : ℚ) := by
  simp only [ShortData.flat, sixthSrcShort]
  rw [shortFunQ_append, shortFunQ_append, sixthSrcPairs_sum, sixthSrcOct_sum, sixthSrcOdd_sum]
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · simp only [Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, ite_false, Finset.sum_const_zero,
      add_zero, ite_self, generatedSixthFinalShortNumerator]
    fin_cases s <;> simp [sixthPairNum_eq]
  · simp only [reduceCtorEq, ite_false, Finset.sum_const_zero, zero_add, add_zero, ite_self,
      Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, generatedSixthFinalShortNumerator,
      generatedSixthFinalOctadNumerator]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    have hiff : generatedSixthMiddleOctad k = o ↔
        generatedSixthMiddleOctadCode k = golayOctadLabel o := by
      constructor
      · intro h
        rw [← h, generatedSixthMiddleOctad_label]
      · intro h
        apply golayOctadLabel_injective
        rw [generatedSixthMiddleOctad_label, h]
    by_cases hk : generatedSixthMiddleOctad k = o
    · simp only [hk, true_and, (hiff.mp hk), ite_true]
      rw [Finset.sum_ite_eq' Finset.univ e]
      simp only [Finset.mem_univ, ite_true, sixthOctVal,
        octIntF_eq e (generatedSixthMiddleOctadSign k)]
      push_cast
      ring
    · simp only [hk, false_and, ite_false, Finset.sum_const_zero, mt hiff.mpr hk]
  · simp only [reduceCtorEq, ite_false, Finset.sum_const_zero, zero_add,
      Sum.inr.injEq, Prod.mk.injEq, generatedSixthFinalShortNumerator]
    rw [Finset.sum_eq_single d]
    · split_ifs with hon
      · simp only [true_and]
        rw [Finset.sum_ite_eq' Finset.univ j]
        simp
      · simp [sixthOdd_zero d j (by simpa using hon)]
    · intro b _ hb
      split_ifs
      · apply Finset.sum_eq_zero
        intro x _
        simp [hb]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ d) h

/-! ## Tensor block -/

/-- A single signed packed entry `v` at field `n`. -/
def sixthSingle (w n : ℕ) (v : ℤ) : SVec :=
  if 0 ≤ v then (v.toNat <<< (w * n), 0) else (0, (-v).toNat <<< (w * n))

/-- Bounds and values of a single signed entry. -/
theorem sixthSingle_spec (w n : ℕ) (v : ℤ) (hn : n < 4096) (hv : v.natAbs < 2 ^ w) :
    SBnd w (2 ^ 12) v.natAbs (sixthSingle w n v) ∧
      ∀ k, sval w (sixthSingle w n v) k = if k = n then v else 0 := by
  have hn1 : n < 2 ^ 12 := by omega
  have hz : (0 : ℕ) < 2 ^ (w * 2 ^ 12) := by positivity
  by_cases h0 : 0 ≤ v
  · have hc : v.toNat < 2 ^ w := by omega
    simp only [sixthSingle, h0, ↓reduceIte]
    refine ⟨⟨single_lt w _ n _ hc hn1, hz, fun k _ => ?_⟩, fun k => ?_⟩
    · rw [fld_single w _ _ _ hc, fld_zero_right_zero]
      constructor <;> (try split_ifs) <;> omega
    · simp only [sval]
      rw [fld_single w _ _ _ hc, fld_zero_right_zero]
      split_ifs <;> omega
  · have hc : (-v).toNat < 2 ^ w := by omega
    simp only [sixthSingle, h0, ↓reduceIte]
    refine ⟨⟨hz, single_lt w _ n _ hc hn1, fun k _ => ?_⟩, fun k => ?_⟩
    · rw [fld_single w _ _ _ hc, fld_zero_right_zero]
      constructor <;> (try split_ifs) <;> omega
    · simp only [sval]
      rw [fld_single w _ _ _ hc, fld_zero_right_zero]
      split_ifs <;> omega

/-- The executable tensor numerator at label `n` and column `j`. -/
def sixthTNum (n : ℕ) (j : Fin 24) : ℤ :=
  8 * nortonUIntegerSign (if n.testBit 11 then 1 else 0) *
      (if (golayEncodedMask (n % 2048)).testBit j.val then -1 else 1) *
      generatedSixthMiddleOddPackedNumerator ⟨n % 2048, Nat.mod_lt _ (by decide)⟩ j -
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask (n % 2048)) / 4 : ℕ) *
      (if (golayEncodedMask (n % 2048)).testBit j.val then -1 else 1) *
      generatedSixthFrameVectorData 8 0 j *
      (generatedSixthPackedSpinPhase ⟨n % 2048, by omega⟩ -
        generatedSixthPackedSpinPhase ⟨n % 2048 + 2048, by omega⟩)

/-- The executable tensor numerator is the final packed tensor numerator. -/
theorem sixthTNum_eq (n : Fin 4096) (j : Fin 24) :
    sixthTNum n.val j = generatedSixthFinalTensorPackedNumerator n j := by
  have hd : spinDictionaryCode (golayLabelCoefficients n) =
      ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext
    simp [spinDictionaryCode, spinDictionaryLabel_coeff]
  simp only [sixthTNum, generatedSixthFinalTensorPackedNumerator, hd, coeff11_eq]

/-- Middle odd numerators are at most three. -/
theorem sixthMiddle_natAbs (d : Fin 2048) (j : Fin 24) :
    (generatedSixthMiddleOddPackedNumerator d j).natAbs ≤ 3 := by
  unfold generatedSixthMiddleOddPackedNumerator
  split_ifs <;> decide

set_option maxRecDepth 100000 in
/-- The frame vector entries are at most eight. -/
theorem sixthFrame_natAbs : ∀ j : Fin 24, (generatedSixthFrameVectorData 8 0 j).natAbs ≤ 8 := by
  decide +kernel

/-- Packed spin phases are signs or zero. -/
theorem sixthPhase_natAbs (n : Fin 4096) : (generatedSixthPackedSpinPhase n).natAbs ≤ 1 := by
  unfold generatedSixthPackedSpinPhase
  split_ifs <;> decide

/-- Integer signs have absolute value one. -/
theorem sixthNorton_natAbs (c : ZMod 2) : (nortonUIntegerSign c).natAbs = 1 := by
  unfold nortonUIntegerSign
  split_ifs <;> rfl

/-- Conditional signs have absolute value one. -/
theorem sixthIteSign_natAbs (b : Bool) : (if b then (-1 : ℤ) else 1).natAbs = 1 := by
  cases b <;> rfl

/-- The tensor numerators are at most `64`. -/
theorem sixthTNum_natAbs (n : ℕ) (j : Fin 24) : (sixthTNum n j).natAbs ≤ 64 := by
  have hM := sixthMiddle_natAbs ⟨n % 2048, Nat.mod_lt _ (by decide)⟩ j
  have hF := sixthFrame_natAbs j
  have hp1 := sixthPhase_natAbs ⟨n % 2048, by omega⟩
  have hp2 := sixthPhase_natAbs ⟨n % 2048 + 2048, by omega⟩
  have hd := le_trans (Int.natAbs_sub_le (generatedSixthPackedSpinPhase ⟨n % 2048, by omega⟩)
    (generatedSixthPackedSpinPhase ⟨n % 2048 + 2048, by omega⟩)) (Nat.add_le_add hp1 hp2)
  unfold sixthTNum
  refine le_trans (Int.natAbs_sub_le _ _) ?_
  simp only [Int.natAbs_mul, sixthNorton_natAbs, sixthIteSign_natAbs, mul_one]
  have h1 : Int.natAbs 8 * (generatedSixthMiddleOddPackedNumerator
      ⟨n % 2048, Nat.mod_lt _ (by decide)⟩ j).natAbs ≤ 8 * 3 := by
    exact Nat.mul_le_mul (le_refl _) hM
  have h2 := Nat.mul_le_mul hF hd
  simp only [one_mul] at h2 ⊢
  omega

/-- Column `i` of the packed Sixth tensor. -/
def sixthColF (i : ℕ) : SVec :=
  ssum ((List.finRange 4096).map (fun n =>
    sixthSingle 128 n.val (sixthTNum n.val ⟨i % 24, Nat.mod_lt _ (by decide)⟩)))

/-- Bounds and values of a column. -/
theorem sixthColF_spec (i : ℕ) :
    SBnd 128 (2 ^ 12) (4096 * 64) (sixthColF i) ∧ ∀ k < 4096,
      sval 128 (sixthColF i) k = sixthTNum k ⟨i % 24, Nat.mod_lt _ (by decide)⟩ := by
  have hv (n : ℕ) : (sixthTNum n ⟨i % 24, Nat.mod_lt _ (by decide)⟩).natAbs < 2 ^ 128 :=
    lt_of_le_of_lt (sixthTNum_natAbs _ _) (by norm_num)
  have h := ssum_spec (w := 128) (n := 2 ^ 12) (B := 64)
    ((List.finRange 4096).map (fun n =>
      sixthSingle 128 n.val (sixthTNum n.val ⟨i % 24, Nat.mod_lt _ (by decide)⟩)))
    (fun x hx => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx
      exact (sixthSingle_spec 128 n.val _ n.isLt (hv n.val)).1.mono (sixthTNum_natAbs _ _))
    (by simp only [List.length_map, List.length_finRange]; norm_num)
  simp only [List.length_map, List.length_finRange] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rw [sixthColF, h.2 k (by norm_num; exact hk), List.map_map, ← Fin.sum_univ_def]
  simp only [Function.comp_apply, (sixthSingle_spec 128 _ _ (Fin.isLt _) (hv _)).2]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro b _ hb
    split_ifs with h
    · exact absurd (Fin.ext h.symm) hb
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The packed Sixth tensor. -/
@[irreducible] def sixthSrcX : List SVec := (List.range 24).map sixthColF

/-- Bounds of the packed Sixth tensor. -/
theorem sixthSrcX_bnd : TBnd 128 (4096 * 64) sixthSrcX := by
  intro i hi
  rw [sixthSrcX, tcol_range_map _ 24 i hi]
  exact (sixthColF_spec i).1

/-- The packed Sixth tensor carries the executable numerators. -/
theorem sixthSrcX_val (k : Fin 4096) (i : Fin 24) :
    sval 128 (tcol sixthSrcX i.val) k.val = sixthTNum k.val i := by
  rw [sixthSrcX, tcol_range_map _ 24 i.val i.isLt, (sixthColF_spec i.val).2 k.val k.isLt]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-! ## The identification vector -/

/-- The Sixth axis as an identification vector. -/
def sixthSrcVec : IdentVec := ⟨sixthSrcMat, sixthSrcShort, 1 / 32, tensorRat 128 sixthSrcX 32⟩

/-- The tensor block of the Sixth representation. -/
theorem sixthSrcVec_ten : sixthSrcVec.ten = tensorRat 128 sixthSrcX 32 := rfl

/-- The short block of the Sixth representation. -/
theorem sixthSrcVec_sh : sixthSrcVec.sh = sixthSrcShort := rfl

/-- The representation gives the genuine coordinates of the Sixth axis. -/
theorem sixthSrc_actual : griessConwayEncode generatedSixthAxis = sixthSrcVec.real := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [generatedSixth_axis_matrix, IdentVec.real_fst, sixthMatQ_real]
    change matR (Matrix.of sixthMatQ) = matR sixthSrcMat.toMat
    rw [sixthSrcMat_toMat]
  · funext r
    change (griessConwayEncode generatedSixthAxis).2.1 r =
      (((1 / 32 : ℚ) * shortFunQ sixthSrcShort.flat r : ℚ) : ℝ)
    rw [generatedSixth_final_short_numerator, sixthSrcShort_spec]
    push_cast
    ring
  · funext t i
    change (griessConwayEncode generatedSixthAxis).2.2 t i =
      ((tensorRat 128 sixthSrcX 32 (generatedAxisGlobalSpinLabel t) i : ℚ) : ℝ) / Real.sqrt 2
    have h := generatedSixth_final_tensor_packed (generatedAxisGlobalSpinLabel t) i
    rw [generatedAxisGlobalSpinLabel_decode] at h
    rw [h]
    change _ = (((sval 128 (tcol sixthSrcX i.val) (generatedAxisGlobalSpinLabel t).val : ℚ) /
      32 : ℚ) : ℝ) / Real.sqrt 2
    rw [sixthSrcX_val, sixthTNum_eq]
    push_cast
    field_simp

/-- The representation of family representative `5`. -/
theorem sixthSrc_rep : griessConwayEncode (generatedAxisGlobalTwelveRepresentative 5) =
    sixthSrcVec.real := sixthSrc_actual

set_option maxRecDepth 100000 in
/-- The short block satisfies the range conditions. -/
theorem sixthSrcVec_ok : sixthSrcVec.sh.ok = true := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
