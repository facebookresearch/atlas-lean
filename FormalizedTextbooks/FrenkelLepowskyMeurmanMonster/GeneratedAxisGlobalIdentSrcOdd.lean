/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddTensorFixed

/-! # The Odd axis as an identification vector

`oddSrcVec : IdentVec` represents the Odd axis `generatedOddAxis` (family representative `2`),
the forward triality image of the odd short axis at `(0, 0)`: its matrix block is
`(1/4) I + 2 e₀ e₀ᵀ`, its short block consists of the `552` pair coordinates `± λ_a λ_b / 4`
(`λ = (-3, 1, …, 1)`), and its tensor block has the two entries `∓ 8 / √2` at the spin labels `0`
and `2048` of column `0`. All coordinates are read off the exact triality formulas for odd short
axes. Densities: `552` short terms, `2` tensor entries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false

/-! ## Matrix block -/

/-- The matrix block of the Odd axis: `(1/4) I + 2 e₀ e₀ᵀ`. -/
def oddSrcMat : MatRep := ⟨1 / 4, [(2, unitList 0)]⟩

set_option maxRecDepth 100000 in
/-- The matrix block is the diagonal Odd matrix. -/
theorem oddSrcMat_toMat : oddSrcMat.toMat =
    Matrix.diagonal (fun j : Fin 24 => if j.val = 0 then (9 / 4 : ℚ) else 1 / 4) := by
  ext i j
  rw [MatRep.toMat_apply, Matrix.diagonal_apply]
  revert i j
  decide +kernel

/-! ## Short block -/

/-- The integral odd short vector at `(0, 0)`: `-3` at coordinate `0`, `1` elsewhere. -/
def oddLam (a : Fin 24) : ℤ := if a.val = 0 then -3 else 1

/-- The pair numerators of the Odd axis (scale `1/4`). -/
def oddPairNum (s : Fin 2) (p : Fin 276) : ℤ :=
  (if s = 0 then 1 else -1) * oddLam (generatedAxisGlobalPairCoordinates p).1 *
    oddLam (generatedAxisGlobalPairCoordinates p).2

/-- The pair terms of the Odd axis. -/
def oddSrcPairs : List (ℕ × ℤ) :=
  (List.finRange 276).map (fun p => (shortEncode (Sum.inl (0, p)), oddPairNum 0 p)) ++
    (List.finRange 276).map (fun p => (shortEncode (Sum.inl (1, p)), oddPairNum 1 p))

/-- The sparse short block of the Odd axis (scale `1/4`): pair terms only. -/
def oddSrcShort : ShortData := ⟨oddSrcPairs, [], []⟩

/-- Short coordinates of a list of encoded terms. -/
theorem oddShort_encode_map {α : Type*} (L : List α) (f : α → GriessShortIndex) (v : α → ℤ)
    (r : GriessShortIndex) :
    shortFunQ (L.map (fun x => (shortEncode (f x), v x))) r =
      (L.map (fun x => if f x = r then (v x : ℚ) else 0)).sum := by
  simp only [shortFunQ, List.map_map, Function.comp_def, shortDecode_encode]

/-- The short coordinates of the Odd block as finite sums. -/
theorem oddSrcShort_sum (r : GriessShortIndex) :
    shortFunQ oddSrcShort.flat r =
      (∑ p : Fin 276, if (Sum.inl (0, p) : GriessShortIndex) = r then
        (oddPairNum 0 p : ℚ) else 0) +
      ∑ p : Fin 276, if (Sum.inl (1, p) : GriessShortIndex) = r then
        (oddPairNum 1 p : ℚ) else 0 := by
  simp only [ShortData.flat, oddSrcShort, octsFlat, List.append_nil]
  rw [oddSrcPairs, shortFunQ_append, oddShort_encode_map, oddShort_encode_map,
    ← Fin.sum_univ_def, ← Fin.sum_univ_def]

/-- The integral odd short vector at `(0, 0)` is `oddLam`. -/
theorem oddLam_eq (a : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inr (0, 0))) a = oddLam a := by
  have hm : golayEncodedMask (0 : Fin 2048).val = 0 := by decide +kernel
  simp only [griessShortIntegral, hm, Nat.zero_testBit, Bool.false_eq_true, ite_false, one_mul,
    oddLam]
  by_cases ha : a = 0
  · subst ha
    rfl
  · have hv : a.val ≠ 0 := fun h => ha (Fin.ext h)
    simp only [ha, hv, ite_false]

/-! ## Tensor block -/

/-- The packed Odd tensor: column `0` carries `-8` at label `0` and `8` at label `2048`. -/
@[irreducible] def oddSrcX : List SVec :=
  (List.range 24).map (fun j => if j = 0 then unitVec 128 0 (-8) else szero)

/-- The columns of the packed Odd tensor. -/
theorem oddSrcX_col (j : ℕ) (hj : j < 24) :
    tcol oddSrcX j = if j = 0 then unitVec 128 0 (-8) else szero := by
  rw [oddSrcX, tcol_range_map _ 24 j hj]

/-- Bounds of the packed Odd tensor. -/
theorem oddSrcX_bnd : TBnd 128 8 oddSrcX := by
  intro j hj
  rw [oddSrcX_col j hj]
  split_ifs
  · exact (unitVec_spec 128 0 (-8) (by norm_num) (by norm_num)).1
  · exact SBnd_zero _ _ _

/-- Values of the packed Odd tensor. -/
theorem oddSrcX_val (k : Fin 4096) (j : Fin 24) :
    sval 128 (tcol oddSrcX j.val) k.val =
      if j.val = 0 then (if k.val = 0 then -8 else if k.val = 2048 then 8 else 0) else 0 := by
  rw [oddSrcX_col j.val j.isLt]
  split_ifs with h0 h1 h2 <;>
    simp_all [(unitVec_spec 128 0 (-8) (by norm_num) (by norm_num)).2, sval_zero]

/-! ## The identification vector -/

/-- The Odd axis as an identification vector. -/
def oddSrcVec : IdentVec := ⟨oddSrcMat, oddSrcShort, 1 / 4, tensorRat 128 oddSrcX 1⟩

/-- The tensor block of the Odd representation. -/
theorem oddSrcVec_ten : oddSrcVec.ten = tensorRat 128 oddSrcX 1 := rfl

/-- The short block of the Odd representation. -/
theorem oddSrcVec_sh : oddSrcVec.sh = oddSrcShort := rfl

/-- The representation gives the genuine coordinates of the Odd axis. -/
theorem oddSrc_actual : griessConwayEncode generatedOddAxis = oddSrcVec.real := by
  have hdef : generatedOddAxis = sExtra (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0) := rfl
  have h8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have h8' : Real.sqrt 8 ≠ 0 := by positivity
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [hdef, generatedAxis_triality_odd_matrix, IdentVec.real_fst]
    change _ = matR oddSrcMat.toMat
    rw [oddSrcMat_toMat]
    ext i j
    simp only [matR, Matrix.map_apply, Matrix.diagonal_apply, Rat.coe_castHom]
    by_cases hij : i = j
    · subst hij
      by_cases h0 : i = 0
      · subst h0
        norm_num
      · have hv : i.val ≠ 0 := fun h => h0 (Fin.ext h)
        simp [h0, hv]
    · simp [hij]
  · funext r
    change (griessConwayEncode generatedOddAxis).2.1 r =
      (((1 / 4 : ℚ) * shortFunQ oddSrcShort.flat r : ℚ) : ℝ)
    rw [oddSrcShort_sum]
    rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
    · rw [hdef, generatedAxis_triality_odd_pair_coordinate]
      simp only [griessShortVector, oddLam_eq, ← generatedAxisGlobalPairCoordinates_actual]
      have hsq : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
      fin_cases s
      · simp [oddPairNum, Finset.sum_ite_eq']
        field_simp
        rw [hsq]
        ring
      · simp [oddPairNum, Finset.sum_ite_eq']
        field_simp
        rw [hsq]
        ring
    · rw [hdef, generatedAxis_triality_odd_octad_coordinate]
      simp
    · rw [hdef, generatedAxis_triality_odd_odd_coordinate]
      simp
  · funext t j
    change (griessConwayEncode generatedOddAxis).2.2 t j =
      ((tensorRat 128 oddSrcX 1 (generatedAxisGlobalSpinLabel t) j : ℚ) : ℝ) / Real.sqrt 2
    rw [show tensorRat 128 oddSrcX 1 (generatedAxisGlobalSpinLabel t) j =
      (sval 128 (tcol oddSrcX j.val) (generatedAxisGlobalSpinLabel t).val : ℚ) / 1 from rfl,
      oddSrcX_val, hdef, generatedAxis_triality_odd_tensor]
    obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
    rw [generatedAxisGlobalSpinLabel_coeff]
    have hk := k.isLt
    have hcode : spinDictionaryCode (golayLabelCoefficients k) =
        ⟨k.val % 2048, Nat.mod_lt _ (by decide)⟩ := by
      apply Fin.ext
      simp [spinDictionaryCode, spinDictionaryLabel_coeff]
    simp only [Pi.smul_apply, smul_eq_mul, trialityYTensor, hcode, coeff11_eq, qSign_zero]
    have hm : golayEncodedMask (0 : Fin 2048).val = 0 := by decide +kernel
    simp only [hm, Nat.zero_testBit, Bool.false_eq_true, ite_false, mul_one]
    by_cases hj : j = 0
    · subst hj
      simp only [Fin.val_zero, ite_true]
      by_cases h0 : k.val = 0
      · have hb : k.val.testBit 11 = false := by rw [h0]; rfl
        have hc : (⟨k.val % 2048, Nat.mod_lt _ (by decide)⟩ : Fin 2048) = 0 := by
          apply Fin.ext; simp [h0]
        simp only [h0, ite_true, Nat.zero_testBit, Bool.false_eq_true, ite_false, hc, qSign_zero]
        push_cast
        ring
      · by_cases h1 : k.val = 2048
        · have hb : k.val.testBit 11 = true := by rw [h1]; rfl
          have hc : (⟨k.val % 2048, Nat.mod_lt _ (by decide)⟩ : Fin 2048) = 0 := by
            apply Fin.ext; simp [h1]
          have hb2 : Nat.testBit 2048 11 = true := by decide
          simp only [h0, h1, ite_true, ite_false, hb2, hc, qSign_one]
          push_cast
          ring
        · have hc : (⟨k.val % 2048, Nat.mod_lt _ (by decide)⟩ : Fin 2048) ≠ 0 := by
            intro h
            have := congrArg Fin.val h
            simp only [Fin.val_zero] at this
            omega
          simp [h0, h1, hc]
    · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [hj, hv]

/-- The representation of family representative `2`. -/
theorem oddSrc_rep : griessConwayEncode (generatedAxisGlobalTwelveRepresentative 2) =
    oddSrcVec.real := oddSrc_actual

set_option maxRecDepth 100000 in
/-- The short block satisfies the range conditions. -/
theorem oddSrcVec_ok : oddSrcVec.sh.ok = true := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
