/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorTriality
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalInverse

/-! # Packed triality tensor parts and the packed tensor pairing

`trialityTensorT w inv X` computes, on packed numerators over twice the denominator, the part of
the triality tensor formula (`generatedAxisGlobalTrialityScaledTensorQ` for `inv = false`,
`generatedAxisGlobalInverseTensorQ` for `inv = true`) that comes from the source tensor.  The
remaining odd-short part is the explicit sparse term `trialityCPart`.  `tdot` computes the tensor
pairing `conwayTensorForm` of two packed tensors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-- The sign mask of the triality tensor part of column `j`. -/
def tmask (w : ℕ) (inv : Bool) (j : ℕ) : ℕ :=
  (if inv then bmask w 12 11 else 0) ^^^ spread w qBits (2 ^ 12) ^^^
    linMask w 12 (gcol j &&& 2047) false 12

/-- The sign predicate of the triality tensor part. -/
def tpred (inv : Bool) (j k : ℕ) : Bool :=
  (inv && k.testBit 11) ^^ qBits.testBit k ^^ bpar (k &&& (gcol j &&& 2047)) 12

/-- The triality sign mask is the field mask of its predicate. -/
theorem tmask_isFieldMask (w : ℕ) (inv : Bool) (j : ℕ) :
    IsFieldMask w (2 ^ 12) (tmask w inv j) (fun k => tpred inv j k = true) := by
  have h1 : IsFieldMask w (2 ^ 12) (if inv then bmask w 12 11 else 0)
      (fun k => (inv && k.testBit 11) = true) := by
    cases inv
    · exact (zero_isFieldMask w _).congr (fun k _ => by simp)
    · exact (bmask_isFieldMask w 12 11 (by norm_num)).congr (fun k _ => by simp)
  have h2 := spread_isFieldMask w (2 ^ 12) qBits
  have h3 := linMask_isFieldMask w 12 (gcol j &&& 2047) false 12 le_rfl
  refine ((isFieldMask_xor (isFieldMask_xor h1 h2) h3)).congr (fun k _ => ?_)
  simp only [tpred, Bool.false_xor]
  cases (inv && k.testBit 11) <;> cases qBits.testBit k <;>
    cases bpar (k &&& (gcol j &&& 2047)) 12 <;> simp

/-- The packed source-tensor part of the triality tensor, on numerators over `2 * D`. -/
def trialityTensorT (w : ℕ) (inv : Bool) (X : List SVec) : List SVec :=
  (List.range 24).map (fun j =>
    sflip (allMask w (2 ^ 12)) (tmask w inv j) (colHalf w (!inv) (tcol X j)))

/-- The packed triality tensor part: bounds and values. -/
theorem trialityTensorT_spec {w B : ℕ} (inv : Bool) {X : List SVec} (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w) :
    TBnd w (4 * B) (trialityTensorT w inv X) ∧ ∀ j < 24, ∀ k < 4096,
      sval w (tcol (trialityTensorT w inv X) j) k =
        (if tpred inv j k then -1 else 1) *
          (sval w (tcol X j) (k % 2048) +
            (if inv then 1 else -1) * sval w (tcol X j) (k % 2048 + 2048)) := by
  have hcol : ∀ j < 24, tcol (trialityTensorT w inv X) j =
      sflip (allMask w (2 ^ 12)) (tmask w inv j) (colHalf w (!inv) (tcol X j)) :=
    fun j hj => tcol_range_map _ 24 j hj
  have hB4 : 4 * B < 2 ^ w := hB
  refine ⟨fun j hj => ?_, fun j hj k hk => ?_⟩
  · rw [hcol j hj]
    exact (sflip_spec (colHalf_spec (!inv) (hX j hj) hB4).1 _ _ (tmask_isFieldMask w inv j)
      hB4).1
  · rw [hcol j hj]
    have hk' : k < 2 ^ 12 := by norm_num; exact hk
    rw [(sflip_spec (colHalf_spec (!inv) (hX j hj) hB4).1 _ _ (tmask_isFieldMask w inv j)
      hB4).2 k hk', (colHalf_spec (!inv) (hX j hj) hB4).2 k hk]
    cases inv <;> split_ifs <;> simp_all

/-! ## Binding to the triality tensor formulas -/

/-- The odd-short part of the forward triality tensor formula. -/
def trialityCPartFwd (C : GriessShortIndex → ℚ) (t : SpinIndex) (j : Fin 24) : ℚ :=
  let d := generatedAxisGlobalSpinLabelLow (generatedAxisGlobalSpinLabel t)
  let z : ℚ := if (golayEncodedMask d.val).testBit j.val then -1 else 1
  (generatedAxisGlobalIntSign (t 11) : ℚ) * z * C (Sum.inr (Sum.inr (d, j)))

/-- The odd-short part of the inverse triality tensor formula. -/
def trialityCPartInv (C : GriessShortIndex → ℚ) (t : SpinIndex) (j : Fin 24) : ℚ :=
  let d := generatedAxisGlobalSpinLabelLow (generatedAxisGlobalSpinLabel t)
  let e : ℚ := generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  e * C (Sum.inr (Sum.inr (d, j)))

/-- The masked parity of a label is the parity of its low label. -/
theorem bpar_low (k g : ℕ) : bpar (k &&& (g &&& 2047)) 12 = bpar (k % 2048 &&& g) 12 := by
  have h : k % 2048 = k &&& 2047 := by
    rw [show (2047 : ℕ) = 2 ^ 11 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  rw [h, Nat.and_assoc, Nat.and_comm 2047 g, ← Nat.and_assoc]

/-- The sign of the triality tensor part is the product of the formula signs. -/
theorem tpred_sign (inv : Bool) (j : Fin 24) (k : Fin 4096) :
    (if tpred inv j.val k.val then (-1 : ℚ) else 1) =
      (if inv then (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) else 1) *
        (generatedAxisGlobalIntSign
          (golayMaskWeight (golayEncodedMask (k.val % 2048)) / 4 : ℕ) : ℚ) *
        (if (golayEncodedMask (k.val % 2048)).testBit j.val then -1 else 1) := by
  rw [intSign_weight, golayEncodedMask_testBit, tpred, qBits_spec k, bpar_low]
  simp only [golayLabelCoefficients]
  cases inv <;> cases h1 : k.val.testBit 11 <;> cases h2 : qPred (k.val % 2048) <;>
    cases h3 : bpar (k.val % 2048 &&& gcol j.val) 12 <;> simp [h1, generatedAxisGlobalIntSign]

/-- The forward triality tensor formula splits into the odd-short part and the packed part. -/
theorem trialityTensorT_fwd {w B : ℕ} {X : List SVec} (hX : TBnd w B X) (hB : 4 * B < 2 ^ w)
    (D : ℚ) (C : GriessShortIndex → ℚ) (t : SpinIndex) (j : Fin 24) :
    generatedAxisGlobalTrialityScaledTensorQ C
        (fun t i => tensorRat w X D (generatedAxisGlobalSpinLabel t) i) t j =
      trialityCPartFwd C t j +
        tensorRat w (trialityTensorT w false X) (2 * D) (generatedAxisGlobalSpinLabel t) j := by
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  simp only [generatedAxisGlobalTrialityScaledTensorQ, trialityCPartFwd, tensorRat,
    generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalSpinLabelLow]
  rw [(trialityTensorT_spec false hX hB).2 j.val j.isLt k.val k.isLt]
  have hsg := tpred_sign false j k
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hsg
  push_cast
  rw [hsg]
  ring

/-- The inverse triality tensor formula splits into the odd-short part and the packed part. -/
theorem trialityTensorT_inv {w B : ℕ} {X : List SVec} (hX : TBnd w B X) (hB : 4 * B < 2 ^ w)
    (D : ℚ) (a : GeneratedAxisGlobalRationalPacket)
    (ha : a.2.2 = fun t i => tensorRat w X D (generatedAxisGlobalSpinLabel t) i)
    (t : SpinIndex) (j : Fin 24) :
    generatedAxisGlobalInverseTensorQ a t j =
      trialityCPartInv a.2.1 t j +
        tensorRat w (trialityTensorT w true X) (2 * D) (generatedAxisGlobalSpinLabel t) j := by
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  simp only [generatedAxisGlobalInverseTensorQ, trialityCPartInv, tensorRat, ha,
    generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalSpinLabelLow]
  rw [(trialityTensorT_spec true hX hB).2 j.val j.isLt k.val k.isLt]
  have hsg := tpred_sign true j k
  simp only [↓reduceIte] at hsg
  push_cast
  rw [hsg]
  simp only [ite_true]
  ring

/-! ## The packed tensor pairing -/

/-- The packed tensor pairing: the sum of the 24 column dot products. -/
def tdot (w : ℕ) (X Y : List SVec) : ℤ :=
  ((List.range 24).map (fun i => sdot w (tcol X i) (tcol Y i) 4096)).sum

/-- Sums over spin indices are sums over spin labels. -/
theorem sum_spinIndex {M : Type*} [AddCommMonoid M] (f : Fin 4096 → M) :
    ∑ t : SpinIndex, f (generatedAxisGlobalSpinLabel t) = ∑ k : Fin 4096, f k := by
  symm
  apply Fintype.sum_bijective golayLabelCoefficients golayLabelCoefficients_bijective
  intro k
  rw [generatedAxisGlobalSpinLabel_coeff]

/-- The rational tensor pairing of two packed tensors. -/
theorem tdot_rat (w : ℕ) (X Y : List SVec) (D E : ℚ) :
    ∑ k : Fin 4096, ∑ i : Fin 24, tensorRat w X D k i * tensorRat w Y E k i / 2 =
      (tdot w X Y : ℚ) / (2 * (D * E)) := by
  simp only [tensorRat]
  rw [tdot, list_sum_map_range, Finset.sum_comm, Fin.sum_univ_eq_sum_range (fun i =>
    ∑ k : Fin 4096, (sval w (tcol X i) k.val : ℚ) / D * ((sval w (tcol Y i) k.val : ℚ) / E) / 2) 24]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_eq_sum_range (fun k =>
    (sval w (tcol X i) k : ℚ) / D * ((sval w (tcol Y i) k : ℚ) / E) / 2) 4096, sdot_eq]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The tensor pairing of two packed tensors. -/
theorem tdot_form (w : ℕ) (X Y : List SVec) (D E : ℚ) :
    conwayTensorForm (generatedAxisGlobalRationalTensorReal (tensorRat w X D))
        (generatedAxisGlobalRationalTensorReal (tensorRat w Y E)) =
      (((tdot w X Y : ℚ) / (2 * (D * E)) : ℚ) : ℝ) := by
  have hsum : conwayTensorForm (generatedAxisGlobalRationalTensorReal (tensorRat w X D))
        (generatedAxisGlobalRationalTensorReal (tensorRat w Y E)) =
      ∑ t : SpinIndex, ∑ i : Fin 24,
        (((tensorRat w X D (generatedAxisGlobalSpinLabel t) i *
          tensorRat w Y E (generatedAxisGlobalSpinLabel t) i / 2 : ℚ)) : ℝ) := by
    simp only [conwayTensorForm, LinearMap.mk₂_apply, generatedAxisGlobalRationalTensorReal]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hsum, sum_spinIndex (fun k => ∑ i : Fin 24,
    (((tensorRat w X D k i * tensorRat w Y E k i / 2 : ℚ)) : ℝ)), ← tdot_rat]
  push_cast
  rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
