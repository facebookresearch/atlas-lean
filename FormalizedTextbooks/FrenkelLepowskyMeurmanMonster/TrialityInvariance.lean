/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Orthogonality of the explicit Seysen dictionary triality.
Product preservation is a separate construction theorem.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Pairing written in the four dictionary blocks. -/
def trialityBlockForm (x y : TrialityBlocks) : ℝ :=
  (∑ i, x.1 i * y.1 i) +
  (2 * ∑ a, ∑ i, x.2.1 a i * y.2.1 a i) +
  (∑ o, ∑ i, x.2.2.1 o i * y.2.2.1 o i) +
  (∑ a, ∑ i, x.2.2.2 a i * y.2.2.2 a i)

/-- Reindexing a rectangular block converts its flat sum to a double sum. -/
theorem trialityBlockUncurry_sum (n m : ℕ) (f : Fin (n * m) → ℝ) :
    (∑ k, f k) = ∑ i : Fin n, ∑ j : Fin m, f (finProdFinEquiv (i,j)) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]

/-- The normalized octad Fourier transform preserves the usual pairing. -/
theorem trialityHadamardEquiv_pairing (x y : Fin 64 → ℝ) :
    (∑ i, trialityHadamardEquiv x i * trialityHadamardEquiv y i) = ∑ i, x i * y i := by
  have ht : trialityNormalizedHadamard.transpose = trialityNormalizedHadamard := by
    ext i j
    simp [trialityNormalizedHadamard, trialityHadamard, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.smul_apply, Nat.and_comm]
  change (trialityNormalizedHadamard.mulVec x) ⬝ᵥ
    (trialityNormalizedHadamard.mulVec y) = x ⬝ᵥ y
  rw [← ht, Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec, ht, triality_normalized_hadamard_square, Matrix.one_mulVec,
    dotProduct_comm]

/-- The diagonal octad signs preserve the usual pairing. -/
theorem trialitySignEquiv_pairing (x y : Fin 64 → ℝ) :
    (∑ i, trialitySignEquiv x i * trialitySignEquiv y i) = ∑ i, x i * y i := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [trialitySignEquiv, LinearEquiv.piCongrRight_apply,
    LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  split <;> ring

/-- The source octad operation is orthogonal. -/
theorem trialityOctadAction_pairing (x y : Fin 64 → ℝ) :
    (∑ i, trialityOctadAction x i * trialityOctadAction y i) = ∑ i, x i * y i := by
  change (∑ i, trialitySignEquiv (trialityHadamardEquiv x) i *
    trialitySignEquiv (trialityHadamardEquiv y) i) = _
  rw [trialitySignEquiv_pairing, trialityHadamardEquiv_pairing]

/-- Cycling three equal-norm dictionary blocks preserves their pairing. -/
theorem trialityCycleAction_pairing (n : ℕ) (x y : Fin 3 → Fin n → ℝ) :
    (∑ a, ∑ i, trialityCycleAction n x a i * trialityCycleAction n y a i) =
      ∑ a, ∑ i, x a i * y a i := by
  simpa [trialityCycleAction, LinearEquiv.piCongrLeft'_apply] using
    trialityCycle.symm.sum_comp (fun a => ∑ i, x a i * y a i)

/-- Triality preserves the form in block coordinates. -/
theorem trialityBlockAction_form (x y : TrialityBlocks) :
    trialityBlockForm (trialityBlockAction x) (trialityBlockAction y) =
      trialityBlockForm x y := by
  simp only [trialityBlockForm, trialityBlockAction, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearEquiv.piCongrRight_apply]
  rw [trialityCycleAction_pairing, trialityCycleAction_pairing]
  simp_rw [trialityOctadAction_pairing]


/-- Coordinate formula for a rectangular dictionary block. -/
theorem trialityBlockUncurry_apply (n m : ℕ) (x : Fin (n * m) → ℝ)
    (i : Fin n) (j : Fin m) :
    trialityBlockUncurry n m x i j = x (finProdFinEquiv (i,j)) := by rfl

/-- The flat pairing agrees with the pairing in the source dictionary blocks. -/
theorem griessForm_eq_trialityBlockForm (x y : GriessSpace) :
    griessForm x y = trialityBlockForm (trialityBlocksEquiv x) (trialityBlocksEquiv y) := by
  simp only [griessForm, LinearMap.mk₂_apply]
  unfold griessFormFun
  rw [show (∑ i : Fin 196884, griessBasisWeight i * x i * y i) =
      (∑ i : Fin 24, griessBasisWeight (Fin.castAdd 196860 i) *
        x (Fin.castAdd 196860 i) * y (Fin.castAdd 196860 i)) +
      (∑ i : Fin 196860, griessBasisWeight (Fin.natAdd 24 i) *
        x (Fin.natAdd 24 i) * y (Fin.natAdd 24 i)) from Fin.sum_univ_add (a := 24) (b := 196860) _]
  simp only [griessBasisWeight, Fin.val_castAdd, Fin.val_natAdd]
  simp only [show ∀ i : Fin 24, ¬ (24 ≤ i.val ∧ i.val < 852) by intro i; omega,
    ite_false, one_mul]
  rw [Fin.sum_univ_add (a := 828) (b := 196032)]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  simp only [show ∀ i : Fin 828, 24 ≤ 24 + i.val ∧ 24 + i.val < 852 by intro i; omega,
    show ∀ i : Fin 196032, ¬ (24 ≤ 24 + (828 + i.val) ∧
      24 + (828 + i.val) < 852) by intro i; omega, ite_false, one_mul]
  rw [Fin.sum_univ_add (a := 48576) (b := 147456)]
  simp only [trialityBlockForm, trialityBlocksEquiv, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    trialityBlockUncurry_apply]
  rw [trialityBlockUncurry_sum 3 276, trialityBlockUncurry_sum 759 64,
    trialityBlockUncurry_sum 3 49152]
  simp only [and_self, ite_true]
  simp_rw [Finset.mul_sum]
  simp only [mul_assoc, add_assoc]
  rfl

/-- The explicit extra symmetry preserves the Griess form. -/
theorem sExtra_preserves_griessForm (x y : GriessSpace) :
    griessForm (sExtra x) (sExtra y) = griessForm x y := by
  rw [griessForm_eq_trialityBlockForm, griessForm_eq_trialityBlockForm]
  have ht (v : GriessSpace) : trialityBlocksEquiv (sExtra v) =
      trialityBlockAction (trialityBlocksEquiv v) := by
    simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
  rw [ht, ht, trialityBlockAction_form]


/-- With orthogonality discharged, only multiplication remains for triality. -/
theorem sExtra_isGriessAuto_iff_product : IsGriessAuto sExtra ↔
    ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y) := by
  exact ⟨And.left, fun h => ⟨h, sExtra_preserves_griessForm⟩⟩

/-- Bilinearity reduces product invariance to the actual dictionary basis. -/
theorem griessProduct_invariance_iff_basis (e : GriessSpace ≃ₗ[ℝ] GriessSpace) :
    (∀ x y, e (griessProd x y) = griessProd (e x) (e y)) ↔
    ∀ i j : Fin 196884,
      e (griessProd (Pi.single i 1) (Pi.single j 1)) =
        griessProd (e (Pi.single i 1)) (e (Pi.single j 1)) := by
  constructor
  · intro h i j
    exact h _ _
  · intro h
    have hm : griessProd.compr₂ e.toLinearMap =
        griessProd.compl₁₂ e.toLinearMap e.toLinearMap := by
      apply (Pi.basisFun ℝ (Fin 196884)).ext
      intro i
      apply (Pi.basisFun ℝ (Fin 196884)).ext
      intro j
      simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
        Pi.basisFun_apply, LinearEquiv.coe_toLinearMap]
        using h i j
    intro x y
    have hv := LinearMap.congr_fun (LinearMap.congr_fun hm x) y
    simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
      LinearEquiv.coe_toLinearMap] using hv

/-- The generated subgroup preserves the algebra whenever both kinds of
specified generators do. No recognition result is assumed here. -/
theorem G_le_griessAutSubgroup_of_generator_invariance
    (hlocal : ∀ h : H, IsGriessAuto (rhoLocal h))
    (hextra : IsGriessAuto sExtra) : G ≤ griessAutSubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro e (⟨h, rfl⟩ | he)
  · exact hlocal h
  · have heq : e = sExtra := Set.mem_singleton_iff.mp he
    subst e
    exact hextra

/-- Embed a pure spin-tensor vector in Conway's three-block space. -/
def conwayPureTensor (f : SpinIndex → Fin 24 → ℝ) : ConwayRawSpace := (0, (0, f))

/-- The matrix component of a pure tensor product, in unit dictionary coordinates. -/
theorem conwayPureTensor_product_matrix (f g : SpinIndex → Fin 24 → ℝ)
    (i j : Fin 24) :
    (conwayRawProduct (conwayPureTensor f) (conwayPureTensor g)).1 i j =
      (∑ t, ((∑ k, f t k * g t k) * (if i = j then 1 else 0) +
        4 * f t i * g t j + 4 * g t i * f t j)) / 8 := by
  simp [conwayRawProduct, conwayPureTensor]

/-- A unit spin vector tensored with one coordinate has the source square
`(9/8)` on that diagonal and `(1/8)` on every other diagonal.
This is Conway, page 536, Calculation (1). -/
theorem conwayPureTensor_unit_square_diagonal (q : SpinSpace)
    (hq : (∑ t, q t * q t) = 1) (j i : Fin 24) :
    (conwayRawProduct
      (conwayPureTensor (fun t k => q t * (if k = j then 1 else 0)))
      (conwayPureTensor (fun t k => q t * (if k = j then 1 else 0)))).1 i i =
        if i = j then 9 / 8 else 1 / 8 := by
  rw [conwayPureTensor_product_matrix]
  simp only [ite_true]
  have hsum (t : SpinIndex) :
      (∑ k : Fin 24, (q t * if k = j then 1 else 0) *
        (q t * if k = j then 1 else 0)) = q t * q t := by
    simp
  simp_rw [hsum]
  by_cases hij : i = j
  · simp only [hij, ite_true, mul_one]
    simp_rw [show ∀ a : ℝ, a * a + 4 * a * a + 4 * a * a = 9 * (a * a) by
      intro a; ring]
    rw [← Finset.mul_sum, hq]
    norm_num
  · simp only [hij, ite_false, mul_zero, add_zero, mul_one]
    rw [hq]

/-- A sum over all increasing pairs is exactly a sum over dictionary pair labels. -/
theorem griessCoordinatePair_sum (f : Fin 24 → Fin 24 → ℝ) :
    (∑ p : Fin 276, f (griessCoordinatePair p).1 (griessCoordinatePair p).2) =
      ∑ i : Fin 24, ∑ j : Fin 24, if i < j then f i j else 0 := by
  rw [← Fintype.sum_prod_type (fun p : Fin 24 × Fin 24 =>
    if p.1 < p.2 then f p.1 p.2 else 0)]
  change (∑ p, (fun p : griessCoordinatePairs => f p.val.1 p.val.2)
      (griessCoordinatePairEquiv p)) = _
  rw [griessCoordinatePairEquiv.sum_comp (fun p : griessCoordinatePairs => f p.val.1 p.val.2)]
  rw [Finset.sum_coe_sort griessCoordinatePairs (fun p : Fin 24 × Fin 24 => f p.1 p.2)]
  simp only [griessCoordinatePairs, Finset.sum_filter]

set_option backward.isDefEq.respectTransparency false in
/-- Frobenius pairing of symmetric matrices, separated into diagonal and pair entries. -/
theorem conwaySymmetricMatrix_pairing_split (a b : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, a i j = a j i) (hb : ∀ i j, b i j = b j i) :
    (∑ i, ∑ j, a i j * b i j) = (∑ i, a i i * b i i) +
      2 * ∑ p : Fin 276,
        a (griessCoordinatePair p).1 (griessCoordinatePair p).2 *
        b (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  rw [griessCoordinatePair_sum (fun i j => a i j * b i j)]
  have hs (i j : Fin 24) : a i j * b i j =
      (if i = j then a i j * b i j else 0) +
      (if i < j then a i j * b i j else 0) +
      (if j < i then a i j * b i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge (le_of_lt h)]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge (le_of_lt h)]
  have hsplit : (∑ i, ∑ j, a i j * b i j) =
      (∑ i : Fin 24, ∑ j : Fin 24, if i = j then a i j * b i j else 0) +
      (∑ i : Fin 24, ∑ j : Fin 24, if i < j then a i j * b i j else 0) +
      (∑ i : Fin 24, ∑ j : Fin 24, if j < i then a i j * b i j else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hs i j)
  rw [hsplit]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hswap : (∑ i : Fin 24, ∑ j : Fin 24, if j < i then a i j * b i j else 0) =
      ∑ i : Fin 24, ∑ j : Fin 24, if i < j then a i j * b i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [ha j i, hb j i]
    · rfl
  rw [hswap]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The encoded symmetric-matrix component carries the diagonal and A-block pairing. -/
theorem griessConwayEncode_matrix_form (x y : GriessSpace) :
    (∑ i, ∑ j, (griessConwayEncode x).1 i j * (griessConwayEncode y).1 i j) =
      (∑ i, (trialityBlocksEquiv x).1 i * (trialityBlocksEquiv y).1 i) +
      2 * ∑ p, (trialityBlocksEquiv x).2.1 0 p * (trialityBlocksEquiv y).2.1 0 p := by
  rw [conwaySymmetricMatrix_pairing_split _ _
    (griessConwayEncode_symmetric x) (griessConwayEncode_symmetric y)]
  simp only [griessConwayEncode]
  apply congrArg₂ (fun a b : ℝ => a + 2 * b)
  · rfl
  · apply Finset.sum_congr rfl
    intro p _
    simp only [griessCoordinatePair_ne p, dite_false, griessPairIndex_pair]


theorem real_sum_pair_fourier {ι : Type*} [Fintype ι]
    (a b c d : ι → ℝ) :
    (∑ i, (a i + b i) * (c i + d i)) +
      (∑ i, (b i - a i) * (d i - c i)) =
      2 * (∑ i, a i * c i) + 2 * (∑ i, b i * d i) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The encoded signed-short component carries B, C, octad and X pairings. -/
theorem griessConwayEncode_short_form (x y : GriessSpace) :
    (∑ r, (griessConwayEncode x).2.1 r * (griessConwayEncode y).2.1 r) =
      2 * (∑ p, (trialityBlocksEquiv x).2.1 1 p * (trialityBlocksEquiv y).2.1 1 p) +
      2 * (∑ p, (trialityBlocksEquiv x).2.1 2 p * (trialityBlocksEquiv y).2.1 2 p) +
      (∑ o, ∑ i, (trialityBlocksEquiv x).2.2.1 o i *
        (trialityBlocksEquiv y).2.2.1 o i) +
      (∑ k, (trialityBlocksEquiv x).2.2.2 0 k * (trialityBlocksEquiv y).2.2.2 0 k) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, griessConwayEncode]
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rw [real_sum_pair_fourier]
  have hodd := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).sum_comp
    (fun k => (trialityBlocksEquiv x).2.2.2 0 k * (trialityBlocksEquiv y).2.2.2 0 k)
  rw [Fintype.sum_prod_type] at hodd
  rw [hodd]
  ring

theorem real_normalized_pair_fourier (a b c d s t : ℝ)
    (hs : s * s = 1) (ht : t * t = 1) :
    ((s * a + t * b) / Real.sqrt 2) * ((s * c + t * d) / Real.sqrt 2) +
      ((s * a - t * b) / Real.sqrt 2) * ((s * c - t * d) / Real.sqrt 2) =
      a * c + b * d := by
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [div_mul_div_comm, div_mul_div_comm, ← add_div, hsqrt]
  calc
    ((s * a + t * b) * (s * c + t * d) +
      (s * a - t * b) * (s * c - t * d)) / 2 =
        (2 * (s * s * (a * c) + t * t * (b * d))) / 2 := by ring
    _ = a * c + b * d := by rw [hs, ht]; ring

/-- The partial Fourier dictionary conversion preserves the tensor pairing. -/
theorem griessConwayEncode_tensor_form (x y : GriessSpace) :
    (∑ t, ∑ i, (griessConwayEncode x).2.2 t i * (griessConwayEncode y).2.2 t i) =
      (∑ k, (trialityBlocksEquiv x).2.2.2 1 k * (trialityBlocksEquiv y).2.2.2 1 k) +
      (∑ k, (trialityBlocksEquiv x).2.2.2 2 k * (trialityBlocksEquiv y).2.2.2 2 k) := by
  have hreindex :=
    (Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective).sum_comp
      (fun t => ∑ i, (griessConwayEncode x).2.2 t i * (griessConwayEncode y).2.2 t i)
  rw [← hreindex]
  change (∑ d : Fin 4096, ∑ i,
    (griessConwayEncode x).2.2 (golayLabelCoefficients d) i *
      (griessConwayEncode y).2.2 (golayLabelCoefficients d) i) = _
  rw [Fin.sum_univ_add (a := 2048) (b := 2048)]
  have hlow (d : Fin 2048) : Fin.castAdd 2048 d =
      (⟨d.val, by omega⟩ : Fin 4096) := by rfl
  have hhigh (d : Fin 2048) : Fin.natAdd 2048 d =
      (⟨d.val + 2048, by omega⟩ : Fin 4096) := Fin.ext (by simp)
  simp only [hlow, hhigh, griessConwayEncode, spinDictionaryCode_low,
    spinDictionaryCode_high, golayLabel_low_last, golayLabel_high_last,
    qSign_zero, qSign_one, one_mul, neg_mul, ← sub_eq_add_neg]
  conv_rhs => rw [trialityBlockUncurry_sum 2048 24
    (fun k => (trialityBlocksEquiv x).2.2.2 1 k * (trialityBlocksEquiv y).2.2.2 1 k),
    trialityBlockUncurry_sum 2048 24
    (fun k => (trialityBlocksEquiv x).2.2.2 2 k * (trialityBlocksEquiv y).2.2.2 2 k)]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  have hsign : (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
      (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) = 1 := by
    split <;> norm_num
  have hf := real_normalized_pair_fourier
    ((trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d, i)))
    ((trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d, i)))
    ((trialityBlocksEquiv y).2.2.2 2 (finProdFinEquiv (d, i)))
    ((trialityBlocksEquiv y).2.2.2 1 (finProdFinEquiv (d, i)))
    (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ))
    (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)
    (qSign_sq _) hsign
  rw [add_comm
    ((trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d, i)) *
      (trialityBlocksEquiv y).2.2.2 1 (finProdFinEquiv (d, i)))
    ((trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d, i)) *
      (trialityBlocksEquiv y).2.2.2 2 (finProdFinEquiv (d, i)))]
  exact hf

/-- The concrete Conway dictionary is an isometry for the specified Griess form. -/
theorem griessForm_eq_conwayCoordinates (x y : GriessSpace) :
    griessForm x y =
      (∑ i, ∑ j, (griessConwayEncode x).1 i j * (griessConwayEncode y).1 i j) +
      (∑ r, (griessConwayEncode x).2.1 r * (griessConwayEncode y).2.1 r) +
      (∑ t, ∑ i, (griessConwayEncode x).2.2 t i * (griessConwayEncode y).2.2 t i) := by
  rw [griessForm_eq_trialityBlockForm, griessConwayEncode_matrix_form,
    griessConwayEncode_short_form, griessConwayEncode_tensor_form]
  set b := trialityBlocksEquiv x
  set c := trialityBlocksEquiv y
  simp only [trialityBlockForm, Fin.sum_univ_three]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
