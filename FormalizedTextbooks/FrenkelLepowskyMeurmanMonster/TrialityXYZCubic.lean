/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Zero cubic coefficients of the actual XYZ source families.
These follow from the orthogonal Conway blocks and all-one spin parity.
Source: Conway's Griess product; Seysen, §8.1, Table 5.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayFrobenius
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairOddQProducts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawCubic_tensor_zero (f g h : SpinIndex → Fin 24 → ℝ) :
    conwayRawForm (conwayRawProduct (0, (0, f)) (0, (0, g))) (0, (0, h)) = 0 := by
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, Matrix.zero_apply, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add]
  simp [conwayTensorForm, conwayRawProduct, spinOperator]

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawCubic_noTensor_tensor_zero
    (a b : Matrix (Fin 24) (Fin 24) ℝ) (x y : GriessShortIndex → ℝ)
    (h : SpinIndex → Fin 24 → ℝ) :
    conwayRawForm (conwayRawProduct (a, (x, 0)) (b, (y, 0))) (0, (0, h)) = 0 := by
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, Matrix.zero_apply, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add]
  simp [conwayTensorForm, conwayRawProduct, spinOperator]

/-- Pure tensor vectors have zero cubic product coefficient. -/
theorem griessCubic_tensor_zero (x y z : GriessSpace)
    (hx1 : (griessConwayEncode x).1 = 0) (hx2 : (griessConwayEncode x).2.1 = 0)
    (hy1 : (griessConwayEncode y).1 = 0) (hy2 : (griessConwayEncode y).2.1 = 0)
    (hz1 : (griessConwayEncode z).1 = 0) (hz2 : (griessConwayEncode z).2.1 = 0) :
    griessForm (griessProd x y) z = 0 := by
  rw [griessForm_eq_conwayRawForm, griessProd_encode]
  have hx : griessConwayEncode x = (0, (0, (griessConwayEncode x).2.2)) := by
    exact Prod.ext hx1 (Prod.ext hx2 rfl)
  have hy : griessConwayEncode y = (0, (0, (griessConwayEncode y).2.2)) := by
    exact Prod.ext hy1 (Prod.ext hy2 rfl)
  have hz : griessConwayEncode z = (0, (0, (griessConwayEncode z).2.2)) := by
    exact Prod.ext hz1 (Prod.ext hz2 rfl)
  rw [hx, hy, hz]
  exact conwayRawCubic_tensor_zero _ _ _

/-- Two vectors without a tensor block have zero cubic coefficient against
any pure tensor vector. -/
theorem griessCubic_noTensor_tensor_zero (x y z : GriessSpace)
    (hx : (griessConwayEncode x).2.2 = 0) (hy : (griessConwayEncode y).2.2 = 0)
    (hz1 : (griessConwayEncode z).1 = 0) (hz2 : (griessConwayEncode z).2.1 = 0) :
    griessForm (griessProd x y) z = 0 := by
  rw [griessForm_eq_conwayRawForm, griessProd_encode]
  have hx' : griessConwayEncode x =
      ((griessConwayEncode x).1, ((griessConwayEncode x).2.1, 0)) :=
    Prod.ext rfl (Prod.ext rfl hx)
  have hy' : griessConwayEncode y =
      ((griessConwayEncode y).1, ((griessConwayEncode y).2.1, 0)) :=
    Prod.ext rfl (Prod.ext rfl hy)
  have hz : griessConwayEncode z = (0, (0, (griessConwayEncode z).2.2)) :=
    Prod.ext hz1 (Prod.ext hz2 rfl)
  rw [hx', hy', hz]
  exact conwayRawCubic_noTensor_tensor_zero _ _ _ _ _

theorem trialityXYZBasis_matrix_zero (s : Fin 3) (k : Fin 49152) :
    (griessConwayEncode (trialityXYZBasis s k)).1 = 0 := by
  rw [griessConwayEncode_XYZ_basis]

theorem trialityXYZBasis_nonzero_short_zero (s : Fin 3) (k : Fin 49152) (hs : s ≠ 0) :
    (griessConwayEncode (trialityXYZBasis s k)).2.1 = 0 := by
  rw [griessConwayEncode_XYZ_basis]
  ext r
  rcases r with ⟨u,p⟩ | (⟨o,e⟩ | ⟨d,j⟩) <;> simp [hs.symm]

theorem trialityXYZBasis_X_tensor_zero (k : Fin 49152) :
    (griessConwayEncode (trialityXYZBasis 0 k)).2.2 = 0 := by
  rw [griessConwayEncode_XYZ_basis]
  ext t i
  simp

/-- All YYY, YYZ, YZZ and ZZZ coefficients vanish, for arbitrary source labels. -/
theorem trialityXYZ_cubic_tensor_zero (s t u : Fin 3) (k l m : Fin 49152)
    (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) :
    griessForm (griessProd (trialityXYZBasis s k) (trialityXYZBasis t l))
      (trialityXYZBasis u m) = 0 := by
  exact griessCubic_tensor_zero _ _ _ (trialityXYZBasis_matrix_zero _ _)
    (trialityXYZBasis_nonzero_short_zero _ _ hs) (trialityXYZBasis_matrix_zero _ _)
    (trialityXYZBasis_nonzero_short_zero _ _ ht) (trialityXYZBasis_matrix_zero _ _)
    (trialityXYZBasis_nonzero_short_zero _ _ hu)

/-- All XXY and XXZ coefficients vanish. -/
theorem trialityXYZ_cubic_XX_tensor_zero (k l m : Fin 49152) (s : Fin 3) (hs : s ≠ 0) :
    griessForm (griessProd (trialityXYZBasis 0 k) (trialityXYZBasis 0 l))
      (trialityXYZBasis s m) = 0 := by
  exact griessCubic_noTensor_tensor_zero _ _ _ (trialityXYZBasis_X_tensor_zero _)
    (trialityXYZBasis_X_tensor_zero _) (trialityXYZBasis_matrix_zero _ _)
    (trialityXYZBasis_nonzero_short_zero _ _ hs)

/-- Adding the all-one code coefficient switches the two spin representatives. -/
def trialitySpinOmega : SpinIndex := Pi.single 11 1

/-- An odd function under the all-one shift has zero finite spin sum. -/
theorem trialitySpinSum_zero_of_omega_neg (f : SpinIndex → ℝ)
    (hf : ∀ t, f (t + trialitySpinOmega) = -f t) : ∑ t, f t = 0 := by
  have he := Equiv.sum_comp (Equiv.addRight trialitySpinOmega) f
  have hn : (∑ t, f (t + trialitySpinOmega)) = -(∑ t, f t) := by
    simp_rw [hf]
    rw [Finset.sum_neg_distrib]
  have he' : (∑ t, f (t + trialitySpinOmega)) = ∑ t, f t := he
  linarith

/-- Tensor pairings vanish for opposite all-one-shift parities. -/
theorem conwayTensorForm_zero_of_omega_parity (f g : SpinIndex → Fin 24 → ℝ)
    (a b : ℝ) (hab : a * b = -1)
    (hf : ∀ t i, f (t + trialitySpinOmega) i = a * f t i)
    (hg : ∀ t i, g (t + trialitySpinOmega) i = b * g t i) :
    conwayTensorForm f g = 0 := by
  change (∑ t, ∑ i, f t i * g t i) = 0
  apply trialitySpinSum_zero_of_omega_neg
  intro t
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]
  calc
    (a * f t i) * (b * g t i) = (a * b) * (f t i * g t i) := by ring
    _ = -(f t i * g t i) := by rw [hab]; ring

/-- A short lift with odd Ω modulation reverses the Ω parity of every spin vector. -/
theorem spinOperator_omega_parity (q : Q) (hq : spinModulation q 11 = 1)
    (f : SpinSpace) (a : ℝ) (hf : ∀ t, f (t + trialitySpinOmega) = a * f t)
    (t : SpinIndex) :
    spinOperator q f (t + trialitySpinOmega) = -a * spinOperator q f t := by
  have hdot : spinDot (spinModulation q) trialitySpinOmega = 1 := by
    simp [spinDot, trialitySpinOmega, Pi.single_apply, hq]
  have hphase : spinPhase q (t + trialitySpinOmega) = spinPhase q t + 1 := by
    simp only [spinPhase, spinDot_add_right, hdot, add_assoc]
  have ht : t + trialitySpinOmega + spinTranslation q =
      (t + spinTranslation q) + trialitySpinOmega := by abel
  change qSign (spinPhase q (t + trialitySpinOmega)) *
    f (t + trialitySpinOmega + spinTranslation q) =
      -a * (qSign (spinPhase q t) * f (t + spinTranslation q))
  rw [hphase, qSign_add, ht, hf]
  have hsign : qSign (1 : ZMod 2) = -1 := by norm_num [qSign]
  rw [hsign]
  ring

theorem xyz_sum_single_smul {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid V] [Module ℝ V] (F : ι → V) (r : ι) :
    (∑ u, (Pi.single r (1 : ℝ) : ι → ℝ) u • F u) = F r := by
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
theorem xyzShortTensor_single_apply (r : GriessShortIndex)
    (f : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    conwayShortTensorProduct (Pi.single r 1) f t i =
      (∑ j, spinOperator (griessShortQ r) (fun v => f v j) t *
        conwayTensorCoefficient r j i) / 8 := by
  rw [conwayShortTensorProduct, xyz_sum_single_smul]
  simp only [Pi.smul_apply, smul_eq_mul, conwayTensorShortOperator_apply]
  ring

set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
/-- The short-times-tensor Conway rule inherits the reversed Ω parity. -/
theorem conwayShortTensorProduct_single_omega_parity (r : GriessShortIndex)
    (hr : spinModulation (griessShortQ r) 11 = 1)
    (f : SpinIndex → Fin 24 → ℝ) (a : ℝ)
    (hf : ∀ t i, f (t + trialitySpinOmega) i = a * f t i) (t : SpinIndex) (i : Fin 24) :
    conwayShortTensorProduct (Pi.single r 1) f (t + trialitySpinOmega) i =
      -a * conwayShortTensorProduct (Pi.single r 1) f t i := by
  simp only [xyzShortTensor_single_apply]
  have hs (j : Fin 24) := spinOperator_omega_parity (griessShortQ r) hr
    (fun v => f v j) a (fun v => hf v j) t
  simp_rw [hs]
  have hsum : (∑ j, (-a * spinOperator (griessShortQ r) (fun v => f v j) t) *
      conwayTensorCoefficient r j i) =
      -a * ∑ j, spinOperator (griessShortQ r) (fun v => f v j) t *
        conwayTensorCoefficient r j i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
/-- Odd-modulation short vectors have zero cubic coefficient against two
tensors of the same Ω parity. -/
theorem conwayRawCubic_short_tensor_same_parity_zero (r : GriessShortIndex)
    (hr : spinModulation (griessShortQ r) 11 = 1)
    (f g : SpinIndex → Fin 24 → ℝ) (a : ℝ) (ha : a * a = 1)
    (hf : ∀ t i, f (t + trialitySpinOmega) i = a * f t i)
    (hg : ∀ t i, g (t + trialitySpinOmega) i = a * g t i) :
    conwayRawForm (conwayRawProduct (conwayShortBasis r) (0, (0, f))) (0, (0, g)) = 0 := by
  have hT : (conwayRawProduct (conwayShortBasis r) (0, (0, f))).2.2 =
      conwayShortTensorProduct (Pi.single r 1) f := by
    ext t i
    rw [conwayShortTensorProduct_apply]
    simp [conwayRawProduct, conwayShortBasis, spinOperator]
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, Matrix.zero_apply, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add]
  rw [hT]
  apply conwayTensorForm_zero_of_omega_parity _ _ (-a) a
  · rw [neg_mul, ha]
  · exact conwayShortTensorProduct_single_omega_parity r hr f a hf
  · exact hg

theorem xyz_sum_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (u : ι) : (∑ v, f v * (Pi.single u 1 : ι → ℝ) v) = f u := by
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

set_option backward.isDefEq.respectTransparency false in
theorem xyzRawForm_shortBasis (w : ConwayRawSpace) (u : GriessShortIndex) :
    conwayRawForm w (conwayShortBasis u) = w.2.1 u := by
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, conwayShortBasis,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, map_zero, add_zero]
  exact xyz_sum_mul_single _ u

set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual short-basis cubic coefficient is its preferred-Q product phase. -/
theorem conwayRawCubic_short_basis (r s u : GriessShortIndex) :
    conwayRawForm (conwayRawProduct (conwayShortBasis r) (conwayShortBasis s))
      (conwayShortBasis u) =
    if (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then
      qSign (toAdd (griessShortQ r * griessShortQ s).coeff) else 0 := by
  rw [xyzRawForm_shortBasis, conwayRawProduct_shortBasis]

/-- A product with even last modulation cannot equal an odd-modulation base. -/
theorem qProduct_base_ne_of_last_modulation (r s u : Q)
    (hr : spinModulation r 11 = 1) (hs : spinModulation s 11 = 1)
    (hu : spinModulation u 11 = 1) : (r * s).base ≠ u.base := by
  intro h
  have hh : spinModulation (r * s) 11 = spinModulation u 11 :=
    congrArg (fun b : Multiplicative (Fin 24 → ZMod 2) => toAdd b (Fin.natAdd 12 (11 : Fin 12))) h
  rw [spinModulation_mul, Pi.add_apply, hr, hs, hu] at hh
  exact (show (1 + 1 : ZMod 2) ≠ 1 by decide) hh

/-- Three X-family coefficients vanish because three odd modulations cannot
sum to zero in the actual preferred-Q bases. -/
theorem trialityXYZ_cubic_XXX_zero (k l m : Fin 49152) :
    griessForm (griessProd (trialityXYZBasis 0 k) (trialityXYZBasis 0 l))
      (trialityXYZBasis 0 m) = 0 := by
  obtain ⟨⟨d,i⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective k
  obtain ⟨⟨e,j⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective l
  obtain ⟨⟨f,h⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective m
  rw [griessForm_eq_conwayRawForm, griessProd_encode, griessConwayEncode_X_basis,
    griessConwayEncode_X_basis, griessConwayEncode_X_basis]
  change conwayRawForm (conwayRawProduct (conwayShortBasis (Sum.inr (Sum.inr (d,i))))
    (conwayShortBasis (Sum.inr (Sum.inr (e,j)))))
      (conwayShortBasis (Sum.inr (Sum.inr (f,h)))) = 0
  rw [conwayRawCubic_short_basis]
  have hn := qProduct_base_ne_of_last_modulation
    (griessShortQ (Sum.inr (Sum.inr (d,i)))) (griessShortQ (Sum.inr (Sum.inr (e,j))))
    (griessShortQ (Sum.inr (Sum.inr (f,h))))
    (griessOdd_modulation_omega d i) (griessOdd_modulation_omega e j)
    (griessOdd_modulation_omega f h)
  simp only [hn, ite_false]

/-- XYY vanishes because an odd short lift reverses Y's Ω parity. -/
theorem trialityXYZ_cubic_XYY_zero (k l m : Fin 49152) :
    griessForm (griessProd (trialityXYZBasis 0 k) (trialityXYZBasis 1 l))
      (trialityXYZBasis 1 m) = 0 := by
  obtain ⟨⟨d,i⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective k
  obtain ⟨⟨e,j⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective l
  obtain ⟨⟨f,h⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective m
  rw [griessForm_eq_conwayRawForm, griessProd_encode, griessConwayEncode_X_basis,
    griessConwayEncode_Y_basis, griessConwayEncode_Y_basis]
  change conwayRawForm (conwayRawProduct (conwayShortBasis (Sum.inr (Sum.inr (d,i))))
    (0, (0, trialityYTensor e j))) (0, (0, trialityYTensor f h)) = 0
  apply conwayRawCubic_short_tensor_same_parity_zero _ (griessOdd_modulation_omega d i)
    _ _ (-1) (by norm_num)
  · intro t b
    simpa only [trialitySpinOmega, neg_one_mul] using trialityYTensor_add_omega e j t b
  · intro t b
    simpa only [trialitySpinOmega, neg_one_mul] using trialityYTensor_add_omega f h t b

/-- XZZ vanishes because an odd short lift reverses Z's Ω parity. -/
theorem trialityXYZ_cubic_XZZ_zero (k l m : Fin 49152) :
    griessForm (griessProd (trialityXYZBasis 0 k) (trialityXYZBasis 2 l))
      (trialityXYZBasis 2 m) = 0 := by
  obtain ⟨⟨d,i⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective k
  obtain ⟨⟨e,j⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective l
  obtain ⟨⟨f,h⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective m
  rw [griessForm_eq_conwayRawForm, griessProd_encode, griessConwayEncode_X_basis,
    griessConwayEncode_Z_basis, griessConwayEncode_Z_basis]
  change conwayRawForm (conwayRawProduct (conwayShortBasis (Sum.inr (Sum.inr (d,i))))
    (0, (0, trialityZTensor e j))) (0, (0, trialityZTensor f h)) = 0
  apply conwayRawCubic_short_tensor_same_parity_zero _ (griessOdd_modulation_omega d i)
    _ _ 1 (by norm_num)
  · intro t b
    simpa only [trialitySpinOmega, one_mul] using trialityZTensor_add_omega e j t b
  · intro t b
    simpa only [trialitySpinOmega, one_mul] using trialityZTensor_add_omega f h t b

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
