/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorXiCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpatialRational

/-! The genuine inverse Xi uses the reversed Gaussian factors and one64-term sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- The inverse source spin operator applies the original diagonal after the original translation Gaussian. -/
theorem generatedAxisGlobalXiInverse_spin_apply (f : SpinSpace) (t : SpinIndex) :
    (xiSpinHolomorph⁻¹).val f t =
      (nortonUIntegerGammaSign t : ℝ) * ((1 / 8 : ℝ) *
        ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) * f (t + xiGrayCode a)) := by
  change xiSpinGamma (xiSpinG f) t = _
  rw [nortonUIntegerGamma_apply, nortonUIntegerG_apply]

/-- The actual inverse physical matrix has its full transposed integral numerator. -/
theorem generatedAxisGlobalXiInverse_spatial_basis (i j : Fin 24) :
    (co1XiIsometry⁻¹).val (Pi.single j 1) i = (co1XiNumerator j i : ℝ) / 2 := by
  have h := congrFun (generatedAxisGlobalOddSpatialBaseQ_inverse 0 (Pi.single j 1)) i
  change (co1XiIsometry⁻¹).val (Pi.single j 1) i =
    ((co1XiMatrixQ.transpose).map (Rat.castHom ℝ) *ᵥ Pi.single j 1) i at h
  rw [Matrix.mulVec_single_one] at h
  change (co1XiIsometry⁻¹).val (Pi.single j 1) i = (co1XiMatrixQ j i : ℝ) at h
  rw [h]
  change (((co1XiNumerator j i : ℚ) / 2 : ℚ) : ℝ) = _
  norm_num

set_option maxHeartbeats 2000000 in
/-- Every original transposed Xi entry outside its physical tetrad is exactly zero. -/
theorem generatedAxisGlobalXiInverse_numerator_tetrads : ∀ i : Fin 24, ∀ a : Fin 6,
    ∀ b : Fin 4,
    co1XiNumerator (finProdFinEquiv (a, b)) i =
      if a.val = i.val / 4 then co1XiNumerator (generatedAxisGlobalXiColumn i b) i else 0 := by
  decide +kernel

/-- The complete actual transposed row has exactly its four original physical inputs. -/
theorem generatedAxisGlobalXiInverse_numerator_row (i : Fin 24) (v : Fin 24 → ℝ) :
    (∑ j : Fin 24, (co1XiNumerator j i : ℝ) * v j) =
      ∑ b : Fin 4, (co1XiNumerator (generatedAxisGlobalXiColumn i b) i : ℝ) *
        v (generatedAxisGlobalXiColumn i b) := by
  let k : Fin 6 := ⟨i.val / 4, by have hi := i.isLt; omega⟩
  have hc (b : Fin 4) : finProdFinEquiv (k, b) = generatedAxisGlobalXiColumn i b := by
    apply Fin.ext
    change b.val + 4 * k.val = 4 * (i.val / 4) + b.val
    dsimp [k]
    omega
  have hs := Equiv.sum_comp (finProdFinEquiv : Fin 6 × Fin 4 ≃ Fin 24)
    (fun j => (co1XiNumerator j i : ℝ) * v j)
  rw [← hs, Fintype.sum_prod_type]
  calc
    _ = ∑ a : Fin 6, if a = k then
        ∑ b : Fin 4, (co1XiNumerator (generatedAxisGlobalXiColumn i b) i : ℝ) *
          v (generatedAxisGlobalXiColumn i b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = k
      · subst a
        simp only [ite_true, hc]
      · have hav : a.val ≠ i.val / 4 := by
          intro h
          apply ha
          exact Fin.ext h
        simp only [ha, ite_false]
        simp_rw [generatedAxisGlobalXiInverse_numerator_tetrads]
        simp only [hav, ↓reduceIte, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    _ = _ := by simp

/-- The entire inverse rational tensor formula has only64 original spin inputs and four physical inputs. -/
def generatedAxisGlobalRationalTensorXiInverseCached (T : GeneratedAxisGlobalRationalTensor)
    (k : Fin 4096) (i : Fin 24) : ℚ :=
  (∑ a : Fin 64, ∑ b : Fin 4,
    let m := generatedSixthSpinLabelXor k (generatedSixthGrayCodeLabel a)
    let j := generatedAxisGlobalXiColumn i b
    let z := T m j
    if z = 0 then 0 else
      (generatedSixthGraySign a : ℚ) * (generatedSixthSpinGammaFast k : ℚ) *
        (co1XiNumerator j i : ℚ) * z) / 16

/-- The complete original inverse tensor coefficient is its true reversed-Gaussian four-column sum. -/
theorem generatedAxisGlobalXiInverse_tensor_tetrad (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation xiSpinLocalFiber⁻¹ T t i =
      (∑ a : XiGrayIndex, ∑ b : Fin 4,
        qSign (xiGrayQuadratic a) * (nortonUIntegerGammaSign t : ℝ) *
          (co1XiNumerator (generatedAxisGlobalXiColumn i b) i : ℝ) *
            T (t + xiGrayCode a) (generatedAxisGlobalXiColumn i b)) / 16 := by
  rw [generatedAxisGlobalTensor_local_coordinate]
  change (∑ j : Fin 24, (xiSpinHolomorph⁻¹).val (fun u => T u j) t *
    (co1XiIsometry⁻¹).val (Pi.single j 1) i) = _
  simp_rw [generatedAxisGlobalXiInverse_spin_apply, generatedAxisGlobalXiInverse_spatial_basis]
  calc
    _ = (∑ j : Fin 24, ∑ a : XiGrayIndex,
        qSign (xiGrayQuadratic a) * (nortonUIntegerGammaSign t : ℝ) *
          (co1XiNumerator j i : ℝ) * T (t + xiGrayCode a) j) / 16 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply congrArg (fun z : ℝ => z / 16)
      apply Finset.sum_congr rfl
      intro a _
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum,
        generatedAxisGlobalXiInverse_numerator_row]
      simp only [Finset.mul_sum]

/-- Every cached inverse coordinate equals the whole genuine inverse original tensor action. -/
theorem generatedAxisGlobalRationalTensorXiInverseCached_actual
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation xiSpinLocalFiber⁻¹ (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalRationalTensorXiInverseCached T) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [generatedAxisGlobalXiInverse_tensor_tetrad]
  rw [← Equiv.sum_comp generatedSixthGrayEquiv]
  simp only [generatedAxisGlobalRationalTensorReal,
    generatedAxisGlobalRationalTensorXiInverseCached, generatedAxisGlobalSpinLabel_coeff,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, apply_ite,
    Rat.cast_zero]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show generatedSixthGrayEquiv a = generatedSixthGrayCoefficients a from rfl]
  have hc : xiGrayCode (generatedSixthGrayCoefficients a) =
      golayLabelCoefficients (generatedSixthGrayCodeLabel a) :=
    (funext (generatedSixth_gray_code a)).symm
  rw [hc, ← generatedSixth_spin_label_xor, generatedAxisGlobalSpinLabel_coeff,
    ← generatedSixth_spin_gamma_fast, ← xiGraySign_real, ← generatedSixth_gray_sign]
  split_ifs with hz
  · simp only [hz, Rat.cast_zero, zero_div, mul_zero]
  · ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
