/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.EulerianConnesFormula
public import MathlibExt.LinearAlgebra.TensorPower.IntegralEulerianComparison

/-!
# The normalized Connes shift of Eulerian weights

Let k be a commutative ℚ-algebra and A a commutative unital k-algebra.
For normalized Connes B_n:N_n(A)→N_{n+1}(A), the Eulerian components
satisfy e_{n+1}^{(j)}B_n e_n^{(i)}=0 when j≠i+1.
Finite projector completeness then gives
B_n e_n^{(i)}=e_{n+1}^{(i+1)}B_n and e_{n+1}^{(0)}B_n=0.

For every rational parameter a, the bar-lambda convolution obeys
Λ_{n+1}(a)B_n=a B_nΛ_n(a).
For positive integer m, Loday's operation
λ_n^m=(−1)^{m−1}Λ_n(m) obeys the same scalar law with m.
All statements include degree zero.

Reference: J.-L. Loday, Cyclic Homology, §§2.1 and 4.5.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]

local notation "Q" => ModuleCat.Algebra.Hochschild.quotientCarrier k A

private theorem twoPow_injective : Function.Injective (fun n : ℕ => (2 : ℚ) ^ n) := by
  apply StrictMono.injective
  apply strictMono_nat_of_lt_succ
  intro n
  rw [pow_succ]
  have hp : (0 : ℚ) < 2 ^ n := pow_pos (by norm_num) n
  nlinarith

private theorem two_mul_scalar (i : ℕ) :
    (2 : k) * algebraMap ℚ k ((2 : ℚ) ^ i) = algebraMap ℚ k ((2 : ℚ) ^ (i + 1)) := by
  rw [pow_succ, map_mul, map_ofNat]
  ring

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
For j≠i+1, the off-weight component of normalized Connes
boundary vanishes: e_{n+1}^{(j)}B_n e_n^{(i)}=0. -/
theorem normalizedEulerian_connes_cross_zero (n i j : ℕ) (hij : j ≠ i + 1) :
    (normalizedEulerianOperator k A A (n + 1) j).comp
      ((NonUnital.normalizedBoundary k A n).hom.comp (normalizedEulerianOperator k A A n i)) = 0 := by
  rw [normalizedConnesBoundary_eq_formula]
  change (normalizedEulerianOperator k A A (n + 1) j).comp
    ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i)) = 0
  by_cases hi : i ≤ n
  · by_cases hj : j ≤ n + 1
    · let X : A ⊗[k] TensorPower k n Q →ₗ[k] A ⊗[k] TensorPower k (n + 1) Q :=
        (normalizedEulerianOperator k A A (n + 1) j).comp
          ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i))
      have htwo := normalizedConvolutionTwo_connesBoundary k A n
      rw [normalizedConnesBoundary_eq_formula] at htwo
      change (normalizedConvolutionOperator k A A (n + 1) 2).comp (normalizedConnesFormula k A n) =
        (2 : k) • (normalizedConnesFormula k A n).comp (normalizedConvolutionOperator k A A n 2) at htwo
      have h := congrArg (fun f : A ⊗[k] TensorPower k n Q →ₗ[k] A ⊗[k] TensorPower k (n + 1) Q =>
        (normalizedEulerianOperator k A A (n + 1) j).comp
          (f.comp (normalizedEulerianOperator k A A n i))) htwo
      simp only [LinearMap.comp_assoc, LinearMap.comp_smul, LinearMap.smul_comp] at h
      rw [← LinearMap.comp_assoc,
        normalizedEulerianOperator_comp_convolution k A A (n + 1) j hj 2] at h
      rw [normalizedConvolutionOperator_comp_eulerian k A A n i hi 2] at h
      simp only [LinearMap.comp_smul, LinearMap.smul_comp, smul_smul, two_mul_scalar] at h
      have hz : algebraMap ℚ k ((2 : ℚ) ^ j - (2 : ℚ) ^ (i + 1)) • X = 0 := by
        rw [map_sub]
        exact (_root_.sub_smul (algebraMap ℚ k ((2 : ℚ) ^ j))
          (algebraMap ℚ k ((2 : ℚ) ^ (i + 1))) X).trans (sub_eq_zero.mpr h)
      have hr : (2 : ℚ) ^ j - (2 : ℚ) ^ (i + 1) ≠ 0 :=
        sub_ne_zero.mpr (fun h => hij (twoPow_injective h))
      have hc := congrArg (fun Y : A ⊗[k] TensorPower k n Q →ₗ[k]
          A ⊗[k] TensorPower k (n + 1) Q =>
        algebraMap ℚ k (((2 : ℚ) ^ j - (2 : ℚ) ^ (i + 1))⁻¹) • Y) hz
      simpa only [smul_smul, ← map_mul, inv_mul_cancel₀ hr, map_one,
        one_smul, smul_zero, X] using hc
    · rw [normalizedEulerianOperator_outside k A A (n + 1) j (by omega), LinearMap.zero_comp]
  · rw [normalizedEulerianOperator_outside k A A n i (by omega),
      LinearMap.comp_zero, LinearMap.comp_zero]

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
Normalized Connes boundary raises Eulerian weight by one:
B_n e_n^{(i)}=e_{n+1}^{(i+1)}B_n for all n,i≥0. -/
theorem normalizedEulerian_connes_shift (n i : ℕ) :
    (NonUnital.normalizedBoundary k A n).hom.comp (normalizedEulerianOperator k A A n i) =
      (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp
        (NonUnital.normalizedBoundary k A n).hom := by
  rw [normalizedConnesBoundary_eq_formula]
  classical
  have hcross (p q : ℕ) (hpq : q ≠ p + 1) :
      (normalizedEulerianOperator k A A (n + 1) q).comp
        ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n p)) = 0 := by
    have hc := normalizedEulerian_connes_cross_zero k A n p q hpq
    rw [normalizedConnesBoundary_eq_formula] at hc
    exact hc
  have hleft :
      (normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i) =
      (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp
        ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i)) := by
    calc
      _ = (∑ j : Fin (n + 2), normalizedEulerianOperator k A A (n + 1) j.val).comp
          ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i)) := by
        rw [normalizedEulerianOperator_sum, LinearMap.id_comp]
      _ = ∑ j : Fin (n + 2), (normalizedEulerianOperator k A A (n + 1) j.val).comp
          ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i)) := by
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, LinearMap.sum_apply]
      _ = _ := by
        by_cases hi : i ≤ n
        · let j₀ : Fin (n + 2) := ⟨i + 1, by omega⟩
          apply Finset.sum_eq_single j₀
          · intro j _ hj
            exact hcross i j.val (fun h => hj (Fin.ext h))
          · intro hj
            exact (hj (Finset.mem_univ j₀)).elim
        · simp only [normalizedEulerianOperator_outside k A A n i (by omega),
            LinearMap.comp_zero, Finset.sum_const_zero]
  have hright :
      (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp
        (normalizedConnesFormula k A n) =
      (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp
        ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i)) := by
    calc
      _ = (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp
          ((normalizedConnesFormula k A n).comp
            (∑ j : Fin (n + 1), normalizedEulerianOperator k A A n j.val)) := by
        rw [normalizedEulerianOperator_sum, LinearMap.comp_id]
      _ = ∑ j : Fin (n + 1), (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp
          ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n j.val)) := by
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
      _ = _ := by
        by_cases hi : i ≤ n
        · let j₀ : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
          apply Finset.sum_eq_single j₀
          · intro j _ hj
            exact hcross j.val (i + 1) (by
              intro h
              have he : i = j.val := by omega
              exact hj (Fin.ext he.symm))
          · intro hj
            exact (hj (Finset.mem_univ j₀)).elim
        · simp only [normalizedEulerianOperator_outside k A A (n + 1) (i + 1) (by omega),
            LinearMap.zero_comp, Finset.sum_const_zero]
  exact hleft.trans hright.symm

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
The output weight-zero projection annihilates normalized
Connes boundary: e_{n+1}^{(0)}B_n=0. -/
theorem normalizedEulerian_connes_zero_weight (n : ℕ) :
    (normalizedEulerianOperator k A A (n + 1) 0).comp (NonUnital.normalizedBoundary k A n).hom = 0 := by
  rw [normalizedConnesBoundary_eq_formula]
  classical
  calc
    _ = (normalizedEulerianOperator k A A (n + 1) 0).comp
      ((normalizedConnesFormula k A n).comp
        (∑ i : Fin (n + 1), normalizedEulerianOperator k A A n i.val)) := by
      rw [normalizedEulerianOperator_sum, LinearMap.comp_id]
      rfl
    _ = ∑ i : Fin (n + 1), (normalizedEulerianOperator k A A (n + 1) 0).comp
      ((normalizedConnesFormula k A n).comp (normalizedEulerianOperator k A A n i.val)) := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hc := normalizedEulerian_connes_cross_zero k A n i.val 0 (by omega)
      rw [normalizedConnesBoundary_eq_formula] at hc
      exact hc

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
For every a∈ℚ, the coefficient-fixed bar-lambda convolution
satisfies Λ_{n+1}(a)B_n=algMap_ℚ(a) B_nΛ_n(a). -/
theorem normalizedConvolution_connesBoundary (n : ℕ) (a : ℚ) :
    (normalizedConvolutionOperator k A A (n + 1) a).comp (NonUnital.normalizedBoundary k A n).hom =
      algebraMap ℚ k a • (NonUnital.normalizedBoundary k A n).hom.comp
        (normalizedConvolutionOperator k A A n a) := by
  rw [normalizedConnesBoundary_eq_formula]
  let B : A ⊗[k] TensorPower k n Q →ₗ[k] A ⊗[k] TensorPower k (n + 1) Q :=
    normalizedConnesFormula k A n
  change (normalizedConvolutionOperator k A A (n + 1) a).comp B =
    algebraMap ℚ k a • B.comp (normalizedConvolutionOperator k A A n a)
  have hshift (i : ℕ) : B.comp (normalizedEulerianOperator k A A n i) =
      (normalizedEulerianOperator k A A (n + 1) (i + 1)).comp B := by
    have hs := normalizedEulerian_connes_shift k A n i
    rw [normalizedConnesBoundary_eq_formula] at hs
    exact hs
  have hzero : (normalizedEulerianOperator k A A (n + 1) 0).comp B = 0 := by
    have hz := normalizedEulerian_connes_zero_weight k A n
    rw [normalizedConnesBoundary_eq_formula] at hz
    exact hz
  rw [normalizedConvolutionOperator_eq_sum, normalizedConvolutionOperator_eq_sum]
  apply LinearMap.ext
  intro x
  have hzeroVal : normalizedEulerianOperator k A A (n + 1) 0 (B x) = 0 :=
    congrArg (fun f : A ⊗[k] TensorPower k n Q →ₗ[k] A ⊗[k] TensorPower k (n + 1) Q => f x) hzero
  have hshiftVal (i : ℕ) : normalizedEulerianOperator k A A (n + 1) (i + 1) (B x) =
      B (normalizedEulerianOperator k A A n i x) :=
    (congrArg (fun f : A ⊗[k] TensorPower k n Q →ₗ[k] A ⊗[k] TensorPower k (n + 1) Q => f x)
      (hshift i)).symm
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, map_one, one_smul, hzeroVal, zero_add, Fin.val_succ]
  simp_rw [hshiftVal]
  simp only [pow_succ, map_mul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1}, N_n=A⊗[k]Ā^{⊗n}, and
let e_n^{(i)} be the normalized rational Eulerian projectors.
For m>0, the positive-integer Loday operation
λ_n^m=(−1)^{m−1}Λ_n(m) satisfies
λ_{n+1}^m B_n=m B_n λ_n^m. -/
theorem normalizedTrueIntegerLambda_connesBoundary (n m : ℕ) (hm : 0 < m) :
    (TensorPower.coefficientTrueIntegerLambdaOperator (k := k) (M := A)
      (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) (n + 1) m hm).comp
        (NonUnital.normalizedBoundary k A n).hom =
      (m : k) • (NonUnital.normalizedBoundary k A n).hom.comp
        (TensorPower.coefficientTrueIntegerLambdaOperator (k := k) (M := A)
          (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n m hm) := by
  rw [normalizedConnesBoundary_eq_formula]
  rw [TensorPower.coefficientTrueIntegerLambdaOperator_eq_eulerian,
    TensorPower.coefficientTrueIntegerLambdaOperator_eq_eulerian]
  change ((-1 : k) ^ (m - 1) • normalizedConvolutionOperator k A A (n + 1) (m : ℚ)).comp
      (normalizedConnesFormula k A n) =
    (m : k) • (normalizedConnesFormula k A n).comp
      ((-1 : k) ^ (m - 1) • normalizedConvolutionOperator k A A n (m : ℚ))
  have hparam := normalizedConvolution_connesBoundary k A n (m : ℚ)
  rw [normalizedConnesBoundary_eq_formula] at hparam
  change (normalizedConvolutionOperator k A A (n + 1) (m : ℚ)).comp (normalizedConnesFormula k A n) =
    algebraMap ℚ k (m : ℚ) • (normalizedConnesFormula k A n).comp
      (normalizedConvolutionOperator k A A n (m : ℚ)) at hparam
  rw [LinearMap.smul_comp, hparam, LinearMap.comp_smul]
  simp only [map_natCast, smul_smul]
  rw [mul_comm ((-1 : k) ^ (m - 1)) (m : k)]

end ModuleCat.Algebra.Hochschild.Symmetric
