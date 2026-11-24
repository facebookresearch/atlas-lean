/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianPolynomialCoefficients
public import MathlibExt.LinearAlgebra.TensorPower.PermutationRepresentation
public import MathlibExt.LinearAlgebra.TensorPower.ShuffleCutDescents

/-!
# Rational Eulerian elements and the two-cut sum

The descent polynomial defines a rational signed group-ring element.
Its polynomial coefficients are the Eulerian elements; evaluation at one
is the unit and coefficients beyond the exterior degree vanish. Evaluation
at two is the full signed shuffle-cut sum.

Here `eulerianLambda n a` denotes the convolution family `∑ i, a^i eₙⁱ`.
At a positive integer parameter `m`, the signed lambda operation has the
additional scalar `(-1)^(m - 1)`. In particular the signed second operation
is the negative of the convolution value at two. Rational parameters
interpolate only the convolution family; degree zero keeps its unit value.
-/

@[expose] public section
noncomputable section

open scoped BigOperators TensorProduct

universe u v w

namespace Equiv.Perm

/-- The actual signed coefficient of the homogeneous Eulerian polynomial. -/
def eulerianCoefficient (n i : ℕ) (σ : Perm (Fin n)) : ℚ :=
  (descentBinomialPolynomial n (descentNumber σ)).coeff i * ((σ.sign : ℤ) : ℚ)

/-- The actual rational group-ring coefficient element in every homogeneous degree. -/
def eulerianElement (n i : ℕ) : MonoidAlgebra ℚ (Perm (Fin n)) :=
  ∑ σ : Perm (Fin n), MonoidAlgebra.single σ (eulerianCoefficient n i σ)

/-- Evaluation of the actual signed descent polynomial in the original group ring. -/
def eulerianLambda (n : ℕ) (t : ℚ) : MonoidAlgebra ℚ (Perm (Fin n)) :=
  ∑ σ : Perm (Fin n), MonoidAlgebra.single σ
    ((descentBinomialPolynomial n (descentNumber σ)).eval t * ((σ.sign : ℤ) : ℚ))

/-- The finite coefficient expansion of the actual evaluated element. -/
theorem eulerianLambda_eq_sum (n : ℕ) (t : ℚ) :
    eulerianLambda n t = ∑ i : Fin (n + 1), t ^ i.val • eulerianElement n i.val := by
  classical
  ext σ
  simp only [eulerianLambda, eulerianElement, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_smul]
  simp only [MonoidAlgebra.coeff_single]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [descentBinomialPolynomial_eval_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [eulerianCoefficient, smul_eq_mul]
  ring

/-- The original top Eulerian coefficient is the actual alternating coefficient divided by the original factorial. -/
theorem eulerianCoefficient_top (n : ℕ) (σ : Perm (Fin n)) :
    eulerianCoefficient n n σ = (Nat.factorial n : ℚ)⁻¹ * ((σ.sign : ℤ) : ℚ) := by
  rw [eulerianCoefficient, descentBinomialPolynomial_coeff_degree]

/-- The actual highest Eulerian element is the original finite antisymmetrizer divided by factorial. -/
theorem eulerianElement_top (n : ℕ) :
    eulerianElement n n = (Nat.factorial n : ℚ)⁻¹ •
      (∑ σ : Perm (Fin n), MonoidAlgebra.single σ ((σ.sign : ℤ) : ℚ)) := by
  classical
  unfold eulerianElement
  rw [Finset.smul_sum]
  simp_rw [eulerianCoefficient_top, MonoidAlgebra.smul_single, smul_eq_mul]

/-- Actual coefficients beyond the original homogeneous degree are zero. -/
theorem eulerianCoefficient_outside (n i : ℕ) (σ : Perm (Fin n)) (hi : n < i) :
    eulerianCoefficient n i σ = 0 := by
  rw [eulerianCoefficient,
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((descentBinomialPolynomial_natDegree_le n (descentNumber σ)).trans_lt hi), zero_mul]

/-- The original degree-zero polynomial gives exactly one zero-weight coefficient and no others. -/
theorem eulerianCoefficient_degree_zero (i : ℕ) (σ : Perm (Fin 0)) :
    eulerianCoefficient 0 i σ = if i = 0 then 1 else 0 := by
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst σ
  simp [eulerianCoefficient, descentBinomialPolynomial, Polynomial.coeff_one]

/-- Every positive degree has no zero-weight coefficient. -/
theorem eulerianCoefficient_zero_weight (n : ℕ) (σ : Perm (Fin n)) (hn : 0 < n) :
    eulerianCoefficient n 0 σ = 0 := by
  rw [eulerianCoefficient, descentBinomialPolynomial_coeff_zero n (descentNumber σ)
    hn (descentNumber_lt σ hn), zero_mul]

/-- At one the actual rational element is the original group-ring unit. -/
theorem eulerianLambda_one (n : ℕ) : eulerianLambda n 1 = 1 := by
  classical
  cases n with
  | zero =>
    let _ : Unique (Perm (Fin 0)) :=
      { default := 1, uniq := fun σ => Subsingleton.elim _ _ }
    rw [eulerianLambda, Fintype.sum_unique]
    simp [descentBinomialPolynomial, MonoidAlgebra.one_def]
  | succ n =>
    have hcoeff (σ : Perm (Fin (n + 1))) :
        (descentBinomialPolynomial (n + 1) (descentNumber σ)).eval 1 * ((σ.sign : ℤ) : ℚ) =
          if σ = 1 then 1 else 0 := by
      rw [descentBinomialPolynomial_eval_one _ _ (by omega) (descentNumber_lt σ (by omega))]
      by_cases hσ : σ = 1
      · subst σ
        have hd : descentNumber (1 : Perm (Fin (n + 1))) = 0 :=
          (descentNumber_eq_zero_iff _).mpr rfl
        simp [hd]
      · have hd : descentNumber σ ≠ 0 := fun h => hσ ((descentNumber_eq_zero_iff σ).mp h)
        simp only [ite_eq_right hd, zero_mul, ite_eq_right hσ]
    unfold eulerianLambda
    simp_rw [hcoeff]
    simp only [apply_ite, MonoidAlgebra.single_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, MonoidAlgebra.one_def]

/-- The actual homogeneous coefficient elements sum to the original unit. -/
theorem sum_eulerianElement (n : ℕ) : (∑ i : Fin (n + 1), eulerianElement n i.val) = 1 := by
  simpa only [one_pow, one_smul] using (eulerianLambda_eq_sum n 1).symm.trans (eulerianLambda_one n)

end Equiv.Perm

namespace TensorPower

variable {k : Type u} [CommRing k] [Algebra ℚ k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- Evaluation at two in the actual coefficient representation is the actual full shuffle-cut operation. -/
theorem coefficientEulerianLambda_two_eq_shuffleCuts (n : ℕ) (hn : 0 < n) :
    coefficientRationalPermutationAction (M := M) (V := V) n (Equiv.Perm.eulerianLambda n 2) =
      TensorProduct.map (LinearMap.id : M →ₗ[k] M) (shuffleConvolutionTwo (k := k) (V := V) n) := by
  classical
  rw [Equiv.Perm.eulerianLambda, coefficientRationalPermutationAction_sum,
    coefficientPermutationOperator]
  congr 1
  rw [shuffleConvolutionTwo_eq_polynomial n hn]
  unfold permutationOperator
  apply Finset.sum_congr rfl
  intro σ _
  change algebraMap ℚ k
      ((Equiv.Perm.descentBinomialPolynomial n (Equiv.Perm.descentNumber σ)).eval 2 *
        ((σ.sign : ℤ) : ℚ)) • (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap =
    algebraMap ℚ k ((Equiv.Perm.descentBinomialPolynomial n (Equiv.Perm.descentNumber σ)).eval 2) •
      ((σ.sign : ℤ) • (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap)
  rw [map_mul, map_intCast, ← Int.cast_smul_eq_zsmul (R := k), smul_smul]

/-- The actual Eulerian evaluation has two unit cuts and exactly the proper cuts in positive degree. -/
theorem coefficientEulerianLambda_two_eq_properCuts (n : ℕ) (hn : 0 < n) :
    coefficientRationalPermutationAction (M := M) (V := V) n (Equiv.Perm.eulerianLambda n 2) =
      (2 : k) • (LinearMap.id : Module.End k (M ⊗[k] TensorPower k n V)) +
        TensorProduct.map (LinearMap.id : M →ₗ[k] M)
          (properShuffleConvolutionTwo (k := k) (V := V) n) := by
  rw [coefficientEulerianLambda_two_eq_shuffleCuts n hn,
    shuffleConvolutionTwo_eq_two_add_proper n hn, TensorProduct.map_add_right,
    TensorProduct.map_smul_right, TensorProduct.map_id]

end TensorPower
