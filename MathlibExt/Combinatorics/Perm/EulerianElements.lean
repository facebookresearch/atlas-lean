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
# Eulerian coefficients and the convolution family

For `σ ∈ S_n`, write `d(σ)` for its ordinary descent count and `P_(n,d)(X) = (1/n!)
∏_(j=0)^(n-1)(X+j-d)`. The Eulerian element `ε_(n,i)` has coefficient `coeff_i(P_(n,d(σ))) *
sign(σ)` at `σ`. Its evaluation family is `Λ_n(t) = ∑_(i=0)^n t^i ε_(n,i)` in `ℚ[S_n]`.

The elements sum to the unit, and the top element is the antisymmetrizer divided by `n!`.
Degree zero has only `ε_(0,0)=1`; positive degrees have zero constant weight. Under the
coefficient tensor representation, `Λ_n(2)` is the full signed shuffle-cut sum, including the
two unit cuts when `n>0`.

The positive-integer lambda element additionally multiplies this convolution by `(-1)^(m-1)`
at parameter `m`. The rational family `Λ_n(t)` uses only its displayed polynomial evaluation.

Reference: Loday, *Cyclic Homology*, Section 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators TensorProduct

universe u v w

namespace Equiv.Perm

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. For `i : ℕ` and `σ ∈ S_n`,
`eulerianCoefficient n i σ = coeff_i(P_(n,d(σ))) * sign(σ)` in `ℚ`, with the sign coerced from
`ℤˣ` through `ℤ`. -/
def eulerianCoefficient (n i : ℕ) (σ : Perm (Fin n)) : ℚ :=
  (descentBinomialPolynomial n (descentNumber σ)).coeff i * ((σ.sign : ℤ) : ℚ)

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. For `i : ℕ`, `eulerianElement
n i` is `∑ σ ∈ S_n, coeff_i(P_(n,d(σ))) * sign(σ) [σ]` in `ℚ[S_n]`. -/
def eulerianElement (n i : ℕ) : MonoidAlgebra ℚ (Perm (Fin n)) :=
  ∑ σ : Perm (Fin n), MonoidAlgebra.single σ (eulerianCoefficient n i σ)

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. For `t : ℚ`, `eulerianLambda n
t = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in `ℚ[S_n]`. -/
def eulerianLambda (n : ℕ) (t : ℚ) : MonoidAlgebra ℚ (Perm (Fin n)) :=
  ∑ σ : Perm (Fin n), MonoidAlgebra.single σ
    ((descentBinomialPolynomial n (descentNumber σ)).eval t * ((σ.sign : ℤ) : ℚ))

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. For `t : ℚ`, `Λ_n(t) = ∑ i : Fin(n+1), t^i.val • ε_(n,i.val)`. -/
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

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. For `σ ∈ S_n`,
`eulerianCoefficient n n σ = (n!:ℚ)⁻¹ * sign(σ)`. -/
theorem eulerianCoefficient_top (n : ℕ) (σ : Perm (Fin n)) :
    eulerianCoefficient n n σ = (Nat.factorial n : ℚ)⁻¹ * ((σ.sign : ℤ) : ℚ) := by
  rw [eulerianCoefficient, descentBinomialPolynomial_coeff_degree]

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. `ε_(n,n) = (n!:ℚ)⁻¹ • ∑ σ ∈ S_n, sign(σ) [σ]`, including `n=0`. -/
theorem eulerianElement_top (n : ℕ) :
    eulerianElement n n = (Nat.factorial n : ℚ)⁻¹ •
      (∑ σ : Perm (Fin n), MonoidAlgebra.single σ ((σ.sign : ℤ) : ℚ)) := by
  classical
  unfold eulerianElement
  rw [Finset.smul_sum]
  simp_rw [eulerianCoefficient_top, MonoidAlgebra.smul_single, smul_eq_mul]

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. For `i : ℕ`, `σ ∈ S_n`, and
`n<i`, `eulerianCoefficient n i σ = 0`. -/
theorem eulerianCoefficient_outside (n i : ℕ) (σ : Perm (Fin n)) (hi : n < i) :
    eulerianCoefficient n i σ = 0 := by
  rw [eulerianCoefficient,
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((descentBinomialPolynomial_natDegree_le n (descentNumber σ)).trans_lt hi), zero_mul]

/-- For `i : ℕ` and `σ ∈ S_0`, `eulerianCoefficient 0 i σ = if i=0 then 1 else 0`. The empty-word
polynomial is the constant `1`. -/
theorem eulerianCoefficient_degree_zero (i : ℕ) (σ : Perm (Fin 0)) :
    eulerianCoefficient 0 i σ = if i = 0 then 1 else 0 := by
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst σ
  simp [eulerianCoefficient, descentBinomialPolynomial, Polynomial.coeff_one]

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. If `0<n`, then for every `σ ∈
S_n`, `eulerianCoefficient n 0 σ = 0`. -/
theorem eulerianCoefficient_zero_weight (n : ℕ) (σ : Perm (Fin n)) (hn : 0 < n) :
    eulerianCoefficient n 0 σ = 0 := by
  rw [eulerianCoefficient, descentBinomialPolynomial_coeff_zero n (descentNumber σ)
    hn (descentNumber_lt σ hn), zero_mul]

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. For every `n : ℕ`, `Λ_n(1) = 1` in `ℚ[S_n]`. -/
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

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. `∑ i : Fin(n+1), ε_(n,i.val) = 1` in `ℚ[S_n]`. -/
theorem sum_eulerianElement (n : ℕ) : (∑ i : Fin (n + 1), eulerianElement n i.val) = 1 := by
  simpa only [one_pow, one_smul] using (eulerianLambda_eq_sum n 1).symm.trans (eulerianLambda_one n)

end Equiv.Perm

namespace TensorPower

variable {k : Type u} [CommRing k] [Algebra ℚ k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- Let `k` be a commutative `ℚ`-algebra, `M,V` be `k`-modules, and `0<n`. Let `A_n : ℚ[S_n] →
End_k(M ⊗[k] TensorPower k n V)` be `coefficientRationalPermutationAction`, fixing the
coefficient factor and permuting the tensor factors. Then `A_n(eulerianLambda n 2) = id_M ⊗
shuffleConvolutionTwo n`, where the latter operator sums every cut of the tensor word followed
by the corresponding signed shuffle product. -/
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

/-- Let `k` be a commutative `ℚ`-algebra, `M,V` be `k`-modules, and `0<n`. Let `A_n : ℚ[S_n] →
End_k(M ⊗[k] TensorPower k n V)` be `coefficientRationalPermutationAction`, fixing the
coefficient factor and permuting the tensor factors. The coefficient action satisfies
`A_n(eulerianLambda n 2) = 2 • id + id_M ⊗ properShuffleConvolutionTwo n`. The proper sum uses
cuts with both factor lengths positive; the two endpoint cuts contribute the two identity
terms. -/
theorem coefficientEulerianLambda_two_eq_properCuts (n : ℕ) (hn : 0 < n) :
    coefficientRationalPermutationAction (M := M) (V := V) n (Equiv.Perm.eulerianLambda n 2) =
      (2 : k) • (LinearMap.id : Module.End k (M ⊗[k] TensorPower k n V)) +
        TensorProduct.map (LinearMap.id : M →ₗ[k] M)
          (properShuffleConvolutionTwo (k := k) (V := V) n) := by
  rw [coefficientEulerianLambda_two_eq_shuffleCuts n hn,
    shuffleConvolutionTwo_eq_two_add_proper n hn, TensorProduct.map_add_right,
    TensorProduct.map_smul_right, TensorProduct.map_id]

end TensorPower
