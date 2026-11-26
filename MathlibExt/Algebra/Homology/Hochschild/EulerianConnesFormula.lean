/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.NormalizedConnesFormula
public import MathlibExt.Algebra.Homology.Hochschild.NormalizedEulerianOperators
public import MathlibExt.LinearAlgebra.TensorPower.EulerianCyclicNormActions

/-!
# The scalar-two Connes convolution square

Let k be a commutative ℚ-algebra and A a commutative unital k-algebra.
The regular normalized chain module is N_n=A⊗[k](A/span_k{1})^{⊗n}.
Let B_n:N_n→N_{n+1} be normalized Connes boundary and Λ_n(2)
the coefficient-fixed bar-lambda convolution evaluated at two.

In every degree, including n=0, these maps satisfy
Λ_{n+1}(2) B_n = 2 B_n Λ_n(2).
The normalized B first places the coefficient in the quotient tail,
takes its signed cyclic norm, and inserts the unit as the new coefficient.

References: J.-L. Loday, Cyclic Homology, §§2.1 and 4.5.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]

local notation "Q" => ModuleCat.Algebra.Hochschild.quotientCarrier k A
local notation "q" => Submodule.mkQ (ModuleCat.Algebra.Hochschild.unitSubmodule k A)

/-- Let k be a commutative ℚ-algebra and A a commutative unital
k-algebra. Set Ā=A/span_k{1} and N_n(A)=A⊗[k]Ā^{⊗n}.
For normalized Connes B_n:N_n→N_{n+1} and the bar-lambda
convolution Λ_n(2), the all-degree square is
Λ_{n+1}(2)B_n=2B_nΛ_n(2). -/
theorem normalizedConvolutionTwo_connesBoundary (n : ℕ) :
    (normalizedConvolutionOperator k A A (n + 1) 2).comp (NonUnital.normalizedBoundary k A n).hom =
      (2 : k) • (NonUnital.normalizedBoundary k A n).hom.comp
        (normalizedConvolutionOperator k A A n 2) := by
  rw [normalizedConnesBoundary_eq_formula]
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  change normalizedConvolutionOperator k A A (n + 1) 2
      (normalizedConnesFormula k A n (m ⊗ₜ[k] x)) =
    (2 : k) • normalizedConnesFormula k A n
      (normalizedConvolutionOperator k A A n 2 (m ⊗ₜ[k] x))
  simp only [normalizedConvolutionOperator, TensorPower.coefficientRationalPermutationAction_eq_map,
    normalizedConnesFormula, LinearMap.comp_apply, LinearMap.smul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  have h := DFunLike.congr_fun
    (TensorPower.rationalEulerianLambda_two_cyclicNorm (k := k) (V := Q) n)
      (TensorPower.consEquiv k Q n (q m ⊗ₜ[k] x))
  simp only [LinearMap.smul_apply, LinearMap.comp_apply] at h
  have hh := DFunLike.congr_fun
    (TensorPower.rationalPermutationAction_headFixing_cons (k := k) (V := Q) n
      (Equiv.Perm.eulerianLambda n 2)) (q m ⊗ₜ[k] x)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply] at hh
  change TensorPower.rationalPermutationAction (k := k) (V := Q) (n + 1)
      (Equiv.Perm.headFixingGroupRingMap ℚ n (Equiv.Perm.eulerianLambda n 2))
      (TensorPower.consEquiv k Q n (q m ⊗ₜ[k] x)) =
    TensorPower.consEquiv k Q n (q m ⊗ₜ[k]
      TensorPower.rationalPermutationAction (k := k) (V := Q) n (Equiv.Perm.eulerianLambda n 2) x) at hh
  change TensorProduct.map LinearMap.id
      (TensorPower.rationalPermutationAction (k := k) (V := Q) (n + 1)
        (Equiv.Perm.eulerianLambda (n + 1) 2))
      ((1 : A) ⊗ₜ[k] TensorPower.norm k Q n (TensorPower.consEquiv k Q n (q m ⊗ₜ[k] x))) =
    (2 : k) • ((1 : A) ⊗ₜ[k] TensorPower.norm k Q n
      (TensorPower.consEquiv k Q n (q m ⊗ₜ[k]
        TensorPower.rationalPermutationAction (k := k) (V := Q) n (Equiv.Perm.eulerianLambda n 2) x)))
  rw [TensorProduct.map_tmul, LinearMap.id_apply, h, hh]
  exact map_smul (TensorProduct.mk k A (TensorPower k (n + 1) Q) 1) (2 : k) _

end ModuleCat.Algebra.Hochschild.Symmetric
