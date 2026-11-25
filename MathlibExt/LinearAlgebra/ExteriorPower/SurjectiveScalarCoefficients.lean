/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Coefficient exterior powers under surjective scalar extension

For a surjective algebra map `R → S` and modules with compatible `S`-actions,
coefficient tensor exterior powers over `R` and `S` are equivalent. Exterior
base change, the tensor unitor for compatible scalar actions and coefficient
cancellation preserve both module carriers and their given actions.

The comparison includes degree zero and the empty exterior word. The rings
may be zero, and no flatness or finiteness assumption is required.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w z

namespace exteriorPower

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type w) (N : Type z) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module S M] [IsScalarTower R S M]
  [Module R N] [Module S N] [IsScalarTower R S N]

local instance coefficientScalarComm : SMulCommClass R S M where
  smul_comm r s m := by
    rw [← IsScalarTower.algebraMap_smul S r (s • m),
      ← IsScalarTower.algebraMap_smul S r m, smul_smul, smul_smul, mul_comm]

local instance exteriorScalarComm : SMulCommClass R S N where
  smul_comm r s n := by
    rw [← IsScalarTower.algebraMap_smul S r (s • n),
      ← IsScalarTower.algebraMap_smul S r n, smul_smul, smul_smul, mul_comm]

variable (h : Function.Surjective (algebraMap R S))

/-- Native scalar extension of an existing S-module, with its original action. -/
def surjectiveScalarModuleEquiv : S ⊗[R] N ≃ₗ[S] N := by
  letI : TensorProduct.CompatibleSMul R S S N :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := R) (A := S) (M := S) (N := N) h
  exact TensorProduct.lidOfCompatibleSMul R S N

/-- The original scalar-extension representative is evaluated by its actual S-action. -/
theorem surjectiveScalarModuleEquiv_tmul (s : S) (n : N) :
    surjectiveScalarModuleEquiv R S N h (s ⊗ₜ[R] n) = s • n := by
  let : TensorProduct.CompatibleSMul R S S N :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := R) (A := S) (M := S) (N := N) h
  exact TensorProduct.lidOfCompatibleSMul_tmul R S N s n

/-- Native exterior base change followed by the actual existing-module unitor. -/
def surjectiveScalarExteriorEquiv (q : ℕ) :
    S ⊗[R] (⋀[R]^q N) ≃ₗ[S] ⋀[S]^q N :=
  (baseChangeEquiv R S N q).trans
    (mapEquiv S (S ⊗[R] N) q (surjectiveScalarModuleEquiv R S N h))

/-- Every original exterior word maps to the same word with the actual S-scalars. -/
theorem surjectiveScalarExteriorEquiv_ιMulti (q : ℕ) (a : Fin q → N) :
    surjectiveScalarExteriorEquiv R S N h q
      ((1 : S) ⊗ₜ[R] ιMulti R q a) = ιMulti S q a := by
  rw [surjectiveScalarExteriorEquiv, LinearEquiv.trans_apply,
    baseChangeEquiv_apply_tmul_ιMulti, one_smul, mapEquiv_apply_ιMulti]
  congr 1
  funext i
  exact (surjectiveScalarModuleEquiv_tmul R S N h 1 (a i)).trans (one_smul _ _)

/-- The coefficient exterior comparison keeps both original carriers and
uses the actual scalar map. It also includes degree zero. -/
def surjectiveScalarCoefficientEquiv (q : ℕ) :
    M ⊗[R] (⋀[R]^q N) ≃ₗ[S] M ⊗[S] (⋀[S]^q N) :=
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M (⋀[R]^q N)).symm).trans
    (TensorProduct.congr (LinearEquiv.refl S M) (surjectiveScalarExteriorEquiv R S N h q))

/-- An original pure coefficient word has the same coefficient and the same original exterior factors. -/
theorem surjectiveScalarCoefficientEquiv_ιMulti (q : ℕ) (m : M) (a : Fin q → N) :
    surjectiveScalarCoefficientEquiv R S M N h q (m ⊗ₜ[R] ιMulti R q a) =
      m ⊗ₜ[S] ιMulti S q a := by
  change m ⊗ₜ[S] surjectiveScalarExteriorEquiv R S N h q
    ((1 : S) ⊗ₜ[R] ιMulti R q a) = _
  rw [surjectiveScalarExteriorEquiv_ιMulti]

/-- The actual inverse recovers every original pure coefficient word. -/
theorem surjectiveScalarCoefficientEquiv_symm_ιMulti (q : ℕ) (m : M) (a : Fin q → N) :
    (surjectiveScalarCoefficientEquiv R S M N h q).symm (m ⊗ₜ[S] ιMulti S q a) =
      m ⊗ₜ[R] ιMulti R q a := by
  apply (surjectiveScalarCoefficientEquiv R S M N h q).injective
  rw [LinearEquiv.apply_symm_apply, surjectiveScalarCoefficientEquiv_ιMulti]

section OriginalCoefficientScalar

variable (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
  [Module T M] [IsScalarTower R T M] [IsScalarTower S T M]

local instance coefficientTargetComm : SMulCommClass S T M where
  smul_comm s t m := by
    rw [← IsScalarTower.algebraMap_smul T s (t • m),
      ← IsScalarTower.algebraMap_smul T s m, smul_smul, smul_smul, mul_comm]

local instance coefficientBaseTargetComm : SMulCommClass R T M where
  smul_comm r t m := by
    rw [← IsScalarTower.algebraMap_smul T r (t • m),
      ← IsScalarTower.algebraMap_smul T r m, smul_smul, smul_smul, mul_comm]

/-- The same scalar comparison is linear for an additional original
coefficient action. Only the scalar towers on M are required; no scalar
tower R → S → T on the ring T itself is imposed. -/
def surjectiveScalarCoefficientEquivWithActor (q : ℕ) :
    M ⊗[R] (⋀[R]^q N) ≃ₗ[T] M ⊗[S] (⋀[S]^q N) :=
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T M (⋀[R]^q N)).symm).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T M)
      (surjectiveScalarExteriorEquiv R S N h q))

/-- The additional coefficient action retains the same actual pure-word formula. -/
theorem surjectiveScalarCoefficientEquivWithActor_ιMulti
    (q : ℕ) (m : M) (a : Fin q → N) :
    surjectiveScalarCoefficientEquivWithActor R S M N h T q
      (m ⊗ₜ[R] ιMulti R q a) = m ⊗ₜ[S] ιMulti S q a := by
  change m ⊗ₜ[S] surjectiveScalarExteriorEquiv R S N h q
    ((1 : S) ⊗ₜ[R] ιMulti R q a) = _
  rw [surjectiveScalarExteriorEquiv_ιMulti]

end OriginalCoefficientScalar

end exteriorPower
