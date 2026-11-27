/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange
public import MathlibExt.LinearAlgebra.ExteriorPower.Contraction

/-!
# Base change for exterior contraction

Contraction by a functional commutes with scalar extension. The scalar
extended functional is Mathlib's canonical `Module.Dual.baseChange`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace exteriorPower

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- Exterior contraction commutes with extension of scalars. -/
theorem contractLeft_baseChange (x : Module.Dual R M) (n : ℕ) :
    (contractLeft S (S ⊗[R] M) (x.baseChange S) n).comp
        (baseChangeMap R S M (n + 1)) =
      (baseChangeMap R S M n).comp
        ((contractLeft R M x n).baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
    (R := R) (n := n + 1) (M := M)
      (N := ⋀[S]^n (S ⊗[R] M))
  apply AlternatingMap.ext
  intro a
  change contractLeft S (S ⊗[R] M) (x.baseChange S) n
      (baseChangeMap R S M (n + 1)
        (s ⊗ₜ[R] ιMulti R (n + 1) a)) =
    baseChangeMap R S M n
      (((contractLeft R M x n).baseChange S)
        (s ⊗ₜ[R] ιMulti R (n + 1) a))
  rw [baseChangeMap_apply_tmul_ιMulti, map_smul,
    contractLeft_apply_ιMulti]
  simp only [Module.Dual.baseChange_apply_tmul, LinearMap.baseChange_tmul,
    contractLeft_apply_ιMulti, map_sum, TensorProduct.tmul_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hbalance :
      s ⊗ₜ[R] (((-1 : R) ^ i.val) •
        (x (a i) • ιMulti R n (a ∘ i.succAbove))) =
      (algebraMap R S (((-1 : R) ^ i.val) * x (a i)) * s) ⊗ₜ[R]
        ιMulti R n (a ∘ i.succAbove) := by
    rw [smul_smul, TensorProduct.tmul_smul]
    rw [← IsScalarTower.algebraMap_smul S
      (((-1 : R) ^ i.val) * x (a i))]
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  rw [hbalance, baseChangeMap_apply_tmul_ιMulti]
  simp only [Algebra.smul_def, mul_one, smul_smul, Function.comp_apply,
    map_mul, map_pow, map_neg, map_one]
  congr 1
  ring

end exteriorPower
