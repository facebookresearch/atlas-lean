/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_QuaternionAlgebra_BaseChange.lean`,
`Definitions/Def_QuaternionAlgebra_EichlerOrder.lean`
and
`Definitions/Def_QuaternionAlgebra_Order.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open scoped TensorProduct Quaternion

noncomputable section

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable {c₁ c₂ c₃ : R} {d₁ d₂ d₃ : S}

/-- The standard quaternion basis transported along `algebraMap R S`. -/
def Basis.ofAlgebraMapEq (h₁ : algebraMap R S c₁ = d₁)
    (h₂ : algebraMap R S c₂ = d₂) (h₃ : algebraMap R S c₃ = d₃) :
    QuaternionAlgebra.Basis (R := R) ℍ[S, d₁, d₂, d₃] c₁ c₂ c₃ where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by
    rw [← algebraMap_smul S c₁, ← algebraMap_smul S c₂, h₁, h₂]
    ext <;> simp
  j_mul_j := by
    rw [← algebraMap_smul S c₃, h₃]
    ext <;> simp
  i_mul_j := by ext <;> simp
  j_mul_i := by
    rw [← algebraMap_smul S c₂, h₂]
    ext <;> simp

variable (h₁ : algebraMap R S c₁ = d₁) (h₂ : algebraMap R S c₂ = d₂)
  (h₃ : algebraMap R S c₃ = d₃)

/-- The algebra map between quaternion algebras induced by `algebraMap`. -/
def mapOfAlgebraMapEq : ℍ[R, c₁, c₂, c₃] →ₐ[R] ℍ[S, d₁, d₂, d₃] :=
  (Basis.ofAlgebraMapEq h₁ h₂ h₃).liftHom

@[simp] theorem mapOfAlgebraMapEq_apply (x : ℍ[R, c₁, c₂, c₃]) :
    mapOfAlgebraMapEq h₁ h₂ h₃ x =
      ⟨algebraMap R S x.re, algebraMap R S x.imI, algebraMap R S x.imJ,
        algebraMap R S x.imK⟩ := by
  rw [mapOfAlgebraMapEq, Basis.liftHom_apply]
  unfold Basis.lift
  rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul S x.re,
    ← algebraMap_smul S x.imI, ← algebraMap_smul S x.imJ,
    ← algebraMap_smul S x.imK]
  ext <;> simp [Basis.ofAlgebraMapEq] <;> simp [Algebra.smul_def]

/-- The base-change algebra map `S ⊗ ℍ[R] →ₐ[S] ℍ[S]`. -/
def baseChangeHom : S ⊗[R] ℍ[R, c₁, c₂, c₃] →ₐ[S] ℍ[S, d₁, d₂, d₃] :=
  (mapOfAlgebraMapEq h₁ h₂ h₃).liftEquiv R S _ _

theorem baseChangeHom_tmul (s : S) (x : ℍ[R, c₁, c₂, c₃]) :
    baseChangeHom h₁ h₂ h₃ (s ⊗ₜ[R] x) =
      ⟨s * algebraMap R S x.re, s * algebraMap R S x.imI,
        s * algebraMap R S x.imJ, s * algebraMap R S x.imK⟩ := by
  rw [baseChangeHom, AlgHom.liftEquiv_tmul, mapOfAlgebraMapEq_apply]
  ext <;> simp

/-- The inverse of `baseChangeHom` on coordinates. -/
def baseChangeInv (q : ℍ[S, d₁, d₂, d₃]) : S ⊗[R] ℍ[R, c₁, c₂, c₃] :=
  q.re ⊗ₜ[R] (1 : ℍ[R, c₁, c₂, c₃]) +
    q.imI ⊗ₜ[R] (⟨0, 1, 0, 0⟩ : ℍ[R, c₁, c₂, c₃]) +
    q.imJ ⊗ₜ[R] (⟨0, 0, 1, 0⟩ : ℍ[R, c₁, c₂, c₃]) +
    q.imK ⊗ₜ[R] (⟨0, 0, 0, 1⟩ : ℍ[R, c₁, c₂, c₃])

theorem baseChangeInv_add (q q' : ℍ[S, d₁, d₂, d₃]) :
    (baseChangeInv (q + q') : S ⊗[R] ℍ[R, c₁, c₂, c₃]) =
      baseChangeInv q + baseChangeInv q' := by
  simp only [baseChangeInv]
  rw [show (q + q').re = q.re + q'.re from rfl,
    show (q + q').imI = q.imI + q'.imI from rfl,
    show (q + q').imJ = q.imJ + q'.imJ from rfl,
    show (q + q').imK = q.imK + q'.imK from rfl]
  simp only [TensorProduct.add_tmul]
  abel

theorem baseChangeHom_baseChangeInv (q : ℍ[S, d₁, d₂, d₃]) :
    baseChangeHom h₁ h₂ h₃ (baseChangeInv q) = q := by
  simp only [baseChangeInv, map_add, baseChangeHom_tmul]
  ext <;> simp

theorem baseChangeInv_baseChangeHom (x : S ⊗[R] ℍ[R, c₁, c₂, c₃]) :
    baseChangeInv (baseChangeHom h₁ h₂ h₃ x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s y =>
      have aux : ∀ (r : R) (e : ℍ[R, c₁, c₂, c₃]),
          (s * algebraMap R S r) ⊗ₜ[R] e = s ⊗ₜ[R] (r • e) := by
        intro r e
        rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
      rw [baseChangeHom_tmul]
      simp only [baseChangeInv, aux, ← TensorProduct.tmul_add]
      congr 1
      ext <;> simp
  | add x y hx hy => rw [map_add, baseChangeInv_add, hx, hy]

/-- Base change of a quaternion algebra. -/
def baseChange : S ⊗[R] ℍ[R, c₁, c₂, c₃] ≃ₐ[S] ℍ[S, d₁, d₂, d₃] :=
  AlgEquiv.ofBijective (baseChangeHom h₁ h₂ h₃)
    ⟨Function.LeftInverse.injective (g := baseChangeInv)
        (baseChangeInv_baseChangeHom h₁ h₂ h₃),
      Function.RightInverse.surjective (g := baseChangeInv)
        (baseChangeHom_baseChangeInv h₁ h₂ h₃)⟩

theorem baseChange_apply (x : S ⊗[R] ℍ[R, c₁, c₂, c₃]) :
    baseChange h₁ h₂ h₃ x = baseChangeHom h₁ h₂ h₃ x :=
  rfl

@[simp] theorem baseChange_tmul (s : S) (x : ℍ[R, c₁, c₂, c₃]) :
    baseChange h₁ h₂ h₃ (s ⊗ₜ[R] x) =
      ⟨s * algebraMap R S x.re, s * algebraMap R S x.imI,
        s * algebraMap R S x.imJ, s * algebraMap R S x.imK⟩ :=
  baseChangeHom_tmul h₁ h₂ h₃ s x

theorem baseChange_symm_apply (q : ℍ[S, d₁, d₂, d₃]) :
    (baseChange h₁ h₂ h₃).symm q = baseChangeInv q :=
  (baseChange h₁ h₂ h₃).injective (by
    rw [AlgEquiv.apply_symm_apply, baseChange_apply,
      baseChangeHom_baseChangeInv])

/-- Right-handed base change. -/
def baseChangeRight : ℍ[R, c₁, c₂, c₃] ⊗[R] S ≃ₐ[R] ℍ[S, d₁, d₂, d₃] :=
  (Algebra.TensorProduct.comm R ℍ[R, c₁, c₂, c₃] S).trans
    ((baseChange h₁ h₂ h₃).restrictScalars R)

@[simp] theorem baseChangeRight_tmul (x : ℍ[R, c₁, c₂, c₃]) (s : S) :
    baseChangeRight h₁ h₂ h₃ (x ⊗ₜ[R] s) =
      ⟨s * algebraMap R S x.re, s * algebraMap R S x.imI,
        s * algebraMap R S x.imJ, s * algebraMap R S x.imK⟩ := by
  rw [baseChangeRight, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    AlgEquiv.restrictScalars_apply, baseChange_tmul]

theorem baseChangeRight_one_tmul (s : S) :
    baseChangeRight h₁ h₂ h₃ ((1 : ℍ[R, c₁, c₂, c₃]) ⊗ₜ[R] s) =
      algebraMap S ℍ[S, d₁, d₂, d₃] s := by
  rw [baseChangeRight_tmul, Algebra.algebraMap_eq_smul_one]
  ext <;> simp

theorem baseChangeRight_tmul_one (x : ℍ[R, c₁, c₂, c₃]) :
    baseChangeRight h₁ h₂ h₃ (x ⊗ₜ[R] (1 : S)) =
      ⟨algebraMap R S x.re, algebraMap R S x.imI, algebraMap R S x.imJ,
        algebraMap R S x.imK⟩ := by
  rw [baseChangeRight_tmul]
  ext <;> simp

theorem baseChangeRight_symm_apply (q : ℍ[S, d₁, d₂, d₃]) :
    (baseChangeRight h₁ h₂ h₃).symm q =
      (1 : ℍ[R, c₁, c₂, c₃]) ⊗ₜ[R] q.re +
        (⟨0, 1, 0, 0⟩ : ℍ[R, c₁, c₂, c₃]) ⊗ₜ[R] q.imI +
        (⟨0, 0, 1, 0⟩ : ℍ[R, c₁, c₂, c₃]) ⊗ₜ[R] q.imJ +
        (⟨0, 0, 0, 1⟩ : ℍ[R, c₁, c₂, c₃]) ⊗ₜ[R] q.imK := by
  apply (baseChangeRight h₁ h₂ h₃).injective
  rw [AlgEquiv.apply_symm_apply]
  simp only [map_add, baseChangeRight_tmul]
  ext <;> simp

end QuaternionAlgebra

end
