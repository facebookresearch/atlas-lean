/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.GeneralizedTrace
public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Coefficients
public import MathlibExt.Algebra.Homology.Hochschild.Maps
public import Mathlib.Data.Matrix.Basis

/-!
# Nonunital corner maps on Hochschild chains

The matrix corner is multiplicative and intertwines
both coefficient actions. It induces the corresponding
Hochschild face and boundary maps and their chain map
in a common carrier universe, without unit preservation.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct

namespace ModuleCat.Algebra.Hochschild.Matrix

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

universe u v w z

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

/-- The corner algebra map. It is nonunital for matrix size larger than one. -/
def cornerAlgHom (b : ι) : A →ₙₐ[k] Matrix ι ι A where
  toFun := cornerLinear k ι b
  map_zero' := (cornerLinear k ι b).map_zero
  map_add' := (cornerLinear k ι b).map_add
  map_mul' a a' := by
    have h (x : A) : cornerLinear k ι b x = Matrix.single b b x := by
      ext i j
      simp only [cornerLinear_apply, Matrix.single_apply, (eq_comm : b = i ↔ i = b),
        (eq_comm : b = j ↔ j = b), ite_and]
      split_ifs <;> rfl
    rw [h, h, h]
    exact (Matrix.single_mul_single_same a b b b a').symm
  map_smul' := (cornerLinear k ι b).map_smul

@[simp]
theorem cornerAlgHom_apply (b : ι) (a : A) :
    cornerAlgHom k A ι b a = cornerLinear k ι b a := rfl

-- Capture the given pointwise k-module before installing either matrix action.
/-- The original pointwise ground module, captured before the matrix algebra actions. -/
local instance groundMatrixModule : Module k (Matrix ι ι M) := inferInstance
/-- The native left matrix-algebra action on the original coefficient matrix. -/
local instance cornerActorLeftModule : Module (Matrix ι ι A) (Matrix ι ι M) :=
  Coefficients.leftModule A M ι
/-- The native right matrix-algebra action, with the original coefficient carrier. -/
local instance cornerActorRightModule : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.rightModule A M ι
local instance : SMulCommClass (Matrix ι ι A) (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.commute A M ι
local instance : IsScalarTower k (Matrix ι ι A) (Matrix ι ι M) :=
  Coefficients.leftTower A M ι k
local instance : IsScalarTower k (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.rightTower A M ι k

omit [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M]
  [IsScalarTower k Aᵐᵒᵖ M] in
/-- The corner intertwines the left actions. -/
theorem corner_left (b : ι) (a : A) (m : M) :
    cornerLinear k ι b (a • m) = cornerAlgHom k A ι b a • cornerLinear k ι b m := by
  ext i j
  rw [Coefficients.left_smul_apply]
  by_cases hi : i = b <;> by_cases hj : j = b <;>
    simp [cornerAlgHom_apply, cornerLinear_apply, hi, hj]

omit [Module A M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M]
  [IsScalarTower k Aᵐᵒᵖ M] in
/-- The corner intertwines the right actions. -/
theorem corner_right (b : ι) (a : A) (m : M) :
    cornerLinear k ι b (MulOpposite.op a • m) =
      MulOpposite.op (cornerAlgHom k A ι b a) • cornerLinear k ι b m := by
  ext i j
  rw [Coefficients.right_smul_apply]
  by_cases hi : i = b <;> by_cases hj : j = b <;>
    simp [cornerAlgHom_apply, cornerLinear_apply, hi, hj, apply_ite]

omit [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M]
  [IsScalarTower k Aᵐᵒᵖ M] in
/-- The corner chain map has the coefficient tensor-map components. -/
theorem corner_linearMap (b : ι) (n : ℕ) :
    ModuleCat.Algebra.Hochschild.linearMap (cornerAlgHom k A ι b)
      (cornerLinear k ι b : M →ₗ[k] Matrix ι ι M) n = cornerTensor k ι b n := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [ModuleCat.Algebra.Hochschild.linearMap_tprod, cornerTensor_tmul_tprod,
    cornerAlgHom_apply]

/-- Every native corner face square is by algebra/action laws. -/
theorem corner_face_comm (b : ι) (n : ℕ) (i : Fin (n + 2)) :
    (Coefficients.face A M ι k n i).hom.comp (cornerTensor k ι b (n + 1)) =
      (cornerTensor k ι b n).comp (ModuleCat.Algebra.Hochschild.face k A M n i).hom := by
  have h := ModuleCat.Algebra.Hochschild.linearMap_face_comm
    (k := k) (A := A) (B := Matrix ι ι A) (M := M) (N := Matrix ι ι M)
    (cornerAlgHom k A ι b) (cornerLinear k ι b : M →ₗ[k] Matrix ι ι M)
    (corner_left k A M ι b) (corner_right k A M ι b) n i
  simpa only [corner_linearMap, Coefficients.face] using h

/-- The corner chain map in the native canonical common universe. -/
def cornerChainMap (b : ι) :
    ModuleCat.Algebra.Hochschild.chainComplex k A (ULift.{max u v w z} M) ⟶
      ModuleCat.Algebra.Hochschild.chainComplex k (Matrix ι ι A)
        (ULift.{max u v w z} (Matrix ι ι M)) :=
  ModuleCat.Algebra.Hochschild.liftedMap
    (cornerAlgHom k A ι b) (cornerLinear k ι b)
    (corner_left k A M ι b) (corner_right k A M ι b)

/-- The native common-universe chain map retains the corner's generator values. -/
theorem cornerChainMap_f_tprod (b : ι) (n : ℕ) (m : M) (a : Fin n → A) :
    ((cornerChainMap k A M ι b).f n).hom
      (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (cornerLinear k ι b m) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => cornerLinear k ι b (a j)) := by
  simpa only [cornerChainMap, cornerAlgHom_apply] using
    (ModuleCat.Algebra.Hochschild.liftedMap_f_tprod
      (cornerAlgHom k A ι b) (cornerLinear k ι b)
      (corner_left k A M ι b) (corner_right k A M ι b) n m a)

end ModuleCat.Algebra.Hochschild.Matrix
