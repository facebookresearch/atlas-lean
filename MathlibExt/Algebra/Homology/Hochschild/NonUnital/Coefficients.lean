/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Nonunital Hochschild coefficient actions

Left and right actions are nonunital algebra homomorphisms
from A and Aᵐᵒᵖ to ground-module endomorphisms. Commuting
representations define a bimodule. Unitization extends the
actions, while the tensor terms retain their factors in A.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable {k : Type u} [CommRing k]
  {A : Type v} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  {M : Type w} [AddCommGroup M] [Module k M]

section TensorActions

/-- The left coefficient action descends through the native tensor product. -/
def leftTensor (l : A →ₙₐ[k] Module.End k M) : A ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift (l : A →ₗ[k] Module.End k M)

/-- The right coefficient action descends through the native tensor product. -/
def rightTensor (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) : M ⊗[k] A →ₗ[k] M :=
  TensorProduct.lift
    (((r : Aᵐᵒᵖ →ₗ[k] Module.End k M).comp (MulOpposite.opLinearEquiv k).toLinearMap).flip)

omit [IsScalarTower k A A] [SMulCommClass k A A] in
@[simp]
theorem leftTensor_tmul (l : A →ₙₐ[k] Module.End k M) (a : A) (m : M) :
    leftTensor l (a ⊗ₜ[k] m) = l a m := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
@[simp]
theorem rightTensor_tmul (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) (m : M) (a : A) :
    rightTensor r (m ⊗ₜ[k] a) = r (MulOpposite.op a) m := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Associativity is supplied by the multiplication law of the representation. -/
theorem left_mul_apply (l : A →ₙₐ[k] Module.End k M) (a b : A) (m : M) :
    l (a * b) m = l a (l b m) := by
  rw [map_mul]
  rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The opposite multiplication gives the correct order for successive right actions. -/
theorem right_mul_apply (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) (a b : A) (m : M) :
    r (MulOpposite.op (a * b)) m = r (MulOpposite.op b) (r (MulOpposite.op a) m) := by
  rw [MulOpposite.op_mul, map_mul]
  rfl

/-- Regular right multiplication is a native nonunital representation. -/
def regularRight : Aᵐᵒᵖ →ₙₐ[k] Module.End k A :=
  (((MulOpposite.opLinearEquiv k).symm.conjAlgEquiv k).toAlgHom.toNonUnitalAlgHom).comp
    (NonUnitalAlgHom.lmul k Aᵐᵒᵖ)

@[simp]
theorem regularRight_apply (a b : A) : regularRight (k := k) (MulOpposite.op a) b = b * a :=
  rfl

/-- Native left multiplication and right multiplication commute without a unit. -/
theorem regular_commute (a b x : A) :
    NonUnitalAlgHom.lmul k A a (regularRight (k := k) (MulOpposite.op b) x) =
      regularRight (k := k) (MulOpposite.op b) (NonUnitalAlgHom.lmul k A a x) := by
  change a * (x * b) = (a * x) * b
  exact (mul_assoc a x b).symm

end TensorActions

section Unitization

/-- Extend the nonunital left representation by the native unitization property. -/
def unitizationLeft (l : A →ₙₐ[k] Module.End k M) :
    Unitization k A →ₐ[k] Module.End k M :=
  Unitization.lift l

@[simp]
theorem unitizationLeft_apply (l : A →ₙₐ[k] Module.End k M)
    (a : Unitization k A) (m : M) :
    unitizationLeft l a m = a.fst • m + l a.snd m := rfl

theorem unitizationLeft_inr (l : A →ₙₐ[k] Module.End k M) (a : A) (m : M) :
    unitizationLeft l (Unitization.inr a) m = l a m := by
  rw [unitizationLeft_apply, Unitization.fst_inr, Unitization.snd_inr, zero_smul, zero_add]

/-- The native algebra map from the opposite unitization to the unitization of the opposite
algebra. -/
def oppositeUnitization :
    (Unitization k A)ᵐᵒᵖ →ₐ[k] Unitization k Aᵐᵒᵖ where
  toFun a := Unitization.mk (a.unop.fst, MulOpposite.op a.unop.snd)
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := rfl
  map_mul' a b := by
    apply Unitization.ext
    · exact mul_comm _ _
    · simp only [MulOpposite.unop_mul, Unitization.snd_mul,
        MulOpposite.op_add, MulOpposite.op_smul, MulOpposite.op_mul]
      exact congrArg (fun q => q + MulOpposite.op a.unop.snd * MulOpposite.op b.unop.snd)
        (add_comm _ _)
  commutes' c := rfl

/-- The right representation extends to the opposite of the same native unitization. -/
def unitizationRight (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) :
    (Unitization k A)ᵐᵒᵖ →ₐ[k] Module.End k M :=
  (Unitization.lift r).comp oppositeUnitization

@[simp]
theorem unitizationRight_apply (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M)
    (a : (Unitization k A)ᵐᵒᵖ) (m : M) :
    unitizationRight r a m = a.unop.fst • m + r (MulOpposite.op a.unop.snd) m := rfl

theorem unitizationRight_inr (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) (a : A) (m : M) :
    unitizationRight r (MulOpposite.op (Unitization.inr a)) m =
      r (MulOpposite.op a) m := by
  rw [unitizationRight_apply, MulOpposite.unop_op, Unitization.fst_inr,
    Unitization.snd_inr, zero_smul, zero_add]

/-- Commuting nonunital actions extend to commuting actions of the unitization. -/
theorem unitization_commute (l : A →ₙₐ[k] Module.End k M)
    (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M)
    (h : ∀ a b m, l a (r b m) = r b (l a m))
    (a : Unitization k A) (b : (Unitization k A)ᵐᵒᵖ) (m : M) :
    unitizationLeft l a (unitizationRight r b m) =
      unitizationRight r b (unitizationLeft l a m) := by
  simp only [unitizationLeft_apply, unitizationRight_apply, smul_add,
    (l a.snd).map_add, (r (MulOpposite.op b.unop.snd)).map_add,
    (l a.snd).map_smul, (r (MulOpposite.op b.unop.snd)).map_smul, h]
  rw [smul_smul, smul_smul, mul_comm a.fst b.unop.fst]
  abel

end Unitization

end ModuleCat.Algebra.Hochschild.NonUnital
