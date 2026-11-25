/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Opposite
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# Induction along associative ring homomorphisms

The induced module is the integer-balanced quotient with right scalar action `r • a = r * φ a`.
The regular left action descends to the quotient, and pure-tensor maps determine morphisms of
induced modules.
-/

@[expose] public section

open MulOpposite

universe u v w z t

namespace ModuleCat.RingHomInduction

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)

/-- The regular right `k`-action is restriction of the regular opposite action. -/
@[instance_reducible]
def rightModule : Module kᵐᵒᵖ R := Module.compHom R φ.op

theorem rightModule_smul (a : k) (r : R) :
    letI := rightModule φ
    op a • r = r * φ a := rfl

/-- The regular left action commutes with the restricted right action. -/
theorem rightComm :
    letI := rightModule φ
    SMulCommClass R kᵐᵒᵖ R := by
  let := rightModule φ
  refine ⟨?_⟩
  intro r a x
  change r * (x * φ a.unop) = (r * x) * φ a.unop
  exact (mul_assoc r x (φ a.unop)).symm

variable (M : Type w) [AddCommGroup M] [Module k M]

/-- The balanced integer tensor, with the right action stored in its type. -/
abbrev Carrier : Type (max v w) :=
  letI := rightModule φ
  TensorProduct.Balanced ℤ k R M

/-- The regular left `R`-action descends through the balancing quotient. -/
@[instance_reducible]
def outerModule : Module R (Carrier φ M) := by
  letI := rightModule φ
  letI : SMulCommClass R ℤ R := AddGroup.int_smulCommClass'
  letI := rightComm φ
  exact TensorProduct.Balanced.leftModule ℤ k R R M

instance instModule : Module R (Carrier φ M) := outerModule φ M

/-- The pure balanced tensor. -/
def tensor (r : R) (m : M) : Carrier φ M :=
  letI := rightModule φ
  TensorProduct.Balanced.mk ℤ k R M r m

theorem tensor_add_left (r s : R) (m : M) :
    tensor φ M (r + s) m = tensor φ M r m + tensor φ M s m := by
  let := rightModule φ
  exact LinearMap.congr_fun ((TensorProduct.Balanced.mk ℤ k R M).map_add r s) m

theorem tensor_add_right (r : R) (m n : M) :
    tensor φ M r (m + n) = tensor φ M r m + tensor φ M r n := by
  let := rightModule φ
  exact (TensorProduct.Balanced.mk ℤ k R M r).map_add m n

theorem tensor_zero_left (m : M) : tensor φ M 0 m = 0 := by
  let := rightModule φ
  change TensorProduct.Balanced.mk ℤ k R M 0 m = 0
  rw [map_zero, LinearMap.zero_apply]

theorem tensor_zero_right (r : R) : tensor φ M r 0 = 0 := by
  let := rightModule φ
  exact (TensorProduct.Balanced.mk ℤ k R M r).map_zero

/-- The computed outer action retains the order of multiplication in `R`. -/
theorem smul_tensor (s r : R) (m : M) :
    s • tensor φ M r m = tensor φ M (s * r) m := by
  let := rightModule φ
  let : SMulCommClass R ℤ R := AddGroup.int_smulCommClass'
  let := rightComm φ
  exact TensorProduct.Balanced.leftModule_smul_mk ℤ k R R M s r m

/-- The `k`-scalar moves across the balancing quotient. -/
theorem tensor_balance (a : k) (r : R) (m : M) :
    tensor φ M (r * φ a) m = tensor φ M r (a • m) := by
  let := rightModule φ
  exact TensorProduct.Balanced.balance ℤ k R M a r m

/-- Insertion of the unit is semilinear along the ring homomorphism. -/
theorem tensor_one_smul (a : k) (m : M) :
    tensor φ M 1 (a • m) = φ a • tensor φ M 1 m := by
  calc
    tensor φ M 1 (a • m) = tensor φ M (φ a) m := by
      simpa only [one_mul] using (tensor_balance φ M a 1 m).symm
    _ = φ a • tensor φ M 1 m := by
      simpa only [mul_one] using (smul_tensor φ M (φ a) 1 m).symm

/-- Pure balanced tensors determine an `R`-linear map into any module. -/
theorem hom_ext {N : Type z} [AddCommGroup N] [Module R N]
    {f g : Carrier φ M →ₗ[R] N}
    (h : ∀ (r : R) (m : M), f (tensor φ M r m) = g (tensor φ M r m)) :
    f = g := by
  let := rightModule φ
  have ha : f.toAddMonoidHom = g.toAddMonoidHom :=
    TensorProduct.Balanced.addHom_ext ℤ k R M h
  apply LinearMap.ext
  intro x
  exact congrArg (fun q : Carrier φ M →+ N => q x) ha

/-- An coefficient module is induced into its constructed maximum carrier universe. -/
def moduleObj (M : ModuleCat.{w} k) : ModuleCat.{max v w} R :=
  ModuleCat.of R (Carrier φ M)

section Maps

variable {M : Type w} {N : Type z}
  [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]

/-- An module morphism induces the equivariant balanced quotient map. -/
def map (f : M →ₗ[k] N) : Carrier φ M →ₗ[R] Carrier φ N := by
  letI := rightModule φ
  letI : SMulCommClass R ℤ R := AddGroup.int_smulCommClass'
  letI := rightComm φ
  exact TensorProduct.Balanced.mapLeft
    (k := ℤ) (R := k) (S := R)
    (LinearMap.id : R →ₗ[ℤ] R) f.toAddMonoidHom.toIntLinearMap
    (fun _ _ => rfl) (fun a m => f.map_smul a m) (fun _ _ => rfl)

theorem map_tensor (f : M →ₗ[k] N) (r : R) (m : M) :
    map φ f (tensor φ M r m) = tensor φ N r (f m) := by
  let := rightModule φ
  let : SMulCommClass R ℤ R := AddGroup.int_smulCommClass'
  let := rightComm φ
  exact TensorProduct.Balanced.mapLeft_mk
    (k := ℤ) (R := k) (S := R)
    (LinearMap.id : R →ₗ[ℤ] R) f.toAddMonoidHom.toIntLinearMap
    (fun _ _ => rfl) (fun a m => f.map_smul a m) (fun _ _ => rfl) r m

theorem map_id : map φ (LinearMap.id : M →ₗ[k] M) = LinearMap.id := by
  apply hom_ext φ M
  intro r m
  rw [map_tensor]
  rfl

theorem map_comp {P : Type t} [AddCommGroup P] [Module k P]
    (f : M →ₗ[k] N) (g : N →ₗ[k] P) :
    map φ (g.comp f) = (map φ g).comp (map φ f) := by
  apply hom_ext φ M
  intro r m
  simp only [map_tensor, LinearMap.comp_apply]

theorem map_add (f g : M →ₗ[k] N) : map φ (f + g) = map φ f + map φ g := by
  apply hom_ext φ M
  intro r m
  simpa only [map_tensor, LinearMap.add_apply] using
    tensor_add_right φ N r (f m) (g m)

end Maps

end ModuleCat.RingHomInduction
