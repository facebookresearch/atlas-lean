/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.TensorAlgebra.NonUnital
public import Mathlib.Algebra.Algebra.Unitization

/-!
# Lifting original vectors into a possibly nonunital algebra

The stock tensor lift into the actual algebraic unitization has the original
augmentation as its scalar component. Its second component therefore restricts
to a nonunital algebra homomorphism on the actual augmentation kernel.
This constructor serves the source tensor projection and kernel extension,
without selecting DATA from an open universal-property theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe uR uV uA
namespace NonUnitalTensorAlgebra

variable (R : Type uR) [CommSemiring R]
variable (V : Type uV) [AddCommMonoid V] [Module R V]
variable {A : Type uA} [NonUnitalSemiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The stock unital lift into the actual unitization of the original target. -/
def unitizationLift (s : V →ₗ[R] A) : TensorAlgebra R V →ₐ[R] Unitization R A :=
  TensorAlgebra.lift R ((Unitization.inrHom R R A).comp s)

/-- Original generators map to the scalar-zero embedding of their given values. -/
theorem unitizationLift_ι (s : V →ₗ[R] A) (v : V) :
    unitizationLift R V s (TensorAlgebra.ι R v) = (s v : Unitization R A) :=
  TensorAlgebra.lift_ι_apply ((Unitization.inrHom R R A).comp s) v

/-- The actual scalar component equals augmentation, allowing restriction to its kernel. -/
theorem unitizationLift_fst (s : V →ₗ[R] A) (x : TensorAlgebra R V) :
    (unitizationLift R V s x).fst = TensorAlgebra.algebraMapInv x := by
  have h : (Unitization.fstHom (R := R) (A := A)).comp (unitizationLift R V s) =
      TensorAlgebra.algebraMapInv := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change (unitizationLift R V s (TensorAlgebra.ι R v)).fst =
      TensorAlgebra.algebraMapInv (TensorAlgebra.ι R v)
    rw [unitizationLift_ι, TensorAlgebra.algebraMapInv_ι R V v]
    exact Unitization.fst_inr R (s v)
  exact congrArg (fun f : TensorAlgebra R V →ₐ[R] R => f x) h

/-- The original nonunital target receives the actual scalar-zero tensor carrier. -/
def lift (s : V →ₗ[R] A) : NonUnitalTensorAlgebra R V →ₙₐ[R] A where
  toFun x := (unitizationLift R V s x.1).snd
  map_zero' := by
    change (unitizationLift R V s 0).snd = 0
    rw [map_zero]
    exact Unitization.snd_zero
  map_add' := by
    intro x y
    change (unitizationLift R V s (x.1 + y.1)).snd =
      (unitizationLift R V s x.1).snd + (unitizationLift R V s y.1).snd
    rw [map_add, Unitization.snd_add]
  map_mul' := by
    intro x y
    change (unitizationLift R V s (x.1 * y.1)).snd =
      (unitizationLift R V s x.1).snd * (unitizationLift R V s y.1).snd
    rw [map_mul, Unitization.snd_mul]
    have hx := (TensorAlgebra.mem_augmentationKernel R V x.1).1 x.property
    have hy := (TensorAlgebra.mem_augmentationKernel R V y.1).1 y.property
    simp only [unitizationLift_fst, hx, hy, zero_smul, zero_add]
  map_smul' := by
    intro r x
    change (unitizationLift R V s (r • x.1)).snd = r • (unitizationLift R V s x.1).snd
    rw [map_smul, Unitization.snd_smul]

/-- The literal second-component value of the restricted lift. -/
theorem lift_apply (s : V →ₗ[R] A) (x : NonUnitalTensorAlgebra R V) :
    lift R V s x = (unitizationLift R V s x.1).snd := rfl

/-- The computed lift has every original degree-one value. -/
theorem lift_ι (s : V →ₗ[R] A) (v : V) :
    lift R V s (ι R V v) = s v := by
  change (unitizationLift R V s (TensorAlgebra.ι R v)).snd = s v
  rw [unitizationLift_ι]
  exact Unitization.snd_inr R (s v)

end NonUnitalTensorAlgebra
