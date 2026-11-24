/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricDiagonal
public import MathlibExt.Algebra.Homology.Hochschild.Maps

/-!
# Naturality of the symmetric Hochschild diagonal

An algebra homomorphism and a compatible ground-linear
coefficient map induce tensor maps intertwining the
symmetric coefficient actions. They commute with
the diagonal, chain maps and normalization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct Simplicial

universe u v v' w w' z

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

section RegularCoefficientMaps

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]

/-- The algebra map on the canonically lifted regular coefficient.
The lift heights remain those of the two coefficient worlds. -/
def regularCoefficientMap (g : A →ₙₐ[k] B) : ULift.{w} A →ₗ[k] ULift.{w'} B where
  toFun a := ULift.up (g a.down)
  map_add' a b := by
    apply ULift.ext
    exact map_add g a.down b.down
  map_smul' r a := by
    apply ULift.ext
    exact map_smul g r a.down

/-- The lifted regular map acts on the original algebra element. -/
@[simp]
theorem regularCoefficientMap_apply (g : A →ₙₐ[k] B) (a : ULift.{w} A) :
    (regularCoefficientMap g : ULift.{w} A →ₗ[k] ULift.{w'} B) a =
      ULift.up (g a.down) := rfl

/-- The regular map respects multiplication along a possibly nonunital
algebra map, with independent source and target coefficient lifts. -/
theorem regularCoefficientMap_smul (g : A →ₙₐ[k] B)
    (a : A) (m : ULift.{w} A) :
    (regularCoefficientMap g : ULift.{w} A →ₗ[k] ULift.{w'} B) (a • m) =
      g a • regularCoefficientMap g m := by
  apply ULift.ext
  change g (a * m.down) = g a * g m.down
  exact map_mul g a m.down

end RegularCoefficientMaps

section SymmetricCoefficients

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type v'} [CommRing B] [Algebra k B]
  {M : Type w} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]
  {N : Type w'} [AddCommGroup N] [Module k N] [Module B N]
  [IsScalarTower k B N]

omit [IsScalarTower k A M] [IsScalarTower k B N] in
/-- Symmetry earns right-action compatibility from the original left-action square. -/
theorem rightAction_compatibility (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    letI := opModule A M
    letI := opModule B N
    ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m := by
  let := opModule A M
  let := opModule B N
  intro a m
  change f (a • m) = g a • f m
  exact hf a m

/-- The coefficient/algebra tensor maps commute with the symmetric
diagonal in every degree, with independent ground, algebra and coefficient
universes. The only coefficient compatibility premise is the original
module-map square. Unit preservation is not needed at this raw stage. -/
theorem diagonalRaw_naturality (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.linearMap g f n).comp (diagonalRaw k A M n) =
      (diagonalRaw k B N n).comp
        (TensorProduct.map
          (ModuleCat.Algebra.Hochschild.linearMap g
            (regularCoefficientMap g : ULift.{w} A →ₗ[k] ULift.{w'} B) n)
          (ModuleCat.Algebra.Hochschild.linearMap g f n)) := by
  apply TensorProduct.curry_injective
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro a0 a
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m b
  change ModuleCat.Algebra.Hochschild.linearMap g f n
      (diagonalRaw k A M n
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b))) =
    diagonalRaw k B N n
      ((ModuleCat.Algebra.Hochschild.linearMap g
          (regularCoefficientMap g : ULift.{w} A →ₗ[k] ULift.{w'} B) n
          (a0 ⊗ₜ[k] PiTensorProduct.tprod k a)) ⊗ₜ[k]
        (ModuleCat.Algebra.Hochschild.linearMap g f n
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)))
  rw [diagonalRaw_tprod, ModuleCat.Algebra.Hochschild.linearMap_tprod,
    ModuleCat.Algebra.Hochschild.linearMap_tprod,
    ModuleCat.Algebra.Hochschild.linearMap_tprod, diagonalRaw_tprod,
    regularCoefficientMap_apply, hf]
  simp only [map_mul]

end SymmetricCoefficients

end ModuleCat.Algebra.Hochschild.Symmetric
