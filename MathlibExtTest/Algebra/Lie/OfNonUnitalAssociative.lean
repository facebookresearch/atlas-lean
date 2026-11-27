/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Lie.OfNonUnitalAssociative
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Mul

/-! Clients of the actual nonunital commutator constructors and algebra-map conversion. -/

@[expose] public section

noncomputable section

universe u v w z

attribute [local instance 100] LieRing.ofNonUnitalAssociativeRing
attribute [local instance 100] LieAlgebra.ofNonUnitalAssociativeAlgebra

section NonUnital

variable (k : Type u) [CommRing k]
variable (A : Type v) (B : Type w) (C : Type z)
  [NonUnitalRing A] [NonUnitalRing B] [NonUnitalRing C]
  [Module k A] [Module k B] [Module k C]
  [IsScalarTower k A A] [IsScalarTower k B B] [IsScalarTower k C C]
  [SMulCommClass k A A] [SMulCommClass k B B] [SMulCommClass k C C]

/-- Native Lie maps across independent coefficient universes preserve scaled brackets. -/
example (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] C) (r : k) (x y : A) :
    g.toLieHom (r • f.toLieHom ⁅x, y⁆) = r • ⁅g (f x), g (f y)⁆ := by
  simp only [map_smul, LieHom.map_lie, NonUnitalAlgHom.toLieHom_apply]

/-- The zero nonunital algebra map becomes the native zero Lie map without a unit premise. -/
example : (0 : A →ₙₐ[k] B).toLieHom = (0 : A →ₗ⁅k⁆ B) := by
  ext x
  simp

end NonUnital

namespace NonUnitalMatrixClients

private abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℤ

private def leftUnit : Matrix2 := fun i j => if i = 0 ∧ j = 1 then 1 else 0

private def rightUnit : Matrix2 := fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- On unital input maps, both conversions retain the same original linear map. -/
example (f : Matrix2 →ₐ[ℤ] Matrix2) :
    f.toNonUnitalAlgHom.toLieHom.toLinearMap = f.toLieHom.toLinearMap := rfl

/-- The two matrix units have a nonzero commutator, with its original product order. -/
example : (⁅leftUnit, rightUnit⁆ : Matrix2) 0 0 = 1 := by
  decide

/-- The opposite diagonal coordinate has the opposite sign. -/
example : (⁅leftUnit, rightUnit⁆ : Matrix2) 1 1 = -1 := by
  decide

/-- Nonunital maps include the zero map on a nontrivial unital ring; it does not preserve one. -/
example : (0 : Matrix2 →ₙₐ[ℤ] Matrix2).toLieHom (1 : Matrix2) ≠ (1 : Matrix2) := by
  simpa only [NonUnitalAlgHom.toLieHom_apply, NonUnitalAlgHom.zero_apply] using
    (zero_ne_one : (0 : Matrix2) ≠ 1)

end NonUnitalMatrixClients
