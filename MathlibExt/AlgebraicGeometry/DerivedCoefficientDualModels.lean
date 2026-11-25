/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels

/-!
# Actual derived coefficient dual modules

The coefficient opposite comparison retains the literal homogeneous
coefficient map of the commutative one-object algebra. The dual module
is constructed from the native regular Yoneda module and the native
corepresentable Hom functor. On a cofibrant module its value is the
actual dgHom complex into the regular coefficient module, hence
RHom_A(E,A), with its full A-action retained.

A requested dual or transpose cannot substitute an unrelated cochain
complex. Cofibrant module replacements retain their actual augmentation.
Reference: PTVV arXiv:1111.3209v4, §2.1, Definition 2.4.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels

universe u v
variable {R : Type u} [CommRing R]

/-- The source double opposite preserves every original Hom map. -/
def doubleOpposite (C : Type v) [DGCategory R C] :
    EnrichedFunctor (Cochains R) C Cᵒᵖᵒᵖ where
  obj x := op (op x)
  map _ _ := 𝟙 _
  map_id x := by
    change eId (Cochains R) x ≫ 𝟙 _ = eId (Cochains R) x
    exact Category.comp_id _
  map_comp X Y Z := by
    change eComp (Cochains R) X Y Z ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫
        ((β_ (dgHomComplex R X Y) (dgHomComplex R Y Z)).hom ≫
          (β_ (dgHomComplex R Y Z) (dgHomComplex R X Y)).hom ≫
            eComp (Cochains R) X Y Z)
    simp only [Category.comp_id, tensorHom_id, Category.id_comp,
      ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      MonoidalCategory.id_whiskerRight, Category.id_comp]

variable (C : DGCat R) (o : C)

/-- The actual regular coefficient module is the source representable. -/
def regularModule : RightModule R C := (dgYoneda R (C := C)).obj o

/-- The commutative opposite adapter fixes every coefficient Hom map.
The coefficient object is unique in the applications. -/
structure OppositeModel where
  functor : EnrichedFunctor (Cochains R) Cᵒᵖ C
  object_eq : ∀ x : Cᵒᵖ, functor.obj x = x.unop
  map_eq : ∀ x y : Cᵒᵖ, HEq (functor.map x y) (𝟙 (dgHomComplex R o o))

/-- The actual coefficient dual is a source representable construction,
using the regular module and the fixed coefficient opposite adapter. -/
def dualModule (O : OppositeModel C o) (M : RightModule R C) : RightModule R C :=
  ⟨(((O.functor.comp (Cochains R) (dgYoneda R (C := C))).comp
      (Cochains R) (doubleOpposite (R := R) (RightModule R C))).comp
        (Cochains R)
        (dgRepresentable (C := (RightModule R C)ᵒᵖ) R (op M)))⟩

/-- The underlying dual is literally the actual coefficient-linear Hom into A. -/
def dualValueIso (O : OppositeModel C o) (M : RightModule R C) :
    value C o (dualModule C o O M) ≅ dgHomComplex R M (regularModule C o) :=
  eqToIso (by
    dsimp only [value, dualModule, EnrichedFunctor.comp, doubleOpposite]
    rw [O.object_eq]
    rfl)

/-- Derived duality applies the same native dual to a genuine cofibrant replacement. -/
def derivedDual (O : OppositeModel C o) {M : RightModule R C} (P : ModuleReplacement M) :
    RightModule R C := dualModule C o O P.module

end MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
