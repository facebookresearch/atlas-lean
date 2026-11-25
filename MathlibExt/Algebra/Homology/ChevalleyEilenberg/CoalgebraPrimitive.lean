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

public import Mathlib.Algebra.Homology.Additive
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNative
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Primitive Chevalley–Eilenberg chains

For a Lie algebra over a commutative ring, the coproduct minus the two coaugmentation terms is
a chain map. Its kernel is the primitive Chevalley–Eilenberg subcomplex, whose inclusion
annihilates the primitive equation in every degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]


/-- The Chevalley–Eilenberg coproduct minus the two coaugmentation terms. -/
def nativePrimitiveMap : ((canonicalChainData R L).complex) ⟶ nativeTensorComplex R L := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  let right : ((canonicalChainData R L).complex) ⟶ nativeTensorComplex R L :=
    (HomologicalComplex.rightUnitor ((canonicalChainData R L).complex)).inv ≫
      HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex)) (nativeComplexCoaug R L)
  let left : ((canonicalChainData R L).complex) ⟶ nativeTensorComplex R L :=
    (HomologicalComplex.leftUnitor ((canonicalChainData R L).complex)).inv ≫
      HomologicalComplex.tensorHom (nativeComplexCoaug R L) (𝟙 ((canonicalChainData R L).complex))
  exact nativeComplexComul R L - (right + left)

/-- The kernel subcomplex of the Chevalley–Eilenberg primitive equation. -/
def nativePrimitiveComplex : ChainComplex (ModuleCat.{max u v} R) ℕ := kernel (nativePrimitiveMap R L)

/-- The canonical primitive inclusion is a chain map. -/
def nativePrimitiveInclusion : nativePrimitiveComplex R L ⟶ ((canonicalChainData R L).complex) :=
  kernel.ι (nativePrimitiveMap R L)

@[reassoc]
theorem nativePrimitiveInclusion_equation :
    nativePrimitiveInclusion R L ≫ nativePrimitiveMap R L = 0 :=
  kernel.condition (nativePrimitiveMap R L)

/-- Every component of the primitive inclusion satisfies the primitive equation. -/
theorem nativePrimitiveInclusion_component (n : ℕ) :
    (nativePrimitiveInclusion R L).f n ≫ (nativePrimitiveMap R L).f n = 0 := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
    congrArg (fun f => f.f n) (nativePrimitiveInclusion_equation R L)

end ChevalleyEilenberg
