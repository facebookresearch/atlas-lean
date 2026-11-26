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

Let `R` be a commutative ring and `L` an `R`-Lie algebra. The CE coproduct and coaugmentation
define the chain map `P(x) = Δ(x) - (x ⊗ 1 + 1 ⊗ x)` into the tensor total complex.

The kernel of `P` is the primitive chain subcomplex. Its kernel inclusion is a chain map and
satisfies the primitive equation in every degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]


/-- The primitive-equation map of the CE coalgebra complex.

Subtract the two coaugmentation tensor maps `x ↦ x ⊗ 1` and `x ↦ 1 ⊗ x` from the CE
comultiplication chain map. -/
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

/-- The primitive kernel subcomplex of CE chains.

Take the chain-complex kernel of `Δ - (id ⊗ η + η ⊗ id)`, with the tensor unitors included in
the two coaugmentation terms. -/
def nativePrimitiveComplex : ChainComplex (ModuleCat.{max u v} R) ℕ := kernel (nativePrimitiveMap R L)

/-- The chain inclusion of primitive CE chains.

The kernel inclusion maps the primitive subcomplex into the canonical CE complex. -/
def nativePrimitiveInclusion : nativePrimitiveComplex R L ⟶ ((canonicalChainData R L).complex) :=
  kernel.ι (nativePrimitiveMap R L)

/-- The primitive equation of the primitive chain inclusion.

The primitive inclusion followed by the map `Δ - (id ⊗ η + η ⊗ id)` is zero. -/
@[reassoc]
theorem nativePrimitiveInclusion_equation :
    nativePrimitiveInclusion R L ≫ nativePrimitiveMap R L = 0 :=
  kernel.condition (nativePrimitiveMap R L)

/-- The degreewise primitive equation of the chain inclusion.

In each degree, the component of the primitive inclusion followed by the corresponding
primitive-equation component is zero. -/
theorem nativePrimitiveInclusion_component (n : ℕ) :
    (nativePrimitiveInclusion R L).f n ≫ (nativePrimitiveMap R L).f n = 0 := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
    congrArg (fun f => f.f n) (nativePrimitiveInclusion_equation R L)

end ChevalleyEilenberg
