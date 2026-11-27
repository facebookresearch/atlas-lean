/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.ExtComparison
public import MathlibExt.CategoryTheory.Abelian.Ext.DerivedFirstVariable
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Derived Hom comparisons for enveloping cochains

Let `R` be a commutative ring, `L` an `R`-Lie algebra with free underlying `R`-module, and `M`
a left `U_R(L)`-module. The enveloping projective resolution identifies the degree-`n`
cohomology of the exterior cochain complex with linear Ext from the trivial module to `M`.

The first-variable Ext comparison then identifies this cohomology with derived-category Ext
and with the degree-`n` right-derived linear Hom functor in the coefficient variable. The
trivial module and coefficient module are lifted to the joint carrier universe `max u v w`.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Opposite
open scoped ModuleCat.Algebra

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

variable (M : ModuleCat.{w} (UniversalEnvelopingAlgebra R L)) [Module.Free R L]

/-- The derived-category Ext comparison for exterior cochains.

For `Module.Free R L`, the degree-`n` cohomology of the exterior cochain complex with left
coefficients `M` is isomorphic, as an `R`-module, to derived-category Ext from the lifted
trivial enveloping module to the lifted coefficient module. -/
def leftCoefficientHomologyIsoDerivedExt (n : ℕ) :
    (leftCoefficientCochainComplex R L M).homology n ≅
      ModuleCat.of R (Abelian.Ext (liftedEnvelopingTrivial.{u, v, w} R L)
        (liftedLeftCoefficient R L M) n) :=
  leftCoefficientHomologyIsoExt R L M n ≪≫
    (Abelian.firstVariableLinearExtIso R (liftedEnvelopingTrivial.{u, v, w} R L) n).app
      (liftedLeftCoefficient R L M)

/-- The right-derived Hom comparison for exterior cochains.

For `Module.Free R L`, degree-`n` exterior cohomology with coefficients `M` is isomorphic to
the `n`th right-derived linear Hom functor from the lifted trivial module, evaluated on the
lifted coefficient module. -/
def leftCoefficientHomologyIsoRightDerived (n : ℕ) :
    (leftCoefficientCochainComplex R L M).homology n ≅
      ((((linearCoyoneda R (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L))).obj
        (op (liftedEnvelopingTrivial.{u, v, w} R L))).rightDerived n).obj
        (liftedLeftCoefficient R L M)) :=
  leftCoefficientHomologyIsoExt R L M n ≪≫
    ((Abelian.rightDerivedLinearCoyonedaIsoFirstVariableExt R
      (liftedEnvelopingTrivial.{u, v, w} R L) n).app (liftedLeftCoefficient R L M)).symm

end ChevalleyEilenberg
