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
# Derived Hom and enveloping Chevalley–Eilenberg cohomology

Under `Module.Free R L`, the exterior-cochain homology identifies with linear
Ext through the enveloping resolution. The first-variable Ext comparison
then identifies it with derived-category Ext and right-derived linear Hom.
The trivial module and left coefficient module are lifted to a common
carrier universe; module-category instances supply Ext and injective
resolutions there.
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

/-- The exterior cochain homology is the native derived-category Ext
module, by the existing native first-variable comparison. -/
def leftCoefficientHomologyIsoDerivedExt (n : ℕ) :
    (leftCoefficientCochainComplex R L M).homology n ≅
      ModuleCat.of R (Abelian.Ext (liftedEnvelopingTrivial.{u, v, w} R L)
        (liftedLeftCoefficient R L M) n) :=
  leftCoefficientHomologyIsoExt R L M n ≪≫
    (Abelian.firstVariableLinearExtIso R (liftedEnvelopingTrivial.{u, v, w} R L) n).app
      (liftedLeftCoefficient R L M)

/-- The exterior cochain homology is the right derived native linear
Hom functor, with the original left coefficient module as its derived variable. -/
def leftCoefficientHomologyIsoRightDerived (n : ℕ) :
    (leftCoefficientCochainComplex R L M).homology n ≅
      ((((linearCoyoneda R (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L))).obj
        (op (liftedEnvelopingTrivial.{u, v, w} R L))).rightDerived n).obj
        (liftedLeftCoefficient R L M)) :=
  leftCoefficientHomologyIsoExt R L M n ≪≫
    ((Abelian.rightDerivedLinearCoyonedaIsoFirstVariableExt R
      (liftedEnvelopingTrivial.{u, v, w} R L) n).app (liftedLeftCoefficient R L M)).symm

end ChevalleyEilenberg
