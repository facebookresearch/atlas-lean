/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Adjunction.FunctionUnit
public import MathlibExt.CategoryTheory.Monoidal.Mod.EquivalenceFunction

/-!
# Selected units of module function adjunctions transported through equivalences

The complete source tensor map and internal-Hom precomposition use the
original module equivalence and its parametrized adjunction. Both directions
of the unit mate retain the chosen right-unit comparison.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Mod.EquivalenceFunctionTransport.FunctionUnit

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

omit [HasEqualizers C] in
/-- The complete transported covariant source arrow has its identical original value. -/
theorem sourceSmashMap_heq {S T : D} (f : S ⟶ T) :
    HEq ((Mod.EquivalenceFunctionTransport.smashBifunctor A E).map f)
      (Mod.EquivalenceFunctionTransport.sourceSmashMap A E f) := HEq.refl _

/-- The full transported source equation keeps the original selected unit and adjunction. -/
theorem sourcePre_unit_adjoint {S T : D} (f : S ⟶ T)
    (unitIso : Mod.EquivalenceFunctionTransport.functor A E T ≅ 𝟭 D) (X : D) :
    ((Mod.EquivalenceFunctionTransport.adjunction A E S).homEquiv X X)
      ((Mod.EquivalenceFunctionTransport.sourceSmashMap A E f).app X ≫
        (FunctionUnitAdjunction.leftUnitIso
          (Mod.EquivalenceFunctionTransport.adjunction A E T) unitIso).hom.app X) =
      unitIso.inv.app X ≫ (Mod.EquivalenceFunctionTransport.precompose A E f).app X :=
  FunctionUnitAdjunction.sourcePre_unit_adjoint
    (Mod.EquivalenceFunctionTransport.parametrizedAdjunction A E) f unitIso X

/-- Its inverse has exactly the same whole transported source map and chosen unit. -/
theorem sourcePre_unit_uncurried {S T : D} (f : S ⟶ T)
    (unitIso : Mod.EquivalenceFunctionTransport.functor A E T ≅ 𝟭 D) (X : D) :
    ((Mod.EquivalenceFunctionTransport.adjunction A E S).homEquiv X X).symm
      (unitIso.inv.app X ≫ (Mod.EquivalenceFunctionTransport.precompose A E f).app X) =
      (Mod.EquivalenceFunctionTransport.sourceSmashMap A E f).app X ≫
        (FunctionUnitAdjunction.leftUnitIso
          (Mod.EquivalenceFunctionTransport.adjunction A E T) unitIso).hom.app X :=
  FunctionUnitAdjunction.sourcePre_unit_uncurried
    (Mod.EquivalenceFunctionTransport.parametrizedAdjunction A E) f unitIso X

end CategoryTheory.Mod.EquivalenceFunctionTransport.FunctionUnit
