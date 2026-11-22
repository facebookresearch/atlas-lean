/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.WeakScalar
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceTotalDerived
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Derived equivalences from weak scalar change

For a weak monoid morphism, relative flatness of every cofibrant source
module yields a scalar Quillen equivalence under the stated tensor-colimit
preservation and forgetful-functor identifications of weak equivalences
and fibrations. Derived uniqueness compares the chosen cofibrant-replacement
left functor with the canonical total derived functor. Both the direct
localized restriction adjunction and the chosen cofibrant/fibrant-replacement
adjunction become equivalences with their original functors, units and counits.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra HomotopicalAlgebra.DerivedFunctorCoherence
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.WeakScalar

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ModelCategory C]
  {A B : C} [MonObj A] [MonObj B] [HasColimitsOfSize.{0, 0} C]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]
  [ModelCategory (Mod C A)] [ModelCategory (Mod C B)]

/-- The scalar equivalence acts on the actual ordinary weak localizations. -/
def canonicalDerivedEquivalenceOfRelativeFlatness
    (hWA : weakEquivalences (Mod C A) =
      (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hWB : weakEquivalences (Mod C B) =
      (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
    (hFA : fibrations (Mod C A) =
      (fibrations C).inverseImage (Mod.forget (D := C) A))
    (hFB : fibrations (Mod C B) =
      (fibrations C).inverseImage (Mod.forget (D := C) B))
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p)
    (hFlat : ∀ M : Mod C A, IsCofibrant M → RelativeFlat M) :
    (weakEquivalences (Mod C A)).Localization ≌ (weakEquivalences (Mod C B)).Localization := by
  letI : (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence :=
    isQuillenEquivalenceOfRelativeFlatness hWA hWB hFA hFB p hp hFlat
  exact quillenEquivalenceDerivedEquivalence (Mod.ExtensionOfScalars.adjunction p)


end HomotopicalAlgebra.ModuleTransfer.WeakScalar

namespace HomotopicalAlgebra.ModuleTransfer.WeakScalarDerived

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ModelCategory C]
  {A B : C} [MonObj A] [MonObj B] [HasColimitsOfSize.{0, 0} C]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]
  [ModelCategory (Mod C A)] [ModelCategory (Mod C B)]

variable
  (hWA : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
  (hWB : weakEquivalences (Mod C B) = (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
  (hFA : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
  (hFB : fibrations (Mod C B) = (fibrations C).inverseImage (Mod.forget (D := C) B))

/-- The original chosen-Q left functor has the full canonical derived uniqueness comparison. -/
def chosenLeftCanonicalIso (p : A ⟶ B) [IsMonHom p]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenAdjunction :=
      ModuleTransfer.ScalarChange.isQuillen hWA hWB hFA hFB p
    (ModuleTransfer.ScalarChange.derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived ≅
      (quillenDerivedAdjunctionData (Mod.ExtensionOfScalars.adjunction p)).leftDerived := by
  let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenAdjunction :=
    ModuleTransfer.ScalarChange.isQuillen hWA hWB hFA hFB p
  let d := ModuleTransfer.ScalarChange.derivedAdjunctionData hWA hWB hFA hFB p qA
  let c := quillenDerivedAdjunctionData (Mod.ExtensionOfScalars.adjunction p)
  let : d.leftDerived.IsLeftDerivedFunctor d.leftComparison (weakEquivalences (Mod C A)) := d.leftIsDerived
  let : c.leftDerived.IsLeftDerivedFunctor c.leftComparison (weakEquivalences (Mod C A)) := c.leftIsDerived
  exact Functor.leftDerivedUnique c.leftDerived d.leftDerived d.leftComparison c.leftComparison
    (weakEquivalences (Mod C A))

/-- The actual chosen left functor is an equivalence by the genuine weak scalar Quillen criterion. -/
theorem chosenLeft_isEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p)
    (hFlat : ∀ M : Mod C A, IsCofibrant M → HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M)
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    (ModuleTransfer.ScalarChange.derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived.IsEquivalence := by
  let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence :=
    HomotopicalAlgebra.ModuleTransfer.WeakScalar.isQuillenEquivalenceOfRelativeFlatness hWA hWB hFA hFB p hp hFlat
  let : (quillenDerivedAdjunctionData (Mod.ExtensionOfScalars.adjunction p)).leftDerived.IsEquivalence := by
    change (quillenEquivalenceDerivedEquivalence (Mod.ExtensionOfScalars.adjunction p)).functor.IsEquivalence
    infer_instance
  exact Functor.isEquivalence_of_iso (chosenLeftCanonicalIso hWA hWB hFA hFB p qA).symm

/-- M4's direct localized restriction and chosen-Q induction keep their original full derived adjunction. -/
def directDerivedEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p)
    (hFlat : ∀ M : Mod C A, IsCofibrant M → HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M)
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    (weakEquivalences (Mod C A)).Localization ≌ (weakEquivalences (Mod C B)).Localization := by
  let d := ModuleTransfer.ScalarChange.derivedAdjunctionData hWA hWB hFA hFB p qA
  let : d.leftDerived.IsEquivalence := chosenLeft_isEquivalence hWA hWB hFA hFB p hp hFlat qA
  let : IsIso d.adjunction.unit := inferInstance
  let : IsIso d.adjunction.counit := inferInstance
  exact d.adjunction.toEquivalence

/-- The full chosen-Q/chosen-R derived adjunction is an equivalence without replacing either functor. -/
def replacementDerivedEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p)
    (hFlat : ∀ M : Mod C A, IsCofibrant M → HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M)
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
    (rB : GeneratedFunctorialReplacements.Data (C := Mod C B)) :
    (weakEquivalences (Mod C A)).Localization ≌ (weakEquivalences (Mod C B)).Localization := by
  let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenAdjunction :=
    ModuleTransfer.ScalarChange.isQuillen hWA hWB hFA hFB p
  let d := DerivedAdjunctionCoherence.chosenDerivedAdjunctionData (Mod.ExtensionOfScalars.adjunction p) qA rB
  let : d.leftDerived.IsEquivalence := chosenLeft_isEquivalence hWA hWB hFA hFB p hp hFlat qA
  let : IsIso d.adjunction.unit := inferInstance
  let : IsIso d.adjunction.counit := inferInstance
  exact d.adjunction.toEquivalence

variable (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p)
  (hFlat : ∀ M : Mod C A, IsCofibrant M → HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M)
  (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
  (rB : GeneratedFunctorialReplacements.Data (C := Mod C B))

theorem directDerivedEquivalence_functor :
    (directDerivedEquivalence hWA hWB hFA hFB p hp hFlat qA).functor =
      (ModuleTransfer.ScalarChange.derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived := rfl

theorem directDerivedEquivalence_inverse :
    (directDerivedEquivalence hWA hWB hFA hFB p hp hFlat qA).inverse =
      ModuleTransfer.ScalarChange.rightDerived hWA hWB p := rfl

theorem directDerivedEquivalence_unit_hom :
    (directDerivedEquivalence hWA hWB hFA hFB p hp hFlat qA).unitIso.hom =
      (ModuleTransfer.ScalarChange.derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.unit := rfl

theorem directDerivedEquivalence_counit_hom :
    (directDerivedEquivalence hWA hWB hFA hFB p hp hFlat qA).counitIso.hom =
      (ModuleTransfer.ScalarChange.derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.counit := rfl

theorem replacementDerivedEquivalence_functor :
    let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenAdjunction :=
      ModuleTransfer.ScalarChange.isQuillen hWA hWB hFA hFB p
    (replacementDerivedEquivalence hWA hWB hFA hFB p hp hFlat qA rB).functor =
      DerivedFunctorCoherence.left (Mod.ExtensionOfScalars.adjunction p) qA := rfl

theorem replacementDerivedEquivalence_inverse :
    let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenAdjunction :=
      ModuleTransfer.ScalarChange.isQuillen hWA hWB hFA hFB p
    (replacementDerivedEquivalence hWA hWB hFA hFB p hp hFlat qA rB).inverse =
      DerivedFunctorCoherence.right (Mod.ExtensionOfScalars.adjunction p) rB := rfl

theorem replacementDerivedEquivalence_unit_hom :
    let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenAdjunction :=
      ModuleTransfer.ScalarChange.isQuillen hWA hWB hFA hFB p
    (replacementDerivedEquivalence hWA hWB hFA hFB p hp hFlat qA rB).unitIso.hom =
      (DerivedAdjunctionCoherence.chosenDerivedAdjunctionData
        (Mod.ExtensionOfScalars.adjunction p) qA rB).adjunction.unit := rfl

theorem replacementDerivedEquivalence_counit_hom :
    let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenAdjunction :=
      ModuleTransfer.ScalarChange.isQuillen hWA hWB hFA hFB p
    (replacementDerivedEquivalence hWA hWB hFA hFB p hp hFlat qA rB).counitIso.hom =
      (DerivedAdjunctionCoherence.chosenDerivedAdjunctionData
        (Mod.ExtensionOfScalars.adjunction p) qA rB).adjunction.counit := rfl

end HomotopicalAlgebra.ModuleTransfer.WeakScalarDerived
