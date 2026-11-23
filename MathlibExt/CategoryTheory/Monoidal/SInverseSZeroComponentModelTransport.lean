/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Actual additive model transport on the original zero component

The existing Pair equivalence and its actual Grothendieck map reflect the
zero difference. The standard full-subcategory restriction therefore gives
the actual zero-component equivalence. Its selected point comparison uses
the original additive functor's zero comparison in BOTH Pair coordinates.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject Algebra

universe uC vC uD vD

namespace CategoryTheory.SInverseS

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

private instance zeroPropertyClosedUnderIso :
    (zeroComponentProperty (C := D)).IsClosedUnderIsomorphisms where
  of_iso e h := (Hom.difference_eq e.hom).symm.trans h

variable (E : C ≌ D) [E.functor.Additive]

private theorem zeroProperty_inverseImage :
    (zeroComponentProperty (C := D)).inverseImage (pairEquivalence E).functor =
      zeroComponentProperty (C := C) := by
  funext X
  apply propext
  change ((pairEquivalence E).functor.obj X).difference = 0 ↔ X.difference = 0
  rw [(pairEquivalence_characteristic E).1]
  let k := grothEquiv E
  have hDifference : ((pairFunctor E.functor).obj X).difference = k X.difference :=
    ((components_characteristic E.functor).1 X).symm.trans
      (grothEquiv_apply E X.difference).symm
  constructor
  · intro h
    apply k.injective
    exact (hDifference.symm.trans h).trans k.map_zero.symm
  · intro h
    exact hDifference.trans ((congrArg k h).trans k.map_zero)

/-- The ORIGINAL zero categories are equivalent through the ORIGINAL
additive Pair equivalence, with independent object and Hom universes. -/
public def zeroComponentEquivalence : ZeroComponent (C := C) ≌ ZeroComponent (C := D) :=
  (pairEquivalence E).congrFullSubcategory (zeroProperty_inverseImage E)

/-- Its whole inclusion square uses the SAME actual Pair functor. -/
public def zeroComponentEquivalenceInclusionIso :
    (zeroComponentEquivalence E).functor ⋙ (zeroComponentProperty (C := D)).ι ≅
      (zeroComponentProperty (C := C)).ι ⋙ (pairEquivalence E).functor := by
  unfold zeroComponentEquivalence
  exact Iso.refl _

/-- Every image object has its literal original Pair image. -/
public theorem zeroComponentEquivalence_functor_obj_obj (X : ZeroComponent (C := C)) :
    ((zeroComponentEquivalence E).functor.obj X).obj =
      (pairEquivalence E).functor.obj X.obj := by
  unfold zeroComponentEquivalence
  rfl

/-- The actual selected zero object is compared to the original target
zero object through the TWO canonical additive zero comparisons. -/
public def zeroComponentEquivalencePointIso :
    (zeroComponentEquivalence E).functor.obj (zeroComponentBaseObject (C := C)) ≅
      zeroComponentBaseObject (C := D) :=
  (zeroComponentProperty (C := D)).isoMk (by
    let z := zeroComponentBaseObject (C := C)
    have hObj := zeroComponentEquivalence_functor_obj_obj E z
    have hFunctor := congrArg (fun k : Pair C ⥤ Pair D => k.obj z.obj)
      (pairEquivalence_characteristic E).1
    exact eqToIso hObj ≪≫ eqToIso hFunctor ≪≫ zeroPairIso E.functor)

end CategoryTheory.SInverseS

end

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uZeroModelSourceObj uZeroModelSourceHom uZeroModelTargetObj uZeroModelTargetHom

namespace CategoryTheory.SInverseS

variable {C : Type uZeroModelSourceObj} [Category.{uZeroModelSourceHom} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uZeroModelTargetObj} [Category.{uZeroModelTargetHom} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

private theorem zeroComponentEquivalencePointIsoInclusionValueComputed
    (E : C ≌ D) [E.functor.Additive] :
    (zeroComponentProperty (C := D)).ι.mapIso (zeroComponentEquivalencePointIso E) =
      eqToIso (zeroComponentEquivalence_functor_obj_obj E
        (zeroComponentBaseObject (C := C))) ≪≫
        eqToIso (congrArg (fun k : Pair C ⥤ Pair D =>
          k.obj (zeroComponentBaseObject (C := C)).obj)
          (pairEquivalence_characteristic E).1) ≪≫ zeroPairIso E.functor := by
  apply Iso.ext
  rfl

/-- The SAME original selected model zero Iso has its entire inclusion value,
including both actual object transports and the canonical zeroPairIso. -/
public theorem zeroComponentEquivalencePointIso_inclusion_value
    (E : C ≌ D) [E.functor.Additive] :
    (zeroComponentProperty (C := D)).ι.mapIso (zeroComponentEquivalencePointIso E) =
      eqToIso (zeroComponentEquivalence_functor_obj_obj E
        (zeroComponentBaseObject (C := C))) ≪≫
        eqToIso (congrArg (fun k : Pair C ⥤ Pair D =>
          k.obj (zeroComponentBaseObject (C := C)).obj)
          (pairEquivalence_characteristic E).1) ≪≫ zeroPairIso E.functor :=
  zeroComponentEquivalencePointIsoInclusionValueComputed E

end CategoryTheory.SInverseS

end

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uZeroIncludeSourceObj uZeroIncludeSourceHom uZeroIncludeTargetObj uZeroIncludeTargetHom

namespace CategoryTheory.SInverseS

variable {C : Type uZeroIncludeSourceObj} [Category.{uZeroIncludeSourceHom} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uZeroIncludeTargetObj} [Category.{uZeroIncludeTargetHom} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

private theorem zeroComponentEquivalenceInclusionIsoAppValueComputed
    (E : C ≌ D) [E.functor.Additive] (X : ZeroComponent (C := C)) :
    (zeroComponentEquivalenceInclusionIso E).app X =
      eqToIso (zeroComponentEquivalence_functor_obj_obj E X) := by
  apply Iso.ext
  rfl

/-- EVERY original inclusion component is its SAME proper object transport,
retaining the original model equivalence and four category worlds. -/
public theorem zeroComponentEquivalenceInclusionIso_app_value
    (E : C ≌ D) [E.functor.Additive] (X : ZeroComponent (C := C)) :
    (zeroComponentEquivalenceInclusionIso E).app X =
      eqToIso (zeroComponentEquivalence_functor_obj_obj E X) :=
  zeroComponentEquivalenceInclusionIsoAppValueComputed E X

end CategoryTheory.SInverseS

end
