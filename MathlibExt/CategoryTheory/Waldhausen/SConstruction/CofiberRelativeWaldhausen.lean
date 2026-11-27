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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativePushout

/-!
# The named general Waldhausen value on cofiber sequences

The genuine relative cofibration property, the existing levelwise weak
equivalences, the existing zero-object axiom and the actual relative
pushout presentation fill every field of the Waldhausen structure.
The value is named and is not a global instance.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace CofiberSequenceCategory

/-- The general extension-category Waldhausen value uses genuine relative
cofibrations and the existing three component weak equivalences. -/
@[instance_reducible]
noncomputable def relativeWaldhausenCategory :
    WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) where
  cofibrations := relativeCofibrations C
  weakEquivalences := levelwiseWeakEquivalences C
  cofibrations_isMultiplicative := by infer_instance
  cofibrations_respectsIso := by infer_instance
  weakEquivalences_isMultiplicative := by infer_instance
  weakEquivalences_respectsIso := by infer_instance
  zero_isCofibration X f := zero_outOf_isRelativeCofibration C X f
  cofibration_pushout {X Y} i hi Z g := by
    let P := CofiberRelativePushoutPresentation.ofRelativeCofibration (C := C) i g hi
    exact ⟨P.apex, P.inl, P.inr, P.isPushout, P.inlRelative⟩

private theorem relativeWaldhausenCategory_cofibration_aux
    {X Y : CofiberSequenceCategory C} (f : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      IsCofibration f) ↔ relativeCofibrations C f := by
  unfold relativeWaldhausenCategory
  rfl

/-- Cofibrations in the named value are exactly the same genuine relative
cofibrations used by its actual pushout constructor. -/
theorem isCofibration_relativeWaldhausenCategory_iff
    {X Y : CofiberSequenceCategory C} (f : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      IsCofibration f) ↔ relativeCofibrations C f :=
  relativeWaldhausenCategory_cofibration_aux C f

private theorem relativeWaldhausenCategory_weakEquivalence_aux
    {X Y : CofiberSequenceCategory C} (f : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      IsWeakEquivalence f) ↔ levelwiseWeakEquivalences C f := by
  unfold relativeWaldhausenCategory
  rfl

/-- Weak equivalences in the named value are the existing three
component weak equivalences. -/
theorem isWeakEquivalence_relativeWaldhausenCategory_iff
    {X Y : CofiberSequenceCategory C} (f : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      IsWeakEquivalence f) ↔ levelwiseWeakEquivalences C f :=
  relativeWaldhausenCategory_weakEquivalence_aux C f

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
