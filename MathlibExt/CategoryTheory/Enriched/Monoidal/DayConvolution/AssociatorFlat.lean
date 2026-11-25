/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorIndex
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendIso

/-!
# The original flattened triple Day comparison

Inverse index-associator precomposition and forward coefficient
reassociation descend through the two original complete relation faces.
The inverse uses the actual opposite maps on the same three inputs.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorFlat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
  (F G H : EnrichedFunctor V I V) (m : I)

attribute [local instance] Enriched.prodCategory

/-- The original left triple object family. -/
abbrev leftObjects : (I × I) × I → V :=
  Enriched.weightedCoend.objects (AssociatorIndex.leftWeight d m)
    (Associator.leftCoefficients F G H)

/-- The original complete left triple relation family. -/
abbrev leftRelations : ((I × I) × I) × ((I × I) × I) → V :=
  Enriched.weightedCoend.relations (AssociatorIndex.leftWeight d m)
    (Associator.leftCoefficients F G H)

/-- The original right triple object family on the same three input values. -/
abbrev rightObjects : (I × I) × I → V :=
  Enriched.weightedCoend.objects (AssociatorIndex.rightWeight d m)
    (Associator.rightCoefficients F G H)

/-- The original complete right triple relation family includes the whole Hom associator. -/
abbrev rightRelations : ((I × I) × I) × ((I × I) × I) → V :=
  Enriched.weightedCoend.relations (AssociatorIndex.rightWeight d m)
    (Associator.rightCoefficients F G H)

variable [HasCoproduct (leftObjects d F G H m)] [HasCoproduct (leftRelations d F G H m)]
  [HasCoproduct (rightObjects d F G H m)] [HasCoproduct (rightRelations d F G H m)]

/-- The actual left triple weight-face coproduct map. -/
abbrev leftMap0 := Enriched.weightedCoend.leftMap (AssociatorIndex.leftWeight d m)
  (Associator.leftCoefficients F G H)

/-- The actual left triple coefficient-action coproduct map. -/
abbrev leftMap1 := Enriched.weightedCoend.rightMap (AssociatorIndex.leftWeight d m)
  (Associator.leftCoefficients F G H)

/-- The actual right triple weight-face coproduct map. -/
abbrev rightMap0 := Enriched.weightedCoend.leftMap (AssociatorIndex.rightWeight d m)
  (Associator.rightCoefficients F G H)

/-- The actual right triple coefficient-action coproduct map. -/
abbrev rightMap1 := Enriched.weightedCoend.rightMap (AssociatorIndex.rightWeight d m)
  (Associator.rightCoefficients F G H)

variable [HasCoequalizer (leftMap0 d F G H m) (leftMap1 d F G H m)]
  [HasCoequalizer (rightMap0 d F G H m) (rightMap1 d F G H m)]

/-- The selected original left flattened triple coend. -/
abbrev leftPoint : V := Enriched.weightedCoend (AssociatorIndex.leftWeight d m)
  (Associator.leftCoefficients F G H)

/-- The selected original right flattened triple coend. -/
abbrev rightPoint : V := Enriched.weightedCoend (AssociatorIndex.rightWeight d m)
  (Associator.rightCoefficients F G H)

/-- The actual generator of the original left flattened triple presentation. -/
abbrev leftGenerator (X : (I × I) × I) :
    leftObjects d F G H m X ⟶ leftPoint d F G H m :=
  Enriched.weightedCoend.ι (AssociatorIndex.leftWeight d m) (Associator.leftCoefficients F G H) X

/-- The actual generator of the original right flattened triple presentation. -/
abbrev rightGenerator (X : (I × I) × I) :
    rightObjects d F G H m X ⟶ rightPoint d F G H m :=
  Enriched.weightedCoend.ι (AssociatorIndex.rightWeight d m) (Associator.rightCoefficients F G H) X

/-- The actual flattened triple associator, descended through both complete original faces. -/
def iso : leftPoint d F G H m ≅ rightPoint d F G H m :=
  Enriched.weightedCoend.ComponentIso.iso (AssociatorIndex.leftWeight d m)
    (AssociatorIndex.rightWeight d m)
    (Associator.leftCoefficients F G H) (Associator.rightCoefficients F G H)
    (AssociatorIndex.weightIso d m)
    (fun X => α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2))
    (AssociatorIndex.weight_naturality d m)
    (Associator.coefficients_naturality F G H)

/-- The forward map keeps every original generator and its actual two associator factors. -/
@[reassoc]
theorem leftGenerator_iso_hom (X : (I × I) × I) :
    leftGenerator d F G H m X ≫ (iso d F G H m).hom =
      (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv m ⊗ₘ
        (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom) ≫
          rightGenerator d F G H m X := by
  have h := Enriched.weightedCoend.ComponentIso.ι_iso_hom (AssociatorIndex.leftWeight d m)
    (AssociatorIndex.rightWeight d m)
    (Associator.leftCoefficients F G H) (Associator.rightCoefficients F G H)
    (AssociatorIndex.weightIso d m)
    (fun X => α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2))
    (AssociatorIndex.weight_naturality d m)
    (Associator.coefficients_naturality F G H) X
  exact h.trans (congrArg
    (fun f : (AssociatorIndex.leftWeight d m).obj (op X) ⟶
      (AssociatorIndex.rightWeight d m).obj (op X) =>
      (f ⊗ₘ (show (Associator.leftCoefficients F G H).obj X ⟶
        (Associator.rightCoefficients F G H).obj X from
          (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom)) ≫
        rightGenerator d F G H m X)
    (AssociatorIndex.weightIso_hom d m X))

/-- The inverse map keeps every original generator and the actual opposite factors. -/
@[reassoc]
theorem rightGenerator_iso_inv (X : (I × I) × I) :
    rightGenerator d F G H m X ≫ (iso d F G H m).inv =
      (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).hom m ⊗ₘ
        (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv) ≫
          leftGenerator d F G H m X := by
  have h := Enriched.weightedCoend.ComponentIso.ι_iso_inv (AssociatorIndex.leftWeight d m)
    (AssociatorIndex.rightWeight d m)
    (Associator.leftCoefficients F G H) (Associator.rightCoefficients F G H)
    (AssociatorIndex.weightIso d m)
    (fun X => α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2))
    (AssociatorIndex.weight_naturality d m)
    (Associator.coefficients_naturality F G H) X
  exact h.trans (congrArg
    (fun f : (AssociatorIndex.rightWeight d m).obj (op X) ⟶
      (AssociatorIndex.leftWeight d m).obj (op X) =>
      (f ⊗ₘ (show (Associator.rightCoefficients F G H).obj X ⟶
        (Associator.leftCoefficients F G H).obj X from
          (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv)) ≫
        leftGenerator d F G H m X)
    (AssociatorIndex.weightIso_inv d m X))

end CategoryTheory.EnrichedDayKernel.AssociatorFlat
