/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.StructuredReplacementComparisons
public import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer.OriginalRank

/-!
# Structured replacement comparisons from the original transferred generation

The original source-rank transfer supplies the structured model and its two
complete original factor records. The original base generation supplies the
base factor records. Their actual factories construct the R1 comparisons;
both independent ranks, bottoms, all Q/R maps and all factor fields survive.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD wC wD

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.ModuleTransfer.StructuredReplacements

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D]
  {L : C ⥤ D} {U : D ⥤ C} (adj : L ⊣ U)
  {I J : MorphismProperty C}
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (t : RightTransfer.OriginalRankModelTransfer L U I J κD)
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

/-- The actual original base and transferred factors construct the complete underlying replacement package. -/
def ofOriginalRank :
    letI : ModelCategory D := t.model
    StructuredReplacementComparisons.ComparisonData U := by
  letI : ModelCategory D := t.model
  exact StructuredReplacementComparisons.construct U
    dC.cofibrantFactorizationData dC.fibrantFactorizationData
    t.generation.cofibrantFactorizationData t.generation.fibrantFactorizationData
    t.weak_eq adj t.fibrations_eq

/-- The complete original base generation Q/R and both original factor records are retained exactly. -/
theorem ofOriginalRank_base :
    letI : ModelCategory D := t.model
    (ofOriginalRank adj t dC).base = GeneratedFunctorialReplacements.fromGeneration dC := rfl

/-- The complete same-original-rank structured Q/R factory is retained exactly. -/
theorem ofOriginalRank_structured :
    letI : ModelCategory D := t.model
    (ofOriginalRank adj t dC).structured = t.replacements := rfl

/-- Every original structured source arrow keeps the same complete initial-square Q map. -/
theorem ofOriginalRank_Q_map {X Y : D} (f : X ⟶ Y) :
    letI : ModelCategory D := t.model
    (ofOriginalRank adj t dC).structured.Q.map f = t.replacements.Q.map f := rfl

/-- Every original structured source arrow keeps the same complete terminal-square R map. -/
theorem ofOriginalRank_R_map {X Y : D} (f : X ⟶ Y) :
    letI : ModelCategory D := t.model
    (ofOriginalRank adj t dC).structured.R.map f = t.replacements.R.map f := rfl

end HomotopicalAlgebra.ModuleTransfer.StructuredReplacements
