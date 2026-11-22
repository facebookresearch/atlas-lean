/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidTransfer.CellularWeakness
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.RelativeSmallness
public import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# Original associative free-generator source ranks

The caller supplies uniform relative smallness on the actual free-I and
free-J continuous ordinal diagrams. A common regular cardinal is derived
from the original small families and their source bounds. Both full
small-object eligibility records retain the original free maps.
-/

@[expose] public section

noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.SmallObject

namespace HomotopicalAlgebra.MonoidTransfer

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]

/-- The caller's original small generating family remains small under the actual free functor. -/
theorem freeGenerators_isSmall (P : MorphismProperty C) [P.IsSmall.{w}] :
    (freeGenerators P).IsSmall.{w} := IsSmall.strictMap (inferInstance : P.IsSmall.{w}) free

/-- A common regular cardinal and both complete eligibility records for the original free families. -/
structure FreeGenerationCardinal (I J : MorphismProperty C)
    (hI : UniformRelativeSourceSmallness.{w} (freeGenerators I))
    (hJ : UniformRelativeSourceSmallness.{w} (freeGenerators J)) where
  /-- The produced actual common cardinal. -/
  cardinal : Cardinal.{w}
  /-- Its original regularity dictionary. -/
  regular : Fact cardinal.IsRegular
  /-- The produced bottom on the same original ordinal. -/
  orderBot : OrderBot cardinal.ord.ToType
  /-- The original free-I source bounds are strictly below the produced regular rank. -/
  sourceI_bounds : ∀ i : (freeGenerators I).toSet,
    UniformRelativeSourceSmallness.sourceBound hI i < cardinal
  /-- The original free-J source bounds are strictly below that same rank. -/
  sourceJ_bounds : ∀ j : (freeGenerators J).toSet,
    UniformRelativeSourceSmallness.sourceBound hJ j < cardinal
  /-- All six original free-I small-object fields, including the actual Hom colimit maps. -/
  I_smallObject : letI := regular; letI := orderBot; (freeGenerators I).IsCardinalForSmallObjectArgument cardinal
  /-- All six original free-J small-object fields at the identical produced cardinal. -/
  J_smallObject : letI := regular; letI := orderBot; (freeGenerators J).IsCardinalForSmallObjectArgument cardinal

variable [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} (Mon C)]

/-- Conventional relative source smallness constructs the common original free-generation datum. -/
def freeGenerationCardinal (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
    (hI : UniformRelativeSourceSmallness.{w} (freeGenerators I))
    (hJ : UniformRelativeSourceSmallness.{w} (freeGenerators J)) :
    FreeGenerationCardinal I J hI hJ := by
  apply Classical.choice
  let : (freeGenerators I).IsSmall.{w} := freeGenerators_isSmall I
  let : (freeGenerators J).IsSmall.{w} := freeGenerators_isSmall J
  let : LocallySmall.{w} (Mon C) := locallySmall_of_faithful (Mon.forget C)
  obtain ⟨κ, hκ, hIκ, hJκ⟩ := exists_common_relative_source_bound (freeGenerators I) (freeGenerators J) hI hJ
  let : Fact κ.IsRegular := ⟨hκ⟩
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType hκ.ne_zero
  let bottom : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  let : OrderBot κ.ord.ToType := bottom
  refine ⟨?_⟩
  exact
    { cardinal := κ
      regular := inferInstance
      orderBot := bottom
      sourceI_bounds := hIκ
      sourceJ_bounds := hJκ
      I_smallObject := isCardinalForSmallObjectArgument_of_uniform_bounds (freeGenerators I) hI κ hIκ
      J_smallObject := isCardinalForSmallObjectArgument_of_uniform_bounds (freeGenerators J) hJ κ hJκ }

namespace FreeGenerationCardinal

variable {I J : MorphismProperty C}
  {hI : UniformRelativeSourceSmallness.{w} (freeGenerators I)}
  {hJ : UniformRelativeSourceSmallness.{w} (freeGenerators J)}
  (d : FreeGenerationCardinal I J hI hJ)

local instance : Fact d.cardinal.IsRegular := d.regular
/-- Use the original ordinal bottom retained by the produced common generation cardinal. -/
local instance : OrderBot d.cardinal.ord.ToType := d.orderBot

omit [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} (Mon C)] in
/-- The original free-I Hom functor preserves the caller's unchanged continuous ordinal diagram. -/
theorem sourceI_preservesColimit (i : (freeGenerators I).toSet)
    (F : d.cardinal.ord.ToType ⥤ Mon C) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬ IsMax j → relativeCellMaps.{w} (freeGenerators I)
      (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (op i.1.left)) :=
  UniformRelativeSourceSmallness.sourceBound_spec hI i d.cardinal (d.sourceI_bounds i) F hF

omit [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} (Mon C)] in
/-- The original free-J Hom functor preserves the same supplied J-cell diagram and maps. -/
theorem sourceJ_preservesColimit (j : (freeGenerators J).toSet)
    (F : d.cardinal.ord.ToType ⥤ Mon C) [F.IsWellOrderContinuous]
    (hF : ∀ k, ¬ IsMax k → relativeCellMaps.{w} (freeGenerators J)
      (F.map (homOfLE (Order.le_succ k)))) :
    PreservesColimit F (coyoneda.obj (op j.1.left)) :=
  UniformRelativeSourceSmallness.sourceBound_spec hJ j d.cardinal (d.sourceJ_bounds j) F hF

omit [LocallySmall.{w} C] in
/-- The entire original free-I canonical cocone remains colimiting after its original source Hom. -/
def sourceIMappedCanonicalCocone (i : (freeGenerators I).toSet)
    (F : d.cardinal.ord.ToType ⥤ Mon C) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬ IsMax j → relativeCellMaps.{w} (freeGenerators I)
      (F.map (homOfLE (Order.le_succ j)))) :
    IsColimit ((coyoneda.obj (op i.1.left)).mapCocone (colimit.cocone F)) :=
  UniformRelativeSourceSmallness.mappedCanonicalCocone hI i d.cardinal (d.sourceI_bounds i) F hF

omit [LocallySmall.{w} C] in
/-- The entire original free-J cocone has its original source-Hom universal property. -/
def sourceJMappedCanonicalCocone (j : (freeGenerators J).toSet)
    (F : d.cardinal.ord.ToType ⥤ Mon C) [F.IsWellOrderContinuous]
    (hF : ∀ k, ¬ IsMax k → relativeCellMaps.{w} (freeGenerators J)
      (F.map (homOfLE (Order.le_succ k)))) :
    IsColimit ((coyoneda.obj (op j.1.left)).mapCocone (colimit.cocone F)) :=
  UniformRelativeSourceSmallness.mappedCanonicalCocone hJ j d.cardinal (d.sourceJ_bounds j) F hF

end FreeGenerationCardinal







end HomotopicalAlgebra.MonoidTransfer
