/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.SmallObject.PresentableSources

/-!
# Fixed original source ranks for actual small-object constructions

A small actual arrow family whose original sources are presentable at
the specified regular rank satisfies the native transfinite-colimit
conditions at that same rank. The original source ordinal is nonempty
and has its native least stage. These are proofs of the small-object
hypotheses, not assumed factorization or model outcomes.
-/

noncomputable section
universe w v u t
open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  {ι : Type t} [Small.{w} ι] {A B : ι → C} (f : ∀ i, A i ⟶ B i)
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- The genuine original regular source-rank ordinal has a least stage. -/
@[instance_reducible]
def sourceRankOrderBot : OrderBot κ.ord.ToType := by
  have h : Nonempty κ.ord.ToType := by
    apply Cardinal.mk_ne_zero_iff.mp
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact (lt_of_lt_of_le Cardinal.aleph0_pos (Cardinal.IsRegular.aleph0_le Fact.out)).ne'
  let _ : Nonempty κ.ord.ToType := h
  exact WellFoundedLT.toOrderBot _

/-- Actual source presentability verifies every original transfinite-cell colimit hypothesis at the specified rank. -/
theorem ofHoms_isCardinalForSmallObjectArgument [OrderBot κ.ord.ToType]
    [∀ i, IsCardinalPresentable (A i) κ] : IsCardinalForSmallObjectArgument (ofHoms f) κ where
  preservesColimit {X Y U V} i hi g hg := by
    obtain ⟨j⟩ := hi
    let _ : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (Opposite.op (A j))) :=
      preservesColimitsOfShape_of_isCardinalPresentable _ κ _
    infer_instance

/-- The same original fixed source rank gives a genuine native small-object argument. -/
theorem ofHoms_hasSmallObjectArgument_atCardinal [∀ i, IsCardinalPresentable (A i) κ] :
    HasSmallObjectArgument.{w} (ofHoms f) := by
  let _ : OrderBot κ.ord.ToType := sourceRankOrderBot κ
  exact ⟨κ, inferInstance, inferInstance, ofHoms_isCardinalForSmallObjectArgument f κ⟩

/-- Construct the actual native functorial factors at the specified original source rank and ordinal. -/
def ofHomsFunctorialFactorizationAtCardinal [∀ i, IsCardinalPresentable (A i) κ] :
    FunctorialFactorizationData (ofHoms f).rlp.llp (ofHoms f).rlp := by
  let _ : OrderBot κ.ord.ToType := sourceRankOrderBot κ
  let _ : IsCardinalForSmallObjectArgument (ofHoms f) κ := ofHoms_isCardinalForSmallObjectArgument f κ
  exact SmallObject.functorialFactorizationData (ofHoms f) κ

end CategoryTheory.MorphismProperty
