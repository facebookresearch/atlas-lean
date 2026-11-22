/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Presentable.SmallFamily
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Native small-object arguments from proved presentable sources

The actual presentability ranks of a small family of original sources admit
a common regular bound. At its original ordinal, coyoneda preserves the
required transfinite cell colimits. Hence the same actual arrows admit the
native functorial small-object construction. Local presentability supplies
the source presentability; it is not an assumed model or factorization.
-/

noncomputable section
universe w v u t
open CategoryTheory Limits Opposite MorphismProperty

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  [LocallySmall.{w} C] {ι : Type t} [Small.{w} ι]
  {A B : ι → C} (f : ∀ i, A i ⟶ B i)

/-- Genuine source presentability proves all native small-object colimit hypotheses. -/
theorem ofHoms_hasSmallObjectArgument_of_presentable [∀ i, IsPresentable.{w} (A i)] :
    HasSmallObjectArgument.{w} (ofHoms f) := by
  obtain ⟨κ, hκ, hA⟩ := exists_cardinalPresentable_small_family A
  let _ : Fact κ.IsRegular := hκ
  have hκ0 : Nonempty κ.ord.ToType := by
    apply Cardinal.mk_ne_zero_iff.mp
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact (lt_of_lt_of_le Cardinal.aleph0_pos (Cardinal.IsRegular.aleph0_le Fact.out)).ne'
  let _ : Nonempty κ.ord.ToType := hκ0
  let _ : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  refine ⟨κ, inferInstance, inferInstance, ?_⟩
  refine { preservesColimit := ?_ }
  intro X Y U V i hi g hg
  obtain ⟨j⟩ := hi
  let _ : IsCardinalPresentable (A j) κ := hA j
  let _ : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (Opposite.op (A j))) :=
    preservesColimitsOfShape_of_isCardinalPresentable _ κ _
  infer_instance

/-- In a locally presentable carrier every small actual arrow family permits the same-universe construction. -/
theorem ofHoms_hasSmallObjectArgument_of_locallyPresentable [IsLocallyPresentable.{w} C] :
    HasSmallObjectArgument.{w} (ofHoms f) :=
  ofHoms_hasSmallObjectArgument_of_presentable f

/-- The actual functorial factorization on the original carrier follows from its source presentability. -/
def ofHomsFunctorialFactorizationData [IsLocallyPresentable.{w} C] :
    FunctorialFactorizationData (ofHoms f).rlp.llp (ofHoms f).rlp := by
  let _ : HasSmallObjectArgument.{w} (ofHoms f) :=
    ofHoms_hasSmallObjectArgument_of_locallyPresentable f
  exact functorialFactorizationData _ _

/-- The original small family has a genuine weak factorization system from the proved native construction. -/
theorem ofHoms_isWeakFactorizationSystem [IsLocallyPresentable.{w} C] :
    IsWeakFactorizationSystem (ofHoms f).rlp.llp (ofHoms f).rlp := by
  let _ : HasFunctorialFactorization (ofHoms f).rlp.llp (ofHoms f).rlp :=
    ⟨⟨ofHomsFunctorialFactorizationData f⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

end CategoryTheory.MorphismProperty
