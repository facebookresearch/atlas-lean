/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Independent sizes for original ordinary diagram categories

The index object, index Hom, coefficient object, coefficient Hom and working
universes remain independent. The small-index interface records the original
size proofs. The essential interface records a genuine working-small index
equivalence and returns to the original functor category. Limits, coproducts,
products and model structures are not included in this size interface.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uM vM

namespace CategoryTheory.Functor

variable (D : Type uD) [Category.{vD} D] (M : Type uM) [Category.{vM} M]

/-- The simple entry keeps the original index and coefficient size dictionaries. -/
structure SmallIndexData : Prop where
  smallIndex : Small.{w} D
  locallySmallIndex : LocallySmall.{w} D
  locallySmallCoefficient : LocallySmall.{w} M

/-- The essential entry keeps a genuine small-model equivalence for the original index. -/
structure EssentialIndexData where
  /-- The actual representative index carrier in the working universe. -/
  index : Type w
  [indexCategory : SmallCategory index]
  /-- A genuine equivalence from the original index category to its representatives. -/
  equivalence : @Equivalence D index _ indexCategory
  locallySmallCoefficient : LocallySmall.{w} M

attribute [instance] EssentialIndexData.indexCategory

namespace SmallIndexData

variable {D M}

/-- Native shrinking supplies an actual small index without changing the original category. -/
def toEssential (s : SmallIndexData.{w} D M) : EssentialIndexData.{w} D M := by
  letI : Small.{w} D := s.smallIndex
  letI : LocallySmall.{w} D := s.locallySmallIndex
  letI : EssentiallySmall.{w} D := inferInstance
  exact
    { index := SmallModel.{w} D
      indexCategory := inferInstance
      equivalence := equivSmallModel.{w} D
      locallySmallCoefficient := s.locallySmallCoefficient }

end SmallIndexData

namespace EssentialIndexData

variable {D M}

/-- This opt-in value uses the actual native equivalence supplied by essential smallness. -/
def ofEssentiallySmall [EssentiallySmall.{w} D] [LocallySmall.{w} M] :
    EssentialIndexData.{w} D M where
  index := SmallModel.{w} D
  indexCategory := inferInstance
  equivalence := equivSmallModel.{w} D
  locallySmallCoefficient := inferInstance

/-- Local index smallness follows from the same actual equivalence. -/
theorem locallySmallIndex (s : EssentialIndexData.{w} D M) : LocallySmall.{w} D := by
  let : SmallCategory s.index := s.indexCategory
  exact locallySmall_of_faithful s.equivalence.functor

/-- A full original transformation is determined by the components on the small model. -/
theorem component_ext (s : EssentialIndexData.{w} D M)
    {F G : D ⥤ M} {α β : F ⟶ G}
    (h : ∀ d : s.index, α.app (s.equivalence.inverse.obj d) =
      β.app (s.equivalence.inverse.obj d)) : α = β := by
  let : SmallCategory s.index := s.indexCategory
  apply ((s.equivalence.congrLeft (E := M)).functor).map_injective
  apply NatTrans.ext
  funext d
  exact h d

/-- Native precomposition retains every original natural-transformation component. -/
theorem small_component (s : EssentialIndexData.{w} D M)
    {F G : D ⥤ M} (α : F ⟶ G) (d : s.index) :
    (((s.equivalence.congrLeft (E := M)).functor).map α).app d =
      α.app (s.equivalence.inverse.obj d) := rfl

/-- The inverse precomposition retains the actual small-side component at the given object. -/
theorem original_component (s : EssentialIndexData.{w} D M)
    {F G : s.index ⥤ M} (α : F ⟶ G) (d : D) :
    (((s.equivalence.congrLeft (E := M)).inverse).map α).app d =
      α.app (s.equivalence.functor.obj d) := rfl

end EssentialIndexData

end CategoryTheory.Functor
