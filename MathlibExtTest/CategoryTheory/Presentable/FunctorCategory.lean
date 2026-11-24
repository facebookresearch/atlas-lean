/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.FunctorCategory
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.SingleObj

/-!
# Original functor-category local presentability contracts

The generic contract keeps all five universes independent. The actual
equivalence tests check both precomposition maps and all four unit/counit
components on the original categories. Empty, infinite and nonthin indices
exercise the same-cardinal theorem without an index-cardinality bound.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uM vM

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FunctorCategoryTest

variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]

example (s : Functor.EssentialIndexData.{w} D M) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ :=
  s.isCardinalLocallyPresentable κ

example (s : Functor.SmallIndexData.{w} D M) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ :=
  s.isCardinalLocallyPresentable κ

example [EssentiallySmall.{w} D] (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ :=
  Functor.isCardinalLocallyPresentable_of_essentiallySmall κ

example (s : Functor.EssentialIndexData.{w} D M) {F G : D ⥤ M}
    (α : F ⟶ G) (d : s.index) :
    ((s.equivalence.congrLeft (E := M)).functor.map α).app d =
      α.app (s.equivalence.inverse.obj d) :=
  s.small_component α d

example (s : Functor.EssentialIndexData.{w} D M) {F G : s.index ⥤ M}
    (α : F ⟶ G) (d : D) :
    ((s.equivalence.congrLeft (E := M)).inverse.map α).app d =
      α.app (s.equivalence.functor.obj d) :=
  s.original_component α d

example (s : Functor.EssentialIndexData.{w} D M) (F : D ⥤ M) (d : D) :
    (((s.equivalence.congrLeft (E := M)).unitIso.hom.app F).app d) =
      F.map (s.equivalence.unitIso.hom.app d) := by
  simp [Equivalence.congrLeft]

example (s : Functor.EssentialIndexData.{w} D M) (F : D ⥤ M) (d : D) :
    (((s.equivalence.congrLeft (E := M)).unitIso.inv.app F).app d) =
      F.map (s.equivalence.unitIso.inv.app d) := by
  simp [Equivalence.congrLeft]

example (s : Functor.EssentialIndexData.{w} D M) (F : s.index ⥤ M) (d : s.index) :
    (((s.equivalence.congrLeft (E := M)).counitIso.hom.app F).app d) =
      F.map (s.equivalence.counitIso.hom.app d) := by
  simp [Equivalence.congrLeft]

example (s : Functor.EssentialIndexData.{w} D M) (F : s.index ⥤ M) (d : s.index) :
    (((s.equivalence.congrLeft (E := M)).counitIso.inv.app F).app d) =
      F.map (s.equivalence.counitIso.inv.app d) := by
  simp [Equivalence.congrLeft]

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

example : IsCardinalLocallyPresentable (Discrete PEmpty ⥤ Type) Cardinal.aleph0.{0} :=
  Functor.isCardinalLocallyPresentable_of_essentiallySmall _

example : IsCardinalLocallyPresentable (ℕ ⥤ Type) Cardinal.aleph0.{0} :=
  Functor.isCardinalLocallyPresentable_of_essentiallySmall _

example : IsCardinalLocallyPresentable (SingleObj ℕ ⥤ Type) Cardinal.aleph0.{0} :=
  Functor.isCardinalLocallyPresentable_of_essentiallySmall _

/-- Raising the original index object and Hom universes retains the same
countable cardinal and the original infinite diagram carrier. -/
example : IsCardinalLocallyPresentable (Discrete (ULift.{1} ℕ) ⥤ Type) Cardinal.aleph0.{0} :=
  Functor.isCardinalLocallyPresentable_of_essentiallySmall _

end Concrete

end CategoryTheory.FunctorCategoryTest
