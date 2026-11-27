/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Presheaf
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

example {S : Type w} [SmallCategory S] (s : D ≌ S) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ := by
  let : EssentiallySmall.{w} D := EssentiallySmall.mk' s
  infer_instance

example [Small.{w} D] [LocallySmall.{w} D] (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ :=
  inferInstance

example [EssentiallySmall.{w} D] (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ :=
  inferInstance

example {S : Type w} [SmallCategory S] (s : D ≌ S) {F G : D ⥤ M}
    (α : F ⟶ G) (d : S) :
    ((s.congrLeft (E := M)).functor.map α).app d =
      α.app (s.inverse.obj d) :=
  rfl

example {S : Type w} [SmallCategory S] (s : D ≌ S) {F G : S ⥤ M}
    (α : F ⟶ G) (d : D) :
    ((s.congrLeft (E := M)).inverse.map α).app d =
      α.app (s.functor.obj d) :=
  rfl

example {S : Type w} [SmallCategory S] (s : D ≌ S) (F : D ⥤ M) (d : D) :
    (((s.congrLeft (E := M)).unitIso.hom.app F).app d) =
      F.map (s.unitIso.hom.app d) := by
  simp [Equivalence.congrLeft]

example {S : Type w} [SmallCategory S] (s : D ≌ S) (F : D ⥤ M) (d : D) :
    (((s.congrLeft (E := M)).unitIso.inv.app F).app d) =
      F.map (s.unitIso.inv.app d) := by
  simp [Equivalence.congrLeft]

example {S : Type w} [SmallCategory S] (s : D ≌ S) (F : S ⥤ M) (d : S) :
    (((s.congrLeft (E := M)).counitIso.hom.app F).app d) =
      F.map (s.counitIso.hom.app d) := by
  simp [Equivalence.congrLeft]

example {S : Type w} [SmallCategory S] (s : D ≌ S) (F : S ⥤ M) (d : S) :
    (((s.congrLeft (E := M)).counitIso.inv.app F).app d) =
      F.map (s.counitIso.inv.app d) := by
  simp [Equivalence.congrLeft]

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

example : IsCardinalLocallyPresentable (Discrete PEmpty ⥤ Type) Cardinal.aleph0.{0} :=
  inferInstance

example : IsCardinalLocallyPresentable (ℕ ⥤ Type) Cardinal.aleph0.{0} :=
  inferInstance

example : IsCardinalLocallyPresentable (SingleObj ℕ ⥤ Type) Cardinal.aleph0.{0} :=
  inferInstance

/-- Raising the original index object and Hom universes retains the same
countable cardinal and the original infinite diagram carrier. -/
example : IsCardinalLocallyPresentable (Discrete (ULift.{1} ℕ) ⥤ Type) Cardinal.aleph0.{0} :=
  inferInstance

end Concrete

end CategoryTheory.FunctorCategoryTest
