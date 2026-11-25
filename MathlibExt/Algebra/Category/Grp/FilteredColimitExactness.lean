/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Multiplicative exactness of filtered group colimits

Stagewise exactness passes to the maps induced by chosen group colimit cocones,
provided the three underlying set cocones are colimits. The indexing category's
object and morphism universes are independent of the group-value universe.

The native quotient-colimit specialization uses the native cocone descents and
the actual preservation of filtered colimits by the forgetful functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vJ uJ w v u

namespace GrpCat.FilteredColimits

/-- Chosen filtered group colimits preserve multiplicative exactness whenever
the three underlying set cocones are colimits. Both induced maps are the actual
descents given by the first two group colimit universal properties. -/
theorem isColimit_mulExact
    {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
    {D₁ D₂ D₃ : J ⥤ GrpCat.{w}}
    {c₁ : Cocone D₁} {c₂ : Cocone D₂} {c₃ : Cocone D₃}
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂)
    (t₁ : IsColimit ((forget GrpCat.{w}).mapCocone c₁))
    (t₂ : IsColimit ((forget GrpCat.{w}).mapCocone c₂))
    (t₃ : IsColimit ((forget GrpCat.{w}).mapCocone c₃))
    (α : D₁ ⟶ D₂) (β : D₂ ⟶ D₃)
    (hexact : ∀ j, Function.MulExact (α.app j).hom (β.app j).hom) :
    Function.MulExact (h₁.map c₂ α).hom (h₂.map c₃ β).hom := by
  intro x
  constructor
  · intro hx
    obtain ⟨j, xj, hxj⟩ := Types.jointly_surjective_of_isColimit t₂ x
    change c₂.ι.app j xj = x at hxj
    have heq : c₃.ι.app j (β.app j xj) = c₃.ι.app j 1 := by
      calc
        c₃.ι.app j (β.app j xj) = (h₂.map c₃ β) (c₂.ι.app j xj) :=
          (ConcreteCategory.congr_hom (h₂.ι_map c₃ β j) xj).symm
        _ = 1 := by rw [hxj]; exact hx
        _ = c₃.ι.app j 1 := (map_one (c₃.ι.app j).hom).symm
    obtain ⟨k, e, he⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' t₃ (β.app j xj) (1 : D₃.obj j)).mp heq
    change D₃.map e (β.app j xj) = D₃.map e 1 at he
    rw [map_one] at he
    have hk : β.app k (D₂.map e xj) = 1 :=
      (ConcreteCategory.congr_hom (β.naturality e) xj).trans he
    obtain ⟨z, hz⟩ := (hexact k (D₂.map e xj)).mp hk
    refine ⟨c₁.ι.app k z, ?_⟩
    calc
      (h₁.map c₂ α).hom (c₁.ι.app k z) = c₂.ι.app k (α.app k z) :=
        ConcreteCategory.congr_hom (h₁.ι_map c₂ α k) z
      _ = c₂.ι.app k (D₂.map e xj) := congrArg (c₂.ι.app k) hz
      _ = c₂.ι.app j xj := ConcreteCategory.congr_hom (c₂.w e) xj
      _ = x := hxj
  · rintro ⟨z, rfl⟩
    obtain ⟨j, zj, hzj⟩ := Types.jointly_surjective_of_isColimit t₁ z
    change c₁.ι.app j zj = z at hzj
    rw [← hzj]
    calc
      (h₂.map c₃ β).hom ((h₁.map c₂ α).hom (c₁.ι.app j zj)) =
          (h₂.map c₃ β).hom (c₂.ι.app j (α.app j zj)) :=
        congrArg (fun y => (h₂.map c₃ β).hom y)
          (ConcreteCategory.congr_hom (h₁.ι_map c₂ α j) zj)
      _ = c₃.ι.app j (β.app j (α.app j zj)) :=
        ConcreteCategory.congr_hom (h₂.ι_map c₃ β j) (α.app j zj)
      _ = c₃.ι.app j 1 :=
        congrArg (c₃.ι.app j) ((hexact j).apply_apply_eq_one zj)
      _ = 1 := map_one _

/-- The existing induced maps of native filtered quotient colimits preserve
stagewise multiplicative exactness for arbitrary groups. -/
theorem colimitMap_mulExact
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {D₁ D₂ D₃ : J ⥤ GrpCat.{max v u}}
    (α : D₁ ⟶ D₂) (β : D₂ ⟶ D₃)
    (hexact : ∀ j, Function.MulExact (α.app j).hom (β.app j).hom) :
    Function.MulExact
      ((colimitCoconeIsColimit D₁).map (colimitCocone D₂) α).hom
      ((colimitCoconeIsColimit D₂).map (colimitCocone D₃) β).hom := by
  let _ : PreservesFilteredColimitsOfSize.{v, v} (forget GrpCat.{max v u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max v u, max v u, v, v}
      (forget GrpCat.{max v u})
  have t₁ := isColimitOfPreserves (forget GrpCat.{max v u}) (colimitCoconeIsColimit D₁)
  have t₂ := isColimitOfPreserves (forget GrpCat.{max v u}) (colimitCoconeIsColimit D₂)
  have t₃ := isColimitOfPreserves (forget GrpCat.{max v u}) (colimitCoconeIsColimit D₃)
  exact isColimit_mulExact (colimitCoconeIsColimit D₁) (colimitCoconeIsColimit D₂)
    t₁ t₂ t₃ α β hexact

end GrpCat.FilteredColimits
