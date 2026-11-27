/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeLifting
public import Mathlib.CategoryTheory.Retract

/-!
# Relative projectivity and retracts of free objects

An object is projective relative to a functor `U` when maps from it lift through every morphism
split after applying `U`. For an adjunction `F ⊣ U`, objects of the form `F.obj X` have this
property, as do their retracts. Relative projectivity is equivalent to splitting the counit, and
hence to being a retract of a free object.
-/

@[expose] public section

open CategoryTheory
universe uC vC uD vD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

namespace Functor

/-- Every map out of `P` lifts through a morphism split after applying `U`. -/
def IsRelativeProjective (U : D ⥤ C) (P : D) : Prop :=
  ∀ {Y Z : D} (g : Y ⟶ Z) (_s : SplitEpi (U.map g)) (f : P ⟶ Z),
    ∃ l : P ⟶ Y, l ≫ g = f

/-- Relative projectivity is equivalent to surjectivity of precomposition for every `U`-split morphism. -/
theorem isRelativeProjective_iff_postcomp_surjective (U : D ⥤ C) (P : D) :
    U.IsRelativeProjective P ↔
      ∀ {Y Z : D} (g : Y ⟶ Z), IsSplitEpi (U.map g) →
        Function.Surjective (fun l : P ⟶ Y => l ≫ g) := by
  constructor
  · intro h Y Z g hs f
    obtain ⟨s⟩ := hs.exists_splitEpi
    exact h g s f
  · intro h Y Z g s f
    exact h g (IsSplitEpi.mk' s) f

/-- Relative projectivity is preserved by retracts. -/
theorem IsRelativeProjective.of_retract {U : D ⥤ C} {P Q : D}
    (hQ : U.IsRelativeProjective Q) (r : Retract P Q) : U.IsRelativeProjective P := by
  intro Y Z g s f
  obtain ⟨l, hl⟩ := hQ g s (r.r ≫ f)
  refine ⟨r.i ≫ l, ?_⟩
  rw [Category.assoc, hl, ← Category.assoc, r.retract, Category.id_comp]

end Functor

namespace Adjunction

variable {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U)
include adj

/-- The unit is a section of the counit after applying the right adjoint. -/
def mapCounitSplitEpi (P : D) : SplitEpi (U.map (adj.counit.app P)) where
  section_ := adj.unit.app (U.obj P)
  id := adj.right_triangle_components P

/-- The unit component is the section of the mapped counit. -/
@[simp]
theorem mapCounitSplitEpi_section (P : D) :
    (adj.mapCounitSplitEpi P).section_ = adj.unit.app (U.obj P) := rfl

/-- Every free adjunction object is relatively projective by the constructed adjoint lift. -/
theorem isRelativeProjective_obj (X : C) : U.IsRelativeProjective (F.obj X) := by
  intro Y Z g s f
  exact ⟨adj.liftOfSplitEpi g s f, adj.liftOfSplitEpi_comp g s f⟩

/-- Lift the identity to construct a section of the counit from the lifting property. -/
noncomputable def counitSplitEpiOfRelativeProjective (P : D) (h : U.IsRelativeProjective P) :
    SplitEpi (adj.counit.app P) where
  section_ := Classical.choose (h (adj.counit.app P) (adj.mapCounitSplitEpi P) (𝟙 P))
  id := Classical.choose_spec (h (adj.counit.app P) (adj.mapCounitSplitEpi P) (𝟙 P))

/-- The counit section defines a retract of the free object on the restricted coefficient. -/
noncomputable def counitRetractOfRelativeProjective (P : D) (h : U.IsRelativeProjective P) :
    Retract P (F.obj (U.obj P)) where
  i := (adj.counitSplitEpiOfRelativeProjective P h).section_
  r := adj.counit.app P
  retract := (adj.counitSplitEpiOfRelativeProjective P h).id

/-- The constructed retraction retains the prescribed counit. -/
@[simp]
theorem counitRetractOfRelativeProjective_r (P : D) (h : U.IsRelativeProjective P) :
    (adj.counitRetractOfRelativeProjective P h).r = adj.counit.app P := rfl

/-- Relative projectivity is exactly splitting of the canonical counit in the category. -/
theorem isRelativeProjective_iff_counit_isSplitEpi (P : D) :
    U.IsRelativeProjective P ↔ IsSplitEpi (adj.counit.app P) := by
  constructor
  · intro h
    exact IsSplitEpi.mk' (adj.counitSplitEpiOfRelativeProjective P h)
  · intro h
    obtain ⟨s⟩ := h.exists_splitEpi
    exact Functor.IsRelativeProjective.of_retract (adj.isRelativeProjective_obj (U.obj P))
      { i := s.section_, r := adj.counit.app P, retract := s.id }

/-- Relative projectivity is equivalent to the existence of a section of the counit. -/
theorem isRelativeProjective_iff_counit_section (P : D) :
    U.IsRelativeProjective P ↔
      ∃ s : P ⟶ F.obj (U.obj P), s ≫ adj.counit.app P = 𝟙 P := by
  constructor
  · intro h
    exact ⟨(adj.counitSplitEpiOfRelativeProjective P h).section_,
      (adj.counitSplitEpiOfRelativeProjective P h).id⟩
  · rintro ⟨s, hs⟩
    exact Functor.IsRelativeProjective.of_retract (adj.isRelativeProjective_obj (U.obj P))
      { i := s, r := adj.counit.app P, retract := hs }

/-- An object is relatively projective exactly when it is a retract of a free adjunction object. -/
theorem isRelativeProjective_iff_retract_free (P : D) :
    U.IsRelativeProjective P ↔ ∃ X : C, Nonempty (Retract P (F.obj X)) := by
  constructor
  · intro h
    exact ⟨U.obj P, ⟨adj.counitRetractOfRelativeProjective P h⟩⟩
  · rintro ⟨X, ⟨r⟩⟩
    exact Functor.IsRelativeProjective.of_retract (adj.isRelativeProjective_obj X) r

end Adjunction
end CategoryTheory
