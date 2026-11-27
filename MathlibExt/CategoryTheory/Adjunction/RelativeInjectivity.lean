/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeProjectivity
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# Relative injectivity and retracts of cofree objects

An object is injective relative to a functor `F` when maps into it extend across every morphism
split after applying `F`. Opposite categories identify this with relative projectivity. For an
adjunction `F ⊣ U`, cofree objects and their retracts are relatively injective; the property is
equivalent to splitting the unit.
-/

@[expose] public section

open CategoryTheory Opposite
universe uC vC uD vD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

namespace Functor

/-- Every map into `P` extends across each arrow with an F-retraction. -/
def IsRelativeInjective (F : C ⥤ D) (P : C) : Prop :=
  ∀ {X Y : C} (g : X ⟶ Y) (_s : SplitMono (F.map g)) (f : X ⟶ P),
    ∃ e : Y ⟶ P, g ≫ e = f

/-- Relative injectivity is relative projectivity in the opposite category. -/
theorem isRelativeInjective_iff_op_isRelativeProjective (F : C ⥤ D) (P : C) :
    F.IsRelativeInjective P ↔ F.op.IsRelativeProjective (op P) := by
  constructor
  · intro h X Y g s f
    let t : SplitMono (F.map g.unop) :=
      { retraction := s.section_.unop
        id := Quiver.Hom.op_inj (by simp) }
    obtain ⟨e, he⟩ := h g.unop t f.unop
    refine ⟨e.op, ?_⟩
    exact Quiver.Hom.unop_inj (by simpa using he)
  · intro h X Y g s f
    obtain ⟨e, he⟩ := h g.op s.op f.op
    refine ⟨e.unop, ?_⟩
    exact Quiver.Hom.op_inj (by simpa using he)

/-- The data-based extension property is equivalently precomposition surjectivity. -/
theorem isRelativeInjective_iff_precomp_surjective (F : C ⥤ D) (P : C) :
    F.IsRelativeInjective P ↔
      ∀ {X Y : C} (g : X ⟶ Y), IsSplitMono (F.map g) →
        Function.Surjective (fun e : Y ⟶ P => g ≫ e) := by
  constructor
  · intro h X Y g hs f
    obtain ⟨s⟩ := hs.exists_splitMono
    exact h g s f
  · intro h X Y g s f
    exact h g (IsSplitMono.mk' s) f

/-- Relative injectivity is preserved by retracts. -/
theorem IsRelativeInjective.of_retract {F : C ⥤ D} {P Q : C}
    (hQ : F.IsRelativeInjective Q) (r : Retract P Q) : F.IsRelativeInjective P := by
  apply (isRelativeInjective_iff_op_isRelativeProjective F P).mpr
  exact Functor.IsRelativeProjective.of_retract
    ((isRelativeInjective_iff_op_isRelativeProjective F Q).mp hQ) r.op

end Functor

namespace Adjunction

variable {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U)

include adj

/-- The counit retracts the mapped unit by the left triangle. -/
def mapUnitSplitMono (P : C) : SplitMono (F.map (adj.unit.app P)) where
  retraction := adj.counit.app (F.obj P)
  id := adj.left_triangle_components P

/-- The retraction of the mapped unit is precisely the counit component. -/
@[simp]
theorem mapUnitSplitMono_retraction (P : C) :
    (adj.mapUnitSplitMono P).retraction = adj.counit.app (F.obj P) := rfl

/-- Every cofree object is relatively injective by opposite adjunction projectivity. -/
theorem isRelativeInjective_obj (Y : D) : F.IsRelativeInjective (U.obj Y) := by
  apply (Functor.isRelativeInjective_iff_op_isRelativeProjective F (U.obj Y)).mpr
  exact adj.op.isRelativeProjective_obj (Opposite.op Y)

/-- Extending the identity gives a retraction of the unit. -/
noncomputable def unitSplitMonoOfRelativeInjective (P : C) (h : F.IsRelativeInjective P) :
    SplitMono (adj.unit.app P) where
  retraction := Classical.choose (h (adj.unit.app P) (adj.mapUnitSplitMono P) (𝟙 P))
  id := Classical.choose_spec (h (adj.unit.app P) (adj.mapUnitSplitMono P) (𝟙 P))

/-- A retraction of the unit defines a retract of the cofree object. -/
noncomputable def unitRetractOfRelativeInjective (P : C) (h : F.IsRelativeInjective P) :
    Retract P (U.obj (F.obj P)) where
  i := adj.unit.app P
  r := (adj.unitSplitMonoOfRelativeInjective P h).retraction
  retract := (adj.unitSplitMonoOfRelativeInjective P h).id

/-- The constructed retract preserves the prescribed unit inclusion. -/
@[simp]
theorem unitRetractOfRelativeInjective_i (P : C) (h : F.IsRelativeInjective P) :
    (adj.unitRetractOfRelativeInjective P h).i = adj.unit.app P := rfl

/-- Relative injectivity is splitting of the canonical unit. -/
theorem isRelativeInjective_iff_unit_isSplitMono (P : C) :
    F.IsRelativeInjective P ↔ IsSplitMono (adj.unit.app P) := by
  constructor
  · intro h
    exact IsSplitMono.mk' (adj.unitSplitMonoOfRelativeInjective P h)
  · intro h
    obtain ⟨s⟩ := h.exists_splitMono
    exact Functor.IsRelativeInjective.of_retract (adj.isRelativeInjective_obj (F.obj P))
      { i := adj.unit.app P, r := s.retraction, retract := s.id }

/-- Relative injectivity is equivalent to the existence of a retraction of the unit. -/
theorem isRelativeInjective_iff_unit_retraction (P : C) :
    F.IsRelativeInjective P ↔
      ∃ r : U.obj (F.obj P) ⟶ P, adj.unit.app P ≫ r = 𝟙 P := by
  constructor
  · intro h
    exact ⟨(adj.unitSplitMonoOfRelativeInjective P h).retraction,
      (adj.unitSplitMonoOfRelativeInjective P h).id⟩
  · rintro ⟨r, hr⟩
    exact Functor.IsRelativeInjective.of_retract (adj.isRelativeInjective_obj (F.obj P))
      { i := adj.unit.app P, r := r, retract := hr }

/-- Relative injectivity is equivalent to being a retract of a cofree object. -/
theorem isRelativeInjective_iff_retract_cofree (P : C) :
    F.IsRelativeInjective P ↔ ∃ Y : D, Nonempty (Retract P (U.obj Y)) := by
  constructor
  · intro h
    exact ⟨F.obj P, ⟨adj.unitRetractOfRelativeInjective P h⟩⟩
  · rintro ⟨Y, ⟨r⟩⟩
    exact Functor.IsRelativeInjective.of_retract (adj.isRelativeInjective_obj Y) r

end Adjunction
end CategoryTheory
