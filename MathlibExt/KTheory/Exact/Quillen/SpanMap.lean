/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.KTheory.Exact.Quillen.Basic
public import MathlibExt.CategoryTheory.ExactCategory.Functor

/-!
# Raw span maps for the Quillen Q-construction

For an additive exact functor `F` between exact categories, every admissible span
`X ←↞ M ↪ Y` has a raw image with apex `F.obj M` and legs `F.map` applied to each
leg. Leg admissibility is transported by unpacking the witnessing admissible exact
sequence and applying `F.map_admissibleExact`.

This packet supplies the raw span action, its transport of span isomorphisms, and the
per-hom-set quotient lift together with the identity-representative law. It supplies no
bundled functor on `QuillenQ`, no composition or pullback-comparison law, no
limit-preservation hypothesis, and no isomorphism-family, invariance, consumer, or test
development.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- Raw image of an admissible span under an additive exact functor. -/
def QuillenSpan.map (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : C} (S : QuillenSpan X Y) : QuillenSpan (F.obj X) (F.obj Y) where
  apex := F.obj S.apex
  l := F.map S.l
  r := F.map S.r
  wl := by obtain ⟨X, i, w, hS⟩ := S.wl; exact ⟨F.obj X, F.map i, _, F.map_admissibleExact _ hS⟩
  wr := by obtain ⟨Z, p, w, hS⟩ := S.wr; exact ⟨F.obj Z, F.map p, _, F.map_admissibleExact _ hS⟩


private theorem QuillenSpan.mapRawComputed (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : C} (S : QuillenSpan X Y) :
    QuillenSpan.map F S =
      { apex := F.obj S.apex
        l := F.map S.l
        r := F.map S.r
        wl := by
          obtain ⟨X, i, w, hS⟩ := S.wl
          exact ⟨F.obj X, F.map i, _, F.map_admissibleExact _ hS⟩
        wr := by
          obtain ⟨Z, q, w, hS⟩ := S.wr
          exact ⟨F.obj Z, F.map q, _, F.map_admissibleExact _ hS⟩ } := rfl

/-- The actual mapped span retains its complete original apex and mapped leg record. -/
theorem QuillenSpan.map_eq_raw (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : C} (S : QuillenSpan X Y) :
    QuillenSpan.map F S =
      { apex := F.obj S.apex
        l := F.map S.l
        r := F.map S.r
        wl := by
          obtain ⟨X, i, w, hS⟩ := S.wl
          exact ⟨F.obj X, F.map i, _, F.map_admissibleExact _ hS⟩
        wr := by
          obtain ⟨Z, q, w, hS⟩ := S.wr
          exact ⟨F.obj Z, F.map q, _, F.map_admissibleExact _ hS⟩ } :=
  QuillenSpan.mapRawComputed F S

/-- Apex accessor for the raw span map. -/
@[simp]
theorem QuillenSpan.map_apex (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : C} (S : QuillenSpan X Y) :
    (QuillenSpan.map F S).apex = F.obj S.apex :=
  rfl

/-- Left-leg accessor for the raw span map. -/
@[simp]
theorem QuillenSpan.map_l (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : C} (S : QuillenSpan X Y) :
    (QuillenSpan.map F S).l = F.map S.l :=
  rfl

/-- Right-leg accessor for the raw span map. -/
@[simp]
theorem QuillenSpan.map_r (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : C} (S : QuillenSpan X Y) :
    (QuillenSpan.map F S).r = F.map S.r :=
  rfl

/-- Transport of a span isomorphism along an additive exact functor. -/
noncomputable def QuillenSpan.mapIso (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : C} {S S' : QuillenSpan X Y} (e : S ≅ S') :
    QuillenSpan.map F S ≅ QuillenSpan.map F S' := by
  refine Span.mkIso (F.mapIso (Span.SpanBicat.apexIso e)) ?_ ?_
  · change F.map e.hom.hom ≫ F.map S'.l = F.map S.l
    rw [← F.map_comp, e.hom.hom_l]
  · change F.map e.hom.hom ≫ F.map S'.r = F.map S.r
    rw [← F.map_comp, e.hom.hom_r]

/-- Quotient-level span map on Quillen morphisms. -/
noncomputable def QuillenQ.mapSpanQuotient (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : QuillenQ C} (q : QuillenQHom X Y) :
    QuillenQHom ⟨F.obj X.obj⟩ ⟨F.obj Y.obj⟩ :=
  Quotient.map (fun S => QuillenSpan.map F S) (fun S₁ S₂ h => by
    obtain ⟨e⟩ := h
    exact ⟨QuillenSpan.mapIso F e⟩) q

/-- Representative computation for the quotient span map. -/
@[simp]
theorem QuillenQ.mapSpanQuotient_mk (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : QuillenQ C} (S : QuillenSpan X.obj Y.obj) :
    QuillenQ.mapSpanQuotient F (QuillenQ.mkHom S) =
      QuillenQ.mkHom (QuillenSpan.map F S) :=
  rfl

/-- The mapped identity representative presents the identity morphism. -/
theorem QuillenQ.mapSpanQuotient_id_rep (F : C ⥤ D) [F.Additive] [F.IsExact]
    (X : QuillenQ C) :
    QuillenQ.mapSpanQuotient F
        (QuillenQ.mkHom (Span.id (c := X.obj) : QuillenSpan X.obj X.obj)) =
      𝟙 (⟨F.obj X.obj⟩ : QuillenQ D) := by
  rw [QuillenQ.mapSpanQuotient_mk, ← mkHom_id]
  apply QuillenQ.mkHom_sound
  refine Span.mkIso (Iso.refl _) ?_ ?_
  · change 𝟙 (F.obj X.obj) ≫ 𝟙 (F.obj X.obj) = F.map (𝟙 X.obj)
    rw [Category.id_comp, F.map_id]
  · change 𝟙 (F.obj X.obj) ≫ 𝟙 (F.obj X.obj) = F.map (𝟙 X.obj)
    rw [Category.id_comp, F.map_id]

end AlgebraicKTheory
