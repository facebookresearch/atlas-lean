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

public import MathlibExt.KTheory.Exact.Quillen.SpanMapComp

/-!
# Bundled exact-functor maps on the Quillen Q-construction

For an additive exact functor `F`, the per-hom quotient lift
`QuillenQ.mapSpanQuotient` assembles into a bundled functor `QuillenQ.map`,
with representative computation `QuillenQ.map_mk` and strict
identity/composition laws `QuillenQ.map_id` and `QuillenQ.map_comp`.
The identity and composite functors agree on apex/legs definitionally;
only admissibility proof fields differ, closed inline by span isos with
`Iso.refl`. No equivalence invariance, G-theory consumer, test, root,
pullback, nerve, realization, Q/S, S-construction, spectrum, or BGT content.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Bundled exact-functor map on `QuillenQ`. -/
noncomputable def QuillenQ.map (F : C ⥤ D) [F.Additive] [F.IsExact] :
    QuillenQ C ⥤ QuillenQ D where
  obj X := ⟨F.obj X.obj⟩
  map f := QuillenQ.mapSpanQuotient F f
  map_id X := QuillenQ.mapSpanQuotient_id_rep F X
  map_comp {X Y Z} f g := by
    refine Quotient.inductionOn f ?_
    intro S₁
    refine Quotient.inductionOn g ?_
    intro S₂
    change QuillenQ.mapSpanQuotient F
        (quillenComp (QuillenQ.mkHom S₁) (QuillenQ.mkHom S₂)) =
      quillenComp (QuillenQ.mapSpanQuotient F (QuillenQ.mkHom S₁))
        (QuillenQ.mapSpanQuotient F (QuillenQ.mkHom S₂))
    rw [mkHom_comp, QuillenQ.mapSpanQuotient_comp_rep,
      QuillenQ.mapSpanQuotient_mk, QuillenQ.mapSpanQuotient_mk]

/-- Representative computation for the bundled functor map. -/
@[simp]
theorem QuillenQ.map_mk (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : QuillenQ C} (S : QuillenSpan X.obj Y.obj) :
    (QuillenQ.map F).map (QuillenQ.mkHom S) =
      QuillenQ.mkHom (QuillenSpan.map F S) :=
  QuillenQ.mapSpanQuotient_mk F S

/-- Strict identity law for the bundled functor map. -/
theorem QuillenQ.map_id : QuillenQ.map (𝟭 C) = 𝟭 (QuillenQ C) := by
  have h_obj : ∀ X : QuillenQ C,
      (QuillenQ.map (𝟭 C)).obj X = (𝟭 (QuillenQ C)).obj X :=
    fun X => QuillenQ.mk_get X
  refine CategoryTheory.Functor.ext h_obj (fun X Y f => ?_)
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  change (QuillenQ.map (𝟭 C)).map f = 𝟙 _ ≫ (𝟭 (QuillenQ C)).map f ≫ 𝟙 _
  refine Quotient.inductionOn f ?_
  intro S
  simp only [Functor.id_map, Category.id_comp, Category.comp_id]
  apply QuillenQ.mkHom_sound
  exact Span.mkIso (Iso.refl _) (by simp) (by simp)

/-- Strict composition law for the bundled functor map. -/
theorem QuillenQ.map_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    QuillenQ.map (F ⋙ G) = QuillenQ.map F ⋙ QuillenQ.map G := by
  have h_obj : ∀ X : QuillenQ C,
      (QuillenQ.map (F ⋙ G)).obj X
        = ((QuillenQ.map F ⋙ QuillenQ.map G)).obj X :=
    fun X => rfl
  refine CategoryTheory.Functor.ext h_obj (fun X Y f => ?_)
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  change (QuillenQ.map (F ⋙ G)).map f
      = 𝟙 _ ≫ (QuillenQ.map F ⋙ QuillenQ.map G).map f ≫ 𝟙 _
  refine Quotient.inductionOn f ?_
  intro S
  simp only [Functor.comp_map, Category.id_comp, Category.comp_id]
  apply QuillenQ.mkHom_sound
  exact Span.mkIso (Iso.refl _)
    (by change 𝟙 _ ≫ G.map (F.map S.l) = G.map (F.map S.l)
        rw [Category.id_comp])
    (by change 𝟙 _ ≫ G.map (F.map S.r) = G.map (F.map S.r)
        rw [Category.id_comp])

end AlgebraicKTheory


noncomputable section

open CategoryTheory

universe vObjectSource uObjectSource vObjectTarget uObjectTarget

namespace AlgebraicKTheory

variable {C : Type uObjectSource} [Category.{vObjectSource} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  {D : Type uObjectTarget} [Category.{vObjectTarget} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

private theorem originalQuillenQMapObjectValueComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] (X : QuillenQ C) :
    (QuillenQ.map F).obj X = (⟨F.obj X.obj⟩ : QuillenQ D) := rfl

/-- The WHOLE original Q-map object is the SAME original image object,
with all four independent source and target universe roles retained. -/
theorem QuillenQ.map_obj_value
    (F : C ⥤ D) [F.Additive] [F.IsExact] (X : QuillenQ C) :
    (QuillenQ.map F).obj X = (⟨F.obj X.obj⟩ : QuillenQ D) :=
  originalQuillenQMapObjectValueComputed F X

end AlgebraicKTheory

end
