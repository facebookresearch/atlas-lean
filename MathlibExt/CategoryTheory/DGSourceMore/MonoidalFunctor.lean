/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Functor.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: module/namespace paths are adapted for Atlas, and the
universes of the final independent section are redeclared explicitly.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Monoidal functors: tensor comparisons, transport, and conjugates

The tensorator of a lax monoidal functor is natural in its right argument, giving a
square between left tensoring and the functor.

For an oplax monoidal functor with invertible unit comparison, its tensor comparisons at the
unit are invertible. Invertibility in either argument propagates across any colimit preserved
by the two functors in the corresponding tensor comparison. This reduces tensor compatibility
for objects built from coproducts and cokernels to the unit case.

A lax monoidal structure transports along a natural isomorphism of functors
(`CategoryTheory.Functor.LaxMonoidal.transport`), in the same way as Mathlib's
`CategoryTheory.Functor.Monoidal.transport` transports a monoidal structure. This is how a
functor isomorphic to a composite of lax monoidal functors inherits a lax monoidal structure.

An oplax monoidal structure passes to a retract `G` of an oplax monoidal functor `F` whose
idempotent does not change the counit and the comultiplication followed by the retraction
(`CategoryTheory.Functor.OplaxMonoidal.ofRetract`).  This is how normalized chains, a natural
direct summand of all chains, inherit the Alexander–Whitney comultiplication.

For two monoidal adjunctions `F₁ ⊣ G₁` and `F₂ ⊣ G₂`, where the right adjoints are lax monoidal
and the left adjoints carry the induced oplax monoidal structures, a natural transformation
`σ : F₂ ⟶ F₁` whose conjugate `G₁ ⟶ G₂` is a monoidal natural transformation is compatible with
the oplax structures (`CategoryTheory.Adjunction.app_tensorUnit_comp_η_of_conjugateEquiv` and
`CategoryTheory.Adjunction.app_tensor_comp_δ_of_conjugateEquiv`). This is how the comparison
isomorphisms between left adjoints, such as the composition isomorphism of pullback functors, are
shown to respect their oplax monoidal structures from the corresponding facts about the right
adjoints.

Along a monoidal adjunction `F ⊣ G`, transposition carries the oplax unit and tensor comparisons
of `F` to the lax ones of `G` (`CategoryTheory.Adjunction.homEquiv_η_comp` and
`CategoryTheory.Adjunction.homEquiv_δ_comp_tensorHom_comp`). These are the equations by which
transposition preserves morphisms of monoid objects.

**Doctrinal adjunction** for tensorators: if `F ⊣ G` is an adjunction between lax monoidal
functors whose unit and counit are compatible with the tensorators, then the tensorator of the
left adjoint `F` is invertible (`CategoryTheory.Adjunction.isIso_μ_of_unit_of_counit`), and its
inverse is the mate of the tensorator of `G` (`CategoryTheory.Adjunction.inv_μ_eq_homEquiv_symm`),
the tensor comparison of `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`. This is how a
left adjoint that is lax monoidal for an independent reason, such as restriction of sheaves to an
open subset, is shown to have invertible oplax tensor comparisons.

For a fully faithful monoidal functor `F`, morphisms `X ⊗ Y ⟶ Z` correspond to morphisms
`F.obj X ⊗ F.obj Y ⟶ F.obj Z` (`CategoryTheory.Functor.FullyFaithful.tensorHomEquiv`), by
`e ↦ μ F X Y ≫ F.map e`. This is how a monoidal equivalence transports pairings `X ⊗ Y ⟶ Z`.

An adjunction from a strong monoidal functor to a lax monoidal functor is monoidal as soon as its
unit is a monoidal natural transformation
(`CategoryTheory.Adjunction.isMonoidal_of_isMonoidal_unit`). So an equivalence is a monoidal
equivalence once its unit is monoidal, and its counit is then monoidal too; this is how an
equivalence built from given monoidal functors and a monoidal unit is shown to be monoidal.

Precomposition by a monoidal equivalence also identifies the categories of lax monoidal
functors and therefore their tensor-automorphism groups. The construction
`CategoryTheory.Equivalence.precomposeLaxMonoidalEquivalence` refines Mathlib’s
`CategoryTheory.Equivalence.congrLeft` to monoidal natural transformations.

## References

* G. M. Kelly, *Doctrinal adjunction*, Lecture Notes in Mathematics 420 (1974).
-/

public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The natural tensorator square for left tensoring by `A` under a lax monoidal functor. -/
def laxCommTensorLeft (F : C ⥤ D) [F.LaxMonoidal] (A : C) :
    TwoSquare F (MonoidalCategory.tensorLeft A)
      (MonoidalCategory.tensorLeft (F.obj A)) F :=
  .mk _ _ _ _ { app := fun B => Functor.LaxMonoidal.μ F A B
                naturality := fun _ _ f => Functor.LaxMonoidal.μ_natural_right F A f }

/-- The component of the tensorator square is the tensorator. -/
@[simp]
theorem laxCommTensorLeft_app (F : C ⥤ D) [F.LaxMonoidal] (A B : C) :
    (laxCommTensorLeft F A).app B = Functor.LaxMonoidal.μ F A B := by
  unfold laxCommTensorLeft
  rfl

/-- The natural oplax tensor comparison for right tensoring by `B`. -/
def oplaxCommTensorRight (F : C ⥤ D) [F.OplaxMonoidal] (B : C) :
    MonoidalCategory.tensorRight B ⋙ F ⟶ F ⋙ MonoidalCategory.tensorRight (F.obj B) where
  app A := Functor.OplaxMonoidal.δ F A B
  naturality _ _ f := (Functor.OplaxMonoidal.δ_natural_left F f B).symm

/-- The component of the oplax tensor comparison is the oplax tensorator. -/
@[simp]
theorem oplaxCommTensorRight_app (F : C ⥤ D) [F.OplaxMonoidal] (A B : C) :
    (F.oplaxCommTensorRight B).app A = Functor.OplaxMonoidal.δ F A B :=
  (rfl)

/-- The natural oplax tensor comparison for left tensoring by `A`. -/
def oplaxCommTensorLeft (F : C ⥤ D) [F.OplaxMonoidal] (A : C) :
    MonoidalCategory.tensorLeft A ⋙ F ⟶ F ⋙ MonoidalCategory.tensorLeft (F.obj A) where
  app B := Functor.OplaxMonoidal.δ F A B
  naturality _ _ f := (Functor.OplaxMonoidal.δ_natural_right F A f).symm

/-- The component of the oplax tensor comparison is the oplax tensorator. -/
@[simp]
theorem oplaxCommTensorLeft_app (F : C ⥤ D) [F.OplaxMonoidal] (A B : C) :
    (F.oplaxCommTensorLeft A).app B = Functor.OplaxMonoidal.δ F A B :=
  (rfl)

namespace OplaxMonoidal

open MonoidalCategory Limits

variable (F : C ⥤ D) [F.OplaxMonoidal]

/-- An invertible unit comparison makes the tensor comparison at the left unit invertible. -/
theorem isIso_δ_tensorUnit_left [IsIso (η F)] (B : C) :
    IsIso (δ F (𝟙_ C) B) := by
  have : IsIso (δ F (𝟙_ C) B ≫ η F ▷ F.obj B ≫ (λ_ (F.obj B)).hom) := by
    rw [left_unitality_hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (η F ▷ F.obj B ≫ (λ_ (F.obj B)).hom)

/-- Invertibility of an oplax tensor comparison extends across a colimit when the functor and
right tensoring preserve that colimit. -/
theorem isIso_δ_of_isColimit_left {J : Type*} [Category* J] (K : J ⥤ C)
    (c : Cocone K) (hc : IsColimit c) (B : C)
    [PreservesColimit K (tensorRight B ⋙ F)]
    [PreservesColimit K (F ⋙ tensorRight (F.obj B))]
    (h : ∀ j, IsIso (δ F (K.obj j) B)) : IsIso (δ F c.pt B) := by
  have : IsIso (whiskerLeft K (F.oplaxCommTensorRight B)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact h
  exact isIso_app_coconePt_of_preservesColimit K (F.oplaxCommTensorRight B) c hc

/-- An invertible unit comparison makes the tensor comparison at the right unit invertible. -/
theorem isIso_δ_tensorUnit_right [IsIso (η F)] (A : C) :
    IsIso (δ F A (𝟙_ C)) := by
  have : IsIso (δ F A (𝟙_ C) ≫ F.obj A ◁ η F ≫ (ρ_ (F.obj A)).hom) := by
    rw [right_unitality_hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.obj A ◁ η F ≫ (ρ_ (F.obj A)).hom)

/-- Invertibility of an oplax tensor comparison extends across a colimit when the functor and
left tensoring preserve that colimit. -/
theorem isIso_δ_of_isColimit_right {J : Type*} [Category* J] (K : J ⥤ C)
    (c : Cocone K) (hc : IsColimit c) (A : C)
    [PreservesColimit K (tensorLeft A ⋙ F)]
    [PreservesColimit K (F ⋙ tensorLeft (F.obj A))]
    (h : ∀ j, IsIso (δ F A (K.obj j))) : IsIso (δ F A c.pt) := by
  have : IsIso (whiskerLeft K (F.oplaxCommTensorLeft A)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact h
  exact isIso_app_coconePt_of_preservesColimit K (F.oplaxCommTensorLeft A) c hc

end OplaxMonoidal

namespace LaxMonoidal

section Composition

universe v₃ u₃

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- Equality of tensor comparisons for two lax monoidal structures on a functor is preserved
by postcomposition with a lax monoidal functor. -/
lemma comp_μ_congr (F : C ⥤ D) (G : D ⥤ E) [G.LaxMonoidal]
    (L₁ L₂ : F.LaxMonoidal) (X Y : C)
    (h : @μ _ _ _ _ _ _ F L₁ X Y = @μ _ _ _ _ _ _ F L₂ X Y) :
    (letI := L₁; μ (F ⋙ G) X Y) = (letI := L₂; μ (F ⋙ G) X Y) := by
  simp only [comp_μ]
  rw [h]

end Composition

open MonoidalCategory

/-- Transport a lax monoidal structure along a natural isomorphism of functors. This is the lax
analogue of Mathlib's `CategoryTheory.Functor.Monoidal.transport`. -/
@[instance_reducible]
def transport {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : G.LaxMonoidal :=
  ofTensorHom (ε F ≫ i.hom.app (𝟙_ C))
    (fun X Y ↦ (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y))
    (fun f g ↦ by
      rw [tensorHom_comp_tensorHom_assoc, i.inv.naturality, i.inv.naturality,
        ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, i.hom.naturality, Category.assoc,
        Category.assoc])
    (fun X Y Z ↦ by
      simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp, ← i.hom.naturality]
      have hl : ((i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y) ⊗ₘ i.inv.app Z =
          ((i.inv.app X ⊗ₘ i.inv.app Y) ⊗ₘ i.inv.app Z) ≫ (μ F X Y ▷ F.obj Z) := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      have hr : i.inv.app X ⊗ₘ ((i.inv.app Y ⊗ₘ i.inv.app Z) ≫ μ F Y Z) =
          (i.inv.app X ⊗ₘ (i.inv.app Y ⊗ₘ i.inv.app Z)) ≫ (F.obj X ◁ μ F Y Z) := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      rw [hl, hr, Category.assoc, Category.assoc, LaxMonoidal.associativity_assoc,
        associator_naturality_assoc])
    (fun X ↦ by
      simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp, ← i.hom.naturality]
      have h : ε F ⊗ₘ i.inv.app X = (𝟙_ D ◁ i.inv.app X) ≫ (ε F ▷ F.obj X) := by
        rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
          Category.id_comp]
      rw [h, Category.assoc, ← LaxMonoidal.left_unitality_assoc, leftUnitor_naturality_assoc,
        Iso.inv_hom_id_app, Category.comp_id])
    (fun X ↦ by
      simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp, ← i.hom.naturality]
      have h : i.inv.app X ⊗ₘ ε F = (i.inv.app X ▷ 𝟙_ D) ≫ (F.obj X ◁ ε F) := by
        rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
          Category.id_comp]
      rw [h, Category.assoc, ← LaxMonoidal.right_unitality_assoc, rightUnitor_naturality_assoc,
        Iso.inv_hom_id_app, Category.comp_id])

/-- The unit of the transported lax monoidal structure. -/
@[reassoc]
lemma transport_ε {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : letI := transport i
    ε G = ε F ≫ i.hom.app (𝟙_ C) :=
  (rfl)

/-- The tensorator of the transported lax monoidal structure. -/
@[reassoc]
lemma transport_μ {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y) :=
  (rfl)

end LaxMonoidal

namespace OplaxMonoidal

open MonoidalCategory

section Retract

variable {F G : C ⥤ D} [F.OplaxMonoidal]

private lemma retract_δ_natural (i : G ⟶ F) (r : F ⟶ G) {X Y X' Y' : C} (f : X ⟶ Y)
    (g : X' ⟶ Y') :
    (i.app (X ⊗ X') ≫ δ F X X' ≫ (r.app X ⊗ₘ r.app X')) ≫ (G.map f ⊗ₘ G.map g) =
      G.map (f ⊗ₘ g) ≫ i.app (Y ⊗ Y') ≫ δ F Y Y' ≫ (r.app Y ⊗ₘ r.app Y') := by
  simp only [Category.assoc, i.naturality_assoc, ← δ_natural_assoc, tensorHom_comp_tensorHom,
    NatTrans.naturality]

/-- An oplax monoidal structure on a retract `G` of an oplax monoidal functor `F`, given by
`e : Retract G F`, provided the idempotent `e.r ≫ e.i` of `F` does not change the counit `η F`
and the comultiplication `δ F` followed by `e.r ⊗ e.r`.  The counit of `G` is `e.i ≫ η F`
(`CategoryTheory.Functor.OplaxMonoidal.ofRetract_η`) and its comultiplication is
`e.i ≫ δ F ≫ (e.r ⊗ e.r)` (`CategoryTheory.Functor.OplaxMonoidal.ofRetract_δ`). -/
@[instance_reducible]
def ofRetract (e : Retract G F)
    (hδ : ∀ X Y : C, e.r.app (X ⊗ Y) ≫ e.i.app (X ⊗ Y) ≫ δ F X Y ≫ (e.r.app X ⊗ₘ e.r.app Y) =
      δ F X Y ≫ (e.r.app X ⊗ₘ e.r.app Y))
    (hη : e.r.app (𝟙_ C) ≫ e.i.app (𝟙_ C) ≫ η F = η F) : G.OplaxMonoidal where
  η := e.i.app (𝟙_ C) ≫ η F
  δ X Y := e.i.app (X ⊗ Y) ≫ δ F X Y ≫ (e.r.app X ⊗ₘ e.r.app Y)
  δ_natural_left f X' := by
    simpa using retract_δ_natural e.i e.r f (𝟙 X')
  δ_natural_right X' f := by
    simpa using retract_δ_natural e.i e.r (𝟙 X') f
  oplax_associativity X Y Z := by
    -- the idempotent `e.r ≫ e.i` created between the two comultiplications is absorbed by `hδ`
    have hl : (e.r.app (X ⊗ Y) ⊗ₘ e.r.app Z) ≫
        (e.i.app (X ⊗ Y) ≫ δ F X Y ≫ (e.r.app X ⊗ₘ e.r.app Y)) ▷ G.obj Z =
          (δ F X Y ▷ F.obj Z) ≫ ((e.r.app X ⊗ₘ e.r.app Y) ⊗ₘ e.r.app Z) := by
      rw [tensorHom_comp_whiskerRight, hδ, whiskerRight_comp_tensorHom]
    have hr : (e.r.app X ⊗ₘ e.r.app (Y ⊗ Z)) ≫
        G.obj X ◁ (e.i.app (Y ⊗ Z) ≫ δ F Y Z ≫ (e.r.app Y ⊗ₘ e.r.app Z)) =
          (F.obj X ◁ δ F Y Z) ≫ (e.r.app X ⊗ₘ (e.r.app Y ⊗ₘ e.r.app Z)) := by
      rw [tensorHom_comp_whiskerLeft, hδ, whiskerLeft_comp_tensorHom]
    simp only [Category.assoc]
    rw [reassoc_of% hl, associator_naturality, associativity_assoc, ← e.i.naturality_assoc, hr]
  oplax_left_unitality X := by
    have h : (e.r.app (𝟙_ C) ⊗ₘ e.r.app X) ≫ (e.i.app (𝟙_ C) ≫ η F) ▷ G.obj X =
        (η F ▷ F.obj X) ≫ (𝟙_ D ◁ e.r.app X) := by
      rw [tensorHom_comp_whiskerRight, hη, tensorHom_def]
    simp only [Category.assoc]
    rw [h, e.i.naturality_assoc, ← left_unitality_assoc]
    simp [← NatTrans.comp_app_assoc]
  oplax_right_unitality X := by
    have h : (e.r.app X ⊗ₘ e.r.app (𝟙_ C)) ≫ G.obj X ◁ (e.i.app (𝟙_ C) ≫ η F) =
        (F.obj X ◁ η F) ≫ (e.r.app X ▷ 𝟙_ D) := by
      rw [tensorHom_comp_whiskerLeft, hη, tensorHom_def']
    simp only [Category.assoc]
    rw [h, e.i.naturality_assoc, ← right_unitality_assoc]
    simp [← NatTrans.comp_app_assoc]

variable (e : Retract G F)
  (hδ : ∀ X Y : C, e.r.app (X ⊗ Y) ≫ e.i.app (X ⊗ Y) ≫ δ F X Y ≫ (e.r.app X ⊗ₘ e.r.app Y) =
    δ F X Y ≫ (e.r.app X ⊗ₘ e.r.app Y))
  (hη : e.r.app (𝟙_ C) ≫ e.i.app (𝟙_ C) ≫ η F = η F)

/-- The counit of the oplax monoidal structure on a retract. -/
lemma ofRetract_η : letI := ofRetract e hδ hη
    η G = e.i.app (𝟙_ C) ≫ η F :=
  (rfl)

/-- The comultiplication of the oplax monoidal structure on a retract. -/
lemma ofRetract_δ (X Y : C) : letI := ofRetract e hδ hη
    δ G X Y = e.i.app (X ⊗ Y) ≫ δ F X Y ≫ (e.r.app X ⊗ₘ e.r.app Y) :=
  (rfl)

end Retract

end OplaxMonoidal

section FullyFaithful

open MonoidalCategory

variable {F : C ⥤ D} [F.Monoidal]

/-- For a fully faithful monoidal functor `F`, morphisms `X ⊗ Y ⟶ Z` correspond to morphisms
`F.obj X ⊗ F.obj Y ⟶ F.obj Z`, by `e ↦ μ F X Y ≫ F.map e`. -/
noncomputable def FullyFaithful.tensorHomEquiv (hF : F.FullyFaithful) {X Y Z : C} :
    (X ⊗ Y ⟶ Z) ≃ (F.obj X ⊗ F.obj Y ⟶ F.obj Z) where
  toFun e := LaxMonoidal.μ F X Y ≫ F.map e
  invFun e := hF.preimage (OplaxMonoidal.δ F X Y ≫ e)
  left_inv e := by simp
  right_inv e := by simp

/-- `Functor.FullyFaithful.tensorHomEquiv` takes `e` to `μ F X Y ≫ F.map e`. -/
@[simp]
theorem FullyFaithful.tensorHomEquiv_apply (hF : F.FullyFaithful) {X Y Z : C}
    (e : X ⊗ Y ⟶ Z) : hF.tensorHomEquiv e = LaxMonoidal.μ F X Y ≫ F.map e :=
  (rfl)

/-- The inverse of `Functor.FullyFaithful.tensorHomEquiv` takes a morphism `e` to the preimage
of `δ F X Y ≫ e`. -/
@[simp]
theorem FullyFaithful.tensorHomEquiv_symm_apply (hF : F.FullyFaithful) {X Y Z : C}
    (e : F.obj X ⊗ F.obj Y ⟶ F.obj Z) :
    hF.tensorHomEquiv.symm e = hF.preimage (OplaxMonoidal.δ F X Y ≫ e) :=
  (rfl)

end FullyFaithful

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)
  [F₁.OplaxMonoidal] [F₂.OplaxMonoidal] [G₁.LaxMonoidal] [G₂.LaxMonoidal]
  [adj₁.IsMonoidal] [adj₂.IsMonoidal] {σ : F₂ ⟶ F₁} {τ : G₁ ⟶ G₂} [NatTrans.IsMonoidal τ]

/-- A natural transformation between left adjoints whose conjugate is a monoidal natural
transformation of the lax monoidal right adjoints is compatible with the units of the oplax
monoidal structures. -/
theorem app_tensorUnit_comp_η_of_conjugateEquiv (h : conjugateEquiv adj₁ adj₂ σ = τ) :
    σ.app (𝟙_ C) ≫ η F₁ = η F₂ := by
  -- The transpose of `σ` along the units is `τ`.
  have hσ : adj₂.unit.app (𝟙_ C) ≫ G₂.map (σ.app _) = adj₁.unit.app _ ≫ τ.app _ := by
    rw [← unit_conjugateEquiv, h]
  apply (adj₂.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp, reassoc_of% hσ, ← τ.naturality,
    unit_app_unit_comp_map_η_assoc, NatTrans.IsMonoidal.unit, unit_app_unit_comp_map_η]

/-- A natural transformation between left adjoints whose conjugate is a monoidal natural
transformation of the lax monoidal right adjoints is compatible with the tensor comparison maps of
the oplax monoidal structures. -/
@[reassoc]
theorem app_tensor_comp_δ_of_conjugateEquiv (h : conjugateEquiv adj₁ adj₂ σ = τ) (X Y : C) :
    σ.app (X ⊗ Y) ≫ δ F₁ X Y = δ F₂ X Y ≫ (σ.app X ⊗ₘ σ.app Y) := by
  -- The transpose of `σ` along the units is `τ`.
  have hσ (Z : C) : adj₂.unit.app Z ≫ G₂.map (σ.app Z) = adj₁.unit.app Z ≫ τ.app _ := by
    rw [← unit_conjugateEquiv, h]
  apply (adj₂.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp, reassoc_of% hσ, ← τ.naturality,
    unit_app_tensor_comp_map_δ_assoc, NatTrans.IsMonoidal.tensor, ← μ_natural,
    tensorHom_comp_tensorHom_assoc, hσ]

section Transpose

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal] [G.LaxMonoidal]
  [adj.IsMonoidal]

/-- Along a monoidal adjunction, the transpose of a morphism out of `F (𝟙_ C)` that factors
through the oplax unit `η F` factors through the lax unit `ε G`. -/
theorem homEquiv_η_comp {N : D} (u : 𝟙_ D ⟶ N) :
    adj.homEquiv _ _ (η F ≫ u) = ε G ≫ G.map u := by
  simp [homEquiv_unit, unit_app_unit_comp_map_η_assoc]

/-- Along a monoidal adjunction, the transpose of a morphism out of `F (M₁ ⊗ M₂)` that factors
through the oplax tensor comparison `δ F` and a tensor product of morphisms is the tensor product
of the transposes followed by the lax tensor comparison `μ G`. -/
theorem homEquiv_δ_comp_tensorHom_comp {M₁ M₂ : C} {N₁ N₂ N : D} (φ₁ : F.obj M₁ ⟶ N₁)
    (φ₂ : F.obj M₂ ⟶ N₂) (n : N₁ ⊗ N₂ ⟶ N) :
    adj.homEquiv _ _ (δ F M₁ M₂ ≫ (φ₁ ⊗ₘ φ₂) ≫ n) =
      (adj.homEquiv _ _ φ₁ ⊗ₘ adj.homEquiv _ _ φ₂) ≫ μ G N₁ N₂ ≫ G.map n := by
  simp [homEquiv_unit, unit_app_tensor_comp_map_δ_assoc, ← μ_natural_assoc,
    tensorHom_comp_tensorHom_assoc]

end Transpose

section Doctrinal

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.LaxMonoidal] [G.LaxMonoidal]

/-- If the counit of an adjunction between lax monoidal functors is compatible with the
tensorators, then the tensorator of the left adjoint is a split monomorphism, split by the mate
of the tensorator of the right adjoint. -/
theorem μ_comp_homEquiv_symm_tensorHom_unit_comp_μ
    (hcounit : ∀ X Y : D, μ F (G.obj X) (G.obj Y) ≫ F.map (μ G X Y) ≫ adj.counit.app (X ⊗ Y) =
      (adj.counit.app X ⊗ₘ adj.counit.app Y)) (X Y : C) :
    μ F X Y ≫ (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _) = 𝟙 _ := by
  rw [homEquiv_counit, F.map_comp, Category.assoc, ← μ_natural_assoc]
  simp [hcounit]

/-- If the unit of an adjunction between lax monoidal functors is compatible with the
tensorators, then the mate of the tensorator of the right adjoint is a section of the tensorator
of the left adjoint. -/
theorem homEquiv_symm_tensorHom_unit_comp_μ_comp_μ
    (hunit : ∀ X Y : C, adj.unit.app (X ⊗ Y) =
      (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _ ≫ G.map (μ F X Y)) (X Y : C) :
    (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _) ≫ μ F X Y = 𝟙 _ := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc, ← hunit]
  simp [homEquiv_unit]

/-- **Doctrinal adjunction** for tensorators: if the unit and the counit of an adjunction
between lax monoidal functors are compatible with the tensorators, then the tensorator of the
left adjoint is invertible. Its inverse is computed by `inv_μ_eq_homEquiv_symm`. -/
theorem isIso_μ_of_unit_of_counit
    (hunit : ∀ X Y : C, adj.unit.app (X ⊗ Y) =
      (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _ ≫ G.map (μ F X Y))
    (hcounit : ∀ X Y : D, μ F (G.obj X) (G.obj Y) ≫ F.map (μ G X Y) ≫ adj.counit.app (X ⊗ Y) =
      (adj.counit.app X ⊗ₘ adj.counit.app Y)) (X Y : C) :
    IsIso (μ F X Y) :=
  ⟨_, μ_comp_homEquiv_symm_tensorHom_unit_comp_μ adj hcounit X Y,
    homEquiv_symm_tensorHom_unit_comp_μ_comp_μ adj hunit X Y⟩

/-- If the counit of an adjunction between lax monoidal functors is compatible with the
tensorators, then an inverse of the tensorator of the left adjoint is the mate of the tensorator
of the right adjoint, that is, the tensor comparison of the oplax monoidal structure
`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`. -/
theorem inv_μ_eq_homEquiv_symm
    (hcounit : ∀ X Y : D, μ F (G.obj X) (G.obj Y) ≫ F.map (μ G X Y) ≫ adj.counit.app (X ⊗ Y) =
      (adj.counit.app X ⊗ₘ adj.counit.app Y)) (X Y : C) [IsIso (μ F X Y)] :
    inv (μ F X Y) = (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _) :=
  IsIso.inv_eq_of_hom_inv_id (μ_comp_homEquiv_symm_tensorHom_unit_comp_μ adj hcounit X Y)

end Doctrinal

end CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

section MonoidalUnit

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

/-- An adjunction from a strong monoidal functor to a lax monoidal functor is monoidal as soon as
its unit is a monoidal natural transformation. -/
theorem Adjunction.isMonoidal_of_isMonoidal_unit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.Monoidal] [G.LaxMonoidal] [NatTrans.IsMonoidal adj.unit] : adj.IsMonoidal where
  leftAdjoint_ε := by
    have h := NatTrans.IsMonoidal.unit (τ := adj.unit)
    rw [Functor.LaxMonoidal.id_ε, Category.id_comp, Functor.LaxMonoidal.comp_ε] at h
    rw [h, Category.assoc, ← G.map_comp, Functor.Monoidal.ε_η, G.map_id, Category.comp_id]
  leftAdjoint_μ X Y := by
    have h := NatTrans.IsMonoidal.tensor (τ := adj.unit) (G.obj X) (G.obj Y)
    rw [Functor.LaxMonoidal.id_μ, Category.id_comp, Functor.LaxMonoidal.comp_μ] at h
    rw [reassoc_of% h, ← G.map_comp, Functor.Monoidal.μ_δ_assoc,
      ← Functor.LaxMonoidal.μ_natural, tensorHom_comp_tensorHom_assoc]
    simp

/-- An equivalence whose functor and inverse are strong monoidal is a monoidal equivalence as
soon as its unit is a monoidal natural transformation. -/
theorem Equivalence.isMonoidal_of_isMonoidal_unit (e : C ≌ D) [e.functor.Monoidal]
    [e.inverse.Monoidal] [NatTrans.IsMonoidal e.unit] : e.IsMonoidal :=
  have : NatTrans.IsMonoidal e.toAdjunction.unit := inferInstanceAs (NatTrans.IsMonoidal e.unit)
  e.toAdjunction.isMonoidal_of_isMonoidal_unit

end MonoidalUnit

/-- Precomposition by a lax monoidal functor, on bundled lax monoidal functors and
monoidal natural transformations. -/
def Functor.precomposeLaxMonoidal (F : C ⥤ D) [F.LaxMonoidal] :
    LaxMonoidalFunctor D E ⥤ LaxMonoidalFunctor C E where
  obj G := .of (F ⋙ G.toFunctor)
  map α := ⟨Functor.whiskerLeft F α.hom, NatTrans.IsMonoidal.whiskerLeft α.hom⟩

/-- Precomposition leaves the underlying functor equal to the ordinary composite. -/
@[simp]
theorem Functor.precomposeLaxMonoidal_obj_toFunctor (F : C ⥤ D) [F.LaxMonoidal]
    (G : LaxMonoidalFunctor D E) :
    ((F.precomposeLaxMonoidal).obj G).toFunctor = F ⋙ G.toFunctor :=
  (rfl)

open MonoidalCategory Functor.LaxMonoidal in
/-- Precomposition composes the tensor comparisons. Its underlying functor objects are
propositionally identified with those of the composite functor. -/
theorem Functor.precomposeLaxMonoidal_obj_μ (F : C ⥤ D) [F.LaxMonoidal]
    (G : LaxMonoidalFunctor D E) (X Y : C) :
    HEq (μ ((F.precomposeLaxMonoidal).obj G).toFunctor X Y)
      (μ G.toFunctor (F.obj X) (F.obj Y) ≫ G.map (μ F X Y)) :=
  (HEq.rfl)

open MonoidalCategory Functor.LaxMonoidal in
/-- Precomposition composes the unit comparisons. Its underlying functor object is
propositionally identified with that of the composite functor. -/
theorem Functor.precomposeLaxMonoidal_obj_ε (F : C ⥤ D) [F.LaxMonoidal]
    (G : LaxMonoidalFunctor D E) :
    HEq (ε ((F.precomposeLaxMonoidal).obj G).toFunctor)
      (ε G.toFunctor ≫ G.map (ε F)) :=
  (HEq.rfl)

/-- Precomposition acts on a monoidal natural transformation by ordinary left whiskering.
The two transformations are typed through propositionally identified functor objects. -/
@[simp]
theorem Functor.precomposeLaxMonoidal_map_hom_app (F : C ⥤ D) [F.LaxMonoidal]
    {G G' : LaxMonoidalFunctor D E} (α : G ⟶ G') (X : C) :
    HEq (((F.precomposeLaxMonoidal).map α).hom.app X) (α.hom.app (F.obj X)) :=
  (HEq.rfl)

/-- A monoidal equivalence identifies a lax monoidal functor with its round-trip
precomposition. This is the monoidal version of the inverse of `Equivalence.invFunIdAssoc`. -/
noncomputable def Equivalence.laxMonoidalRoundTripIso (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]
    (F : LaxMonoidalFunctor D E) :
    F ≅ LaxMonoidalFunctor.of (e.inverse ⋙ (e.functor ⋙ F.toFunctor)) := by
  let i : F.toFunctor ≅ e.inverse ⋙ (e.functor ⋙ F.toFunctor) :=
    F.toFunctor.leftUnitor.symm ≪≫
      isoWhiskerRight e.counitIso.symm F.toFunctor ≪≫
      Functor.associator e.inverse e.functor F.toFunctor
  have : NatTrans.IsMonoidal e.counitIso.hom := inferInstanceAs (NatTrans.IsMonoidal e.counit)
  have : NatTrans.IsMonoidal e.counitIso.inv := inferInstance
  have : NatTrans.IsMonoidal i.hom := by
    dsimp only [i, Iso.trans_hom, Iso.symm_hom]
    have : NatTrans.IsMonoidal (isoWhiskerRight e.counitIso.symm F.toFunctor).hom := by
      rw [isoWhiskerRight_hom, Iso.symm_hom]
      infer_instance
    infer_instance
  exact @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _ i ‹NatTrans.IsMonoidal i.hom›

/-- The round-trip comparison is induced by the inverse counit of the equivalence. -/
@[simp]
theorem Equivalence.laxMonoidalRoundTripIso_hom_app (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]
    (F : LaxMonoidalFunctor D E) (X : D) :
    (e.laxMonoidalRoundTripIso F).hom.hom.app X = F.map (e.counitIso.inv.app X) := by
  -- Pass to the underlying natural isomorphism constructed by the round-trip comparison.
  change (F.toFunctor.leftUnitor.symm ≪≫
    isoWhiskerRight e.counitIso.symm F.toFunctor ≪≫
      Functor.associator e.inverse e.functor F.toFunctor).hom.app X = _
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    leftUnitor_inv_app, isoWhiskerRight_hom, whiskerRight_app, associator_hom_app,
    Category.id_comp, Category.comp_id]

/-- The round-trip comparison is natural in the lax monoidal functor. -/
theorem Equivalence.laxMonoidalRoundTripIso_naturality (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]
    {F G : LaxMonoidalFunctor D E} (f : F ⟶ G) (X : D) :
    f.hom.app X ≫ (e.laxMonoidalRoundTripIso G).hom.hom.app X =
      (e.laxMonoidalRoundTripIso F).hom.hom.app X ≫
        f.hom.app (e.functor.obj (e.inverse.obj X)) := by
  rw [Equivalence.laxMonoidalRoundTripIso_hom_app,
    Equivalence.laxMonoidalRoundTripIso_hom_app]
  exact (f.hom.naturality (e.counitIso.inv.app X)).symm

/-- Precomposition by a monoidal equivalence is an equivalence on lax monoidal functors.
The inverse precomposes by the inverse equivalence. -/
noncomputable def Equivalence.precomposeLaxMonoidalEquivalence (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    LaxMonoidalFunctor D E ≌ LaxMonoidalFunctor C E :=
  Equivalence.mk e.functor.precomposeLaxMonoidal e.inverse.precomposeLaxMonoidal
    (NatIso.ofComponents (fun F ↦ e.laxMonoidalRoundTripIso F)
      (fun f ↦ by
        ext X
        exact e.laxMonoidalRoundTripIso_naturality f X))
    (NatIso.ofComponents (fun F ↦ e.symm.laxMonoidalRoundTripIso F)
      (fun f ↦ by
        ext X
        exact e.symm.laxMonoidalRoundTripIso_naturality f X)).symm

/-- The forward functor of monoidal precomposition is precomposition by the given functor. -/
@[simp]
theorem Equivalence.precomposeLaxMonoidalEquivalence_functor (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    (e.precomposeLaxMonoidalEquivalence (E := E)).functor =
      e.functor.precomposeLaxMonoidal :=
  (rfl)

/-- The inverse functor of monoidal precomposition is precomposition by the inverse functor. -/
@[simp]
theorem Equivalence.precomposeLaxMonoidalEquivalence_inverse (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    (e.precomposeLaxMonoidalEquivalence (E := E)).inverse =
      e.inverse.precomposeLaxMonoidal :=
  (rfl)

end CategoryTheory
