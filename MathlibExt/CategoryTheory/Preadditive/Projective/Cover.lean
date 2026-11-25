/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Essential epimorphisms and projective covers

An essential epimorphism is an epimorphism `f : P ⟶ X` for which every `g : Y ⟶ P`
whose composite with `f` is epic is itself epic. A projective cover strengthens the
native projective presentation by requiring its epimorphism to be essential.

For projective `P`, an epimorphism from `P` is essential exactly when every
endomorphism fixing it is invertible. No abelian or finite-length assumption is needed.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {P X Y Z : C}

/-- An epimorphism which detects epimorphisms composed before it. -/
class IsEssentialEpi (f : P ⟶ X) : Prop extends Epi f where
  /-- An epimorphic composite forces its first factor to be epic. -/
  epi_of_comp : ∀ {Y : C} (g : Y ⟶ P), Epi (g ≫ f) → Epi g

/-- Every isomorphism is an essential epimorphism. -/
instance isEssentialEpi_of_isIso (f : P ⟶ X) [IsIso f] : IsEssentialEpi f where
  epi_of_comp g h := (epi_comp_iff_of_isIso g f).mp h

/-- Essential epimorphisms are closed under composition. -/
lemma IsEssentialEpi.comp (f : P ⟶ X) (g : X ⟶ Y)
    [IsEssentialEpi f] [IsEssentialEpi g] : IsEssentialEpi (f ≫ g) where
  epi_of_comp h hh := by
    have hfg : Epi ((h ≫ f) ≫ g) := by simpa only [Category.assoc] using hh
    exact IsEssentialEpi.epi_of_comp (f := f) h
      (IsEssentialEpi.epi_of_comp (f := g) (h ≫ f) hfg)

/-- For a projective domain, the essential epimorphisms are exactly the right-minimal epis. -/
theorem isEssentialEpi_iff_endomorphism_isIso (f : P ⟶ X) [Projective P] [Epi f] :
    IsEssentialEpi f ↔ ∀ e : P ⟶ P, e ≫ f = f → IsIso e := by
  constructor
  · intro hf e he
    let : IsEssentialEpi f := hf
    have : Epi (e ≫ f) := by simpa only [he] using (inferInstance : Epi f)
    have : Epi e := IsEssentialEpi.epi_of_comp (f := f) e inferInstance
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 P) e
    have hsf : s ≫ f = f := by
      calc
        s ≫ f = s ≫ (e ≫ f) := by rw [he]
        _ = (s ≫ e) ≫ f := (Category.assoc _ _ _).symm
        _ = f := by rw [hs, Category.id_comp]
    have : Epi (s ≫ f) := by simpa only [hsf] using (inferInstance : Epi f)
    have : Epi s := IsEssentialEpi.epi_of_comp (f := f) s inferInstance
    have hes : e ≫ s = 𝟙 P := by
      apply (cancel_epi s).mp
      rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]
    exact ⟨⟨s, hes, hs⟩⟩
  · intro h
    refine { epi_of_comp := ?_ }
    intro Y g hg
    let : Epi (g ≫ f) := hg
    obtain ⟨s, hs⟩ := Projective.factors f (g ≫ f)
    have : IsIso (s ≫ g) := h (s ≫ g) (by simpa only [Category.assoc] using hs)
    exact epi_of_epi s g

/-- A projective presentation whose epimorphism is essential. -/
structure ProjectiveCover (X : C) extends ProjectivePresentation X where
  /-- The covering epimorphism is essential. -/
  [essential : IsEssentialEpi f]

attribute [instance] ProjectiveCover.essential

namespace ProjectiveCover

/-- An isomorphism from a projective object supplies a projective cover. -/
def ofIso (i : P ≅ X) [Projective P] : ProjectiveCover X where
  p := P
  f := i.hom
  essential := inferInstance

/-- The identity is a projective cover of every projective object. -/
def ofProjective (X : C) [Projective X] : ProjectiveCover X :=
  ofIso (Iso.refl X)

/-- Every endomorphism fixing the covering map is invertible. -/
theorem endomorphism_isIso (cover : ProjectiveCover X) (e : cover.p ⟶ cover.p)
    (h : e ≫ cover.f = cover.f) : IsIso e :=
  (isEssentialEpi_iff_endomorphism_isIso cover.f).mp cover.essential e h

end ProjectiveCover

/-- Every object admits an essential epimorphism from a projective object. -/
class HasProjectiveCovers (C : Type u) [Category.{v} C] : Prop where
  /-- A projective cover of each object. -/
  cover : ∀ X : C, Nonempty (ProjectiveCover X)

/-- Covers provide the projective presentations; no converse is asserted. -/
instance (priority := 100) enoughProjectives_of_hasProjectiveCovers [HasProjectiveCovers C] :
    EnoughProjectives C where
  presentation X := (HasProjectiveCovers.cover X).map ProjectiveCover.toProjectivePresentation

/-- A category in which every object is projective has identity projective covers. -/
theorem hasProjectiveCovers_of_projective (h : ∀ X : C, Projective X) :
    HasProjectiveCovers C where
  cover X := by
    let := h X
    exact ⟨ProjectiveCover.ofProjective X⟩

end CategoryTheory
