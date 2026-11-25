/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Category

/-!
# Universal δ-functors

Homological universality classifies maps into the universal object;
cohomological universality classifies maps out of it. Degree-zero evaluation
is fully faithful on the corresponding category of universal δ-functors,
giving the uniqueness isomorphism.

## References

* C. Weibel, *An Introduction to Homological Algebra* (1994), Definition 2.1.4.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable (A : Type u₁) [Category.{v₁} A] [Preadditive A]
variable (B : Type u₂) [Category.{v₂} B] [Preadditive B]

namespace HomologicalDeltaFunctor

/-- A universal homological δ-functor uniquely receives an extension of each
natural transformation into its degree-zero functor. -/
def IsUniversal (T : HomologicalDeltaFunctor A B) : Prop :=
  ∀ (S : HomologicalDeltaFunctor A B) (f₀ : S.T 0 ⟶ T.T 0),
    ∃! f : S ⟶ T, Hom.app f 0 = f₀

/-- Universality is preserved by an isomorphism of homological δ-functors. -/
theorem isUniversal_of_iso {S T : HomologicalDeltaFunctor A B}
    (hT : IsUniversal A B T) (e : S ≅ T) : IsUniversal A B S := by
  intro U f₀
  obtain ⟨g, hg, huniq⟩ := hT U (f₀ ≫ Hom.app e.hom 0)
  refine ⟨g ≫ e.inv, ?_, ?_⟩
  · change Hom.app (g ≫ e.inv) 0 = f₀
    rw [Hom.comp_app, hg, Category.assoc, ← Hom.comp_app, e.hom_inv_id,
      Hom.id_app, Category.comp_id]
  · intro f hf
    have hfg : Hom.app (f ≫ e.hom) 0 = f₀ ≫ Hom.app e.hom 0 := by
      rw [Hom.comp_app, hf]
    rw [← huniq (f ≫ e.hom) hfg, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The full subcategory of universal homological δ-functors. -/
abbrev UniversalObjects :=
  ObjectProperty.FullSubcategory (IsUniversal A B)

/-- Degree-zero evaluation restricted to universal homological δ-functors. -/
abbrev universalEvaluation : UniversalObjects A B ⥤ (A ⥤ B) :=
  ObjectProperty.ι (IsUniversal A B) ⋙ evaluation A B 0

/-- The universal extension property makes degree-zero evaluation fully faithful. -/
noncomputable def evaluationFullyFaithful :
    (universalEvaluation A B).FullyFaithful where
  preimage {X Y} f₀ := ObjectProperty.homMk (Y.property X.obj f₀).choose
  map_preimage {X Y} f₀ := (Y.property X.obj f₀).choose_spec.1
  preimage_map {X Y} f := by
    apply ObjectProperty.hom_ext
    exact ((Y.property X.obj (Hom.app f.hom 0)).choose_spec.2 f.hom rfl).symm

/-- Lift a degree-zero isomorphism between universal homological δ-functors. -/
noncomputable def isoOfZeroIso (S T : HomologicalDeltaFunctor A B)
    (hS : IsUniversal A B S) (hT : IsUniversal A B T)
    (e : S.T 0 ≅ T.T 0) : S ≅ T :=
  (ObjectProperty.ι (IsUniversal A B)).mapIso
    ((evaluationFullyFaithful A B).preimageIso
      (X := ⟨S, hS⟩) (Y := ⟨T, hT⟩) e)

/-- The lifted comparison induces the prescribed morphism in degree zero. -/
@[simp]
theorem isoOfZeroIso_hom_app_zero (S T : HomologicalDeltaFunctor A B)
    (hS : IsUniversal A B S) (hT : IsUniversal A B T)
    (e : S.T 0 ≅ T.T 0) :
    Hom.app (isoOfZeroIso A B S T hS hT e).hom 0 = e.hom := by
  change (universalEvaluation A B).map
    ((evaluationFullyFaithful A B).preimage
      (X := ⟨S, hS⟩) (Y := ⟨T, hT⟩) e.hom) = e.hom
  exact (evaluationFullyFaithful A B).map_preimage
    (X := ⟨S, hS⟩) (Y := ⟨T, hT⟩) _

end HomologicalDeltaFunctor

namespace CohomologicalDeltaFunctor

/-- A universal cohomological δ-functor uniquely extends each natural
transformation out of its degree-zero functor. -/
def IsUniversal (T : CohomologicalDeltaFunctor A B) : Prop :=
  ∀ (S : CohomologicalDeltaFunctor A B) (f₀ : T.T 0 ⟶ S.T 0),
    ∃! f : T ⟶ S, Hom.app f 0 = f₀

/-- Universality is preserved by an isomorphism of cohomological δ-functors. -/
theorem isUniversal_of_iso {S T : CohomologicalDeltaFunctor A B}
    (hT : IsUniversal A B T) (e : S ≅ T) : IsUniversal A B S := by
  intro U f₀
  obtain ⟨g, hg, huniq⟩ := hT U (Hom.app e.inv 0 ≫ f₀)
  refine ⟨e.hom ≫ g, ?_, ?_⟩
  · change Hom.app (e.hom ≫ g) 0 = f₀
    rw [Hom.comp_app, hg, ← Category.assoc, ← Hom.comp_app, e.hom_inv_id,
      Hom.id_app, Category.id_comp]
  · intro f hf
    have hfg : Hom.app (e.inv ≫ f) 0 = Hom.app e.inv 0 ≫ f₀ := by
      rw [Hom.comp_app, hf]
    rw [← huniq (e.inv ≫ f) hfg, ← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- The full subcategory of universal cohomological δ-functors. -/
abbrev UniversalObjects :=
  ObjectProperty.FullSubcategory (IsUniversal A B)

/-- Degree-zero evaluation restricted to universal cohomological δ-functors. -/
abbrev universalEvaluation : UniversalObjects A B ⥤ (A ⥤ B) :=
  ObjectProperty.ι (IsUniversal A B) ⋙ evaluation A B 0

/-- The universal extension property makes degree-zero evaluation fully faithful. -/
noncomputable def evaluationFullyFaithful :
    (universalEvaluation A B).FullyFaithful where
  preimage {X Y} f₀ := ObjectProperty.homMk (X.property Y.obj f₀).choose
  map_preimage {X Y} f₀ := (X.property Y.obj f₀).choose_spec.1
  preimage_map {X Y} f := by
    apply ObjectProperty.hom_ext
    exact ((X.property Y.obj (Hom.app f.hom 0)).choose_spec.2 f.hom rfl).symm

/-- Lift a degree-zero isomorphism between universal cohomological δ-functors. -/
noncomputable def isoOfZeroIso (S T : CohomologicalDeltaFunctor A B)
    (hS : IsUniversal A B S) (hT : IsUniversal A B T)
    (e : S.T 0 ≅ T.T 0) : S ≅ T :=
  (ObjectProperty.ι (IsUniversal A B)).mapIso
    ((evaluationFullyFaithful A B).preimageIso
      (X := ⟨S, hS⟩) (Y := ⟨T, hT⟩) e)

/-- The lifted comparison induces the prescribed morphism in degree zero. -/
@[simp]
theorem isoOfZeroIso_hom_app_zero (S T : CohomologicalDeltaFunctor A B)
    (hS : IsUniversal A B S) (hT : IsUniversal A B T)
    (e : S.T 0 ≅ T.T 0) :
    Hom.app (isoOfZeroIso A B S T hS hT e).hom 0 = e.hom := by
  change (universalEvaluation A B).map
    ((evaluationFullyFaithful A B).preimage
      (X := ⟨S, hS⟩) (Y := ⟨T, hT⟩) e.hom) = e.hom
  exact (evaluationFullyFaithful A B).map_preimage
    (X := ⟨S, hS⟩) (Y := ⟨T, hT⟩) _

end CohomologicalDeltaFunctor

end CategoryTheory
