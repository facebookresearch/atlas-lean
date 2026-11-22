/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKanRecognition

/-!
# Clients for Dwyer–Kan predicates and complete recognition

These clients exercise homotopy inverses, ordinary homotopy-category
equivalence, essential surjectivity, identity and composition, and
the Kan-complex bridge at arbitrary universes. They also import the
complete recognition theorem and check both directions and weakness
of the original same-endpoint right mapping-space map, without an
extra simplex-full-faithfulness assumption.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace DwyerKanTest

section CompleteRecognition

variable {X Y : SSet.{u}} [SSet.Quasicategory X] [SSet.Quasicategory Y]
  {f : X ⟶ Y}

example : SSet.categoricalEquivalences f ↔ SSet.isDwyerKanEquivalence f :=
  SSet.categoricalEquivalences_iff_isDwyerKanEquivalence

example (hDK : SSet.isDwyerKanEquivalence f) : SSet.categoricalEquivalences f :=
  hDK.categoricalEquivalences

example (hf : SSet.categoricalEquivalences f) (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.realizationWeakEquivalences (SSet.mappingSpaceRight.map X a b f) :=
  hf.rightMappingSpaceMap_weak a b

end CompleteRecognition


section CategoricalImpliesEquivalence

variable {X Y : SSet.{u}} [SSet.Quasicategory X] [SSet.Quasicategory Y]
  {f : X ⟶ Y}

example (hf : SSet.categoricalEquivalences f) : SSet.HasHoInverse f :=
  hf.hasHoInverse

example (h : SSet.HasHoInverse f) : SSet.categoricalEquivalences f :=
  h.categoricalEquivalences

example : SSet.categoricalEquivalences f ↔ SSet.HasHoInverse f :=
  SSet.categoricalEquivalences_iff_hasHoInverse

example (hf : SSet.categoricalEquivalences f) :
    ∃ g : Y ⟶ X,
      Nonempty ((SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X X (f ≫ g)) :
          SSet.hoFunctor.obj ((ihom X).obj X)) ≅
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X X (𝟙 X))) ∧
      Nonempty ((SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv Y Y (g ≫ f)) :
          SSet.hoFunctor.obj ((ihom Y).obj Y)) ≅
        SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv Y Y (𝟙 Y))) :=
  hf.hasHoInverse

example (hf : SSet.categoricalEquivalences f) :
    ∃ g : Y ⟶ X,
      (∃ e : SSet.Edge (SSet.ihomVertexEquiv X X (f ≫ g))
          (SSet.ihomVertexEquiv X X (𝟙 X)), e.IsEquivalence) ∧
      (∃ e : SSet.Edge (SSet.ihomVertexEquiv Y Y (g ≫ f))
          (SSet.ihomVertexEquiv Y Y (𝟙 Y)), e.IsEquivalence) :=
  hf.hasHoInverse.exists_isEquivalence_edges

example : SSet.HasHoInverse (𝟙 X) :=
  (SSet.categoricalEquivalences.of_isIso (𝟙 X)).hasHoInverse

end CategoricalImpliesEquivalence

section HomotopyCategoryEquivalence

variable {X Y : SSet.{u}} {f : X ⟶ Y}

example (hf : SSet.categoricalEquivalences f) :
    (SSet.mapHomotopyCategory f).IsEquivalence :=
  hf.isEquivalence_mapHomotopyCategory

example (hf : SSet.categoricalEquivalences f) :
    (SSet.hoFunctor.map f).toFunctor.IsEquivalence :=
  hf.isEquivalence_hoFunctor_map

example (hf : SSet.categoricalEquivalences f) (y : Y _⦋0⦌) :
    ∃ x : X _⦋0⦌, Nonempty
      (SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) x) ≅
        SSet.HomotopyCategory.mk y) :=
  hf.exists_nonempty_iso_mk_app y

example [SSet.Quasicategory Y] (hf : SSet.categoricalEquivalences f)
    (y : Y _⦋0⦌) :
    ∃ (x : X _⦋0⦌) (e : SSet.Edge (f.app (op ⦋0⦌) x) y),
      e.IsEquivalence :=
  hf.exists_isEquivalence_edge_app y

example : (SSet.mapHomotopyCategory (𝟙 X)).IsEquivalence :=
  (SSet.categoricalEquivalences.of_isIso (𝟙 X))
    |>.isEquivalence_mapHomotopyCategory

example (hf : SSet.categoricalEquivalences f) :
    (SSet.mapHomotopyCategory f).EssSurj := by
  have := hf.isEquivalence_mapHomotopyCategory
  infer_instance

example {C D : Type u} [Category.{u} C] [Category.{u} D]
    (e : Cat.of C ≅ Cat.of D) :
    (SSet.mapHomotopyCategory
      (CategoryTheory.nerveMap e.hom.toFunctor)).IsEquivalence :=
  (SSet.categoricalEquivalences.nerveMap_catIso_hom e)
    |>.isEquivalence_mapHomotopyCategory

end HomotopyCategoryEquivalence

section DwyerKanPredicates

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

example : SSet.dwyerKanEssentiallySurjective f ↔
    (SSet.mapHomotopyCategory f).EssSurj :=
  Iff.rfl

example (hf : SSet.categoricalEquivalences f) :
    SSet.dwyerKanEssentiallySurjective f :=
  hf.dwyerKanEssentiallySurjective

example (h : SSet.isDwyerKanEquivalence f) :
    SSet.dwyerKanEssentiallySurjective f :=
  h.dwyerKanEssentiallySurjective

example (h : SSet.isDwyerKanEquivalence f) :
    SSet.dwyerKanFullyFaithful f :=
  h.dwyerKanFullyFaithful

example (h : SSet.dwyerKanFullyFaithful f) (x y : X _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (SSet.mappingSpaceRight.map X (SSet.const x) (SSet.const y) f) :=
  h.vertex x y

example (h : SSet.dwyerKanFullyFaithful f)
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.realizationWeakEquivalences
      (SSet.mappingSpaceRight.map X a b f) :=
  h a b

example (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.mappingSpaceRight X a b ⟶ SSet.mappingSpaceRight Y (a ≫ f) (b ≫ f) :=
  SSet.mappingSpaceRight.map X a b f

example (x : X _⦋0⦌) :
    (SSet.const (X := (Δ[0] : SSet.{u})) x) ≫ f =
      SSet.const (f.app (op ⦋0⦌) x) :=
  SSet.const_comp x f

example (x y : X _⦋0⦌) {n : SimplexCategoryᵒᵖ}
    (σ : (SSet.mappingSpaceRight X (SSet.const x) (SSet.const y)).obj n) :
    ((SSet.mappingSpaceRight.map X (SSet.const x) (SSet.const y) f).app n σ).1 =
      σ.1 ≫ f :=
  SSet.mappingSpaceRight.map_app_val _ _ _ _ _

example : SSet.dwyerKanFullyFaithful (𝟙 X) :=
  SSet.dwyerKanFullyFaithful_id

example : ∀ {X : SSet.{u}}, SSet.dwyerKanFullyFaithful (𝟙 X) :=
  fun {X} => SSet.dwyerKanFullyFaithful_id (X := X)

example (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (hW : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex.W (SSet.mappingSpaceRight.map X a b f)) :
    SSet.dwyerKanFullyFaithful f :=
  SSet.dwyerKanFullyFaithful.of_kanComplexW hKanX hKanY hW

example (h : SSet.dwyerKanFullyFaithful f)
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.KanComplex.W (SSet.mappingSpaceRight.map X a b f) :=
  h.kanComplexW hKanX hKanY a b

example (hf : SSet.dwyerKanFullyFaithful f)
    (hg : SSet.dwyerKanFullyFaithful g) :
    SSet.dwyerKanFullyFaithful (f ≫ g) :=
  hf.comp hg

example (hf : SSet.isDwyerKanEquivalence f)
    (hg : SSet.isDwyerKanEquivalence g) :
    SSet.isDwyerKanEquivalence (f ≫ g) :=
  hf.comp hg

end DwyerKanPredicates

section UniverseZero

variable {X Y : SSet.{0}} [SSet.Quasicategory X] [SSet.Quasicategory Y]
  {f : X ⟶ Y}

example (hf : SSet.categoricalEquivalences.{0} f) : SSet.HasHoInverse f :=
  hf.hasHoInverse

example (hf : SSet.categoricalEquivalences.{0} f) :
    (SSet.mapHomotopyCategory f).IsEquivalence :=
  hf.isEquivalence_mapHomotopyCategory

example (hf : SSet.categoricalEquivalences.{0} f) (y : Y _⦋0⦌) :
    ∃ (x : X _⦋0⦌) (e : SSet.Edge (f.app (op ⦋0⦌) x) y),
      e.IsEquivalence :=
  hf.exists_isEquivalence_edge_app y

example (m : (Δ[0] : SSet.{0}) ⟶ CategoryTheory.nerve (Fin 2))
    (hf : SSet.categoricalEquivalences.{0} m) :
    SSet.dwyerKanEssentiallySurjective m :=
  hf.dwyerKanEssentiallySurjective

end UniverseZero

end DwyerKanTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end
