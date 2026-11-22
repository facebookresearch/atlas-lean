/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentComponentNerve
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingHoHom
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Equivalence

/-!
# The actual component category of a locally Kan coherent nerve

The native nerve adjunction factors the proved whole component-nerve
map through the actual ordinary homotopy category. It retains every
individual original object and represented arrow. The already proved
Hom-class equivalences make this actual functor an equivalence when
the original enriched Homs are Kan. Its entire strict-map naturality
and specified isomorphism readbacks are derived.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.ComponentHomotopyCategory
open SimplicialEnrichment

/-- The actual nerve-adjunction factorization of the whole original component comparison. -/
def readFunctor (C : Carrier.{u}) :
    (coherentNerveFunctor.obj C).HomotopyCategory ⥤ ComponentCategory.objects.{u} C :=
  SSet.Truncated.HomotopyCategory.descOfTruncation ((SSet.truncation 2).map (ComponentNerve.map C))

/-- The actual ordinary comparison keeps the supplied individual original object itself. -/
theorem readFunctor_obj (C : Carrier.{u}) (x : C) :
    (readFunctor C).obj (MappingHoHom.object x) = ComponentCategory.objectOf.{u} C x := rfl

/-- Every object of the actual coherent-nerve homotopy category is a supplied original individual vertex. -/
theorem object_surjective (C : Carrier.{u}) :
    Function.Surjective (MappingHoHom.object (C := C)) := by
  intro a
  cases a using SSet.HomotopyCategory.rec with
  | mk σ =>
    refine ⟨verticesEquiv C σ, ?_⟩
    change SSet.HomotopyCategory.mk (constantSimplex C ⦋0⦌ (vertexOf C σ)) =
      SSet.HomotopyCategory.mk σ
    exact congrArg SSet.HomotopyCategory.mk (constant_vertexOf C σ)

/-- The full original represented coherent edge reads back its precise original component arrow. -/
theorem readFunctor_map_originalEdge (C : Carrier.{u}) (x y : C)
    (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    (readFunctor C).map (MappingEdges.edge x y τ).toHoHom = ComponentCategory.arrowOf C τ := by
  change (SSet.Truncated.HomotopyCategory.descOfTruncation _).map
    (SSet.Truncated.HomotopyCategory.homMk (MappingEdges.edge x y τ).toTruncated) = _
  rw [SSet.Truncated.HomotopyCategory.descOfTruncation_map_homMk]
  change nerve.homEquiv ((MappingEdges.edge x y τ).map (ComponentNerve.map C)) = _
  apply (nerve.homEquiv
    (x := (ComponentNerve.map C).app (op ⦋0⦌) (SSet.yonedaEquiv (HomSimplexEndpoints.vertex x)))
    (y := (ComponentNerve.map C).app (op ⦋0⦌) (SSet.yonedaEquiv (HomSimplexEndpoints.vertex y)))).symm.injective
  rw [Equiv.symm_apply_apply]
  apply SSet.Edge.ext
  change (ComponentNerve.map C).app (op ⦋1⦌) (MappingEdges.edge x y τ).edge =
    ComposableArrows.mk₁ (ComponentCategory.arrowOf C τ)
  rw [MappingEdges.edge_readback]
  exact ComponentNerve.map_originalEdge x y τ

/-- Every original Hom class reads back unchanged through the existing actual coherent Hom-class equivalence. -/
theorem readFunctor_map_homEquiv (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C)
    (c : SSet.π₀ (x ⟶[SSet.{u}] y)) :
    (readFunctor C).map (MappingHoHom.homEquiv hKan x y c) = c := by
  obtain ⟨τ, rfl⟩ := SSet.π₀.mk_surjective c
  rw [MappingHoHom.homEquiv_mk]
  exact readFunctor_map_originalEdge C x y τ

/-- Genuine local Kan Homs make the actual component readback functor fully faithful. -/
def fullyFaithful (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    (readFunctor C).FullyFaithful := by
  apply Classical.choice
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
  intro a b
  obtain ⟨x, rfl⟩ := object_surjective C a
  obtain ⟨y, rfl⟩ := object_surjective C b
  constructor
  · intro f g h
    obtain ⟨c, rfl⟩ := (MappingHoHom.homEquiv hKan x y).surjective f
    obtain ⟨d, rfl⟩ := (MappingHoHom.homEquiv hKan x y).surjective g
    rw [readFunctor_map_homEquiv, readFunctor_map_homEquiv] at h
    exact congrArg (MappingHoHom.homEquiv hKan x y) h
  · intro c
    exact ⟨MappingHoHom.homEquiv hKan x y c, readFunctor_map_homEquiv C hKan x y c⟩

/-- The readback functor is surjective on the actual individual original object labels, without any local
  Kan premise. -/
theorem readFunctor_essSurj (C : Carrier.{u}) : (readFunctor C).EssSurj :=
  Functor.essSurj_of_surj (fun x => ⟨MappingHoHom.object x, rfl⟩)

/-- The constructed ordinary functor is a genuine equivalence for every locally Kan original enrichment. -/
theorem isEquivalence (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    (readFunctor C).IsEquivalence := {
  faithful := (fullyFaithful C hKan).faithful
  full := (fullyFaithful C hKan).full
  essSurj := readFunctor_essSurj C }

/-- The whole ordinary category equivalence has the same actual readback functor and both inverse comparisons. -/
def equivalence (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    (coherentNerveFunctor.obj C).HomotopyCategory ≌ ComponentCategory.objects.{u} C := by
  let _ := isEquivalence C hKan
  exact (readFunctor C).asEquivalence

/-- The equivalence's forward functor is the actual original component readback. -/
theorem equivalence_functor (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    (equivalence C hKan).functor = readFunctor C := rfl

private theorem desc_postcompose {X : SSet.Truncated.{u} 2}
    {A B : Type u} [SmallCategory A] [SmallCategory B]
    (φ : X ⟶ (SSet.truncation 2).obj (nerve A)) (G : A ⥤ B) :
    SSet.Truncated.HomotopyCategory.descOfTruncation (φ ≫ (SSet.truncation 2).map (nerveMap G)) =
      SSet.Truncated.HomotopyCategory.descOfTruncation φ ⋙ G := by
  apply (SSet.Truncated.HomotopyCategory.functorEquiv (X := X) (C := B)).injective
  change SSet.Truncated.HomotopyCategory.homToNerveMk
      (SSet.Truncated.HomotopyCategory.descOfTruncation (φ ≫ (SSet.truncation 2).map (nerveMap G))) =
    SSet.Truncated.HomotopyCategory.homToNerveMk (SSet.Truncated.HomotopyCategory.descOfTruncation φ ⋙ G)
  rw [SSet.Truncated.HomotopyCategory.homToNerveMk_comp]
  exact (SSet.Truncated.HomotopyCategory.functorEquiv.apply_symm_apply _).trans
    (congrArg (fun ψ => ψ ≫ (SSet.truncation 2).map (nerveMap G))
      (SSet.Truncated.HomotopyCategory.functorEquiv.apply_symm_apply φ)).symm

/-- The entire ordinary category comparison is natural for the same strict enriched map, with no weak-map or
  Kan premise. -/
theorem naturality {C D : Carrier.{u}} (F : C ⟶ D) :
    SSet.mapHomotopyCategory (coherentNerveFunctor.map F) ⋙ readFunctor D =
      readFunctor C ⋙ ComponentCategory.mapFunctor F := by
  have h : (SSet.truncation 2).map (ComponentNerve.map C) ≫
      (SSet.truncation 2).map (nerveMap (ComponentCategory.mapFunctor F)) =
    (SSet.truncation 2).map (coherentNerveFunctor.map F) ≫
      (SSet.truncation 2).map (ComponentNerve.map D) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ComponentNerve.naturality]
  have hh := congrArg (SSet.Truncated.HomotopyCategory.descOfTruncation
    (C := ComponentCategory.objects.{u} D)) h
  rw [desc_postcompose, SSet.Truncated.HomotopyCategory.descOfTruncation_comp] at hh
  exact hh.symm

/-- A specified original component isomorphism gives an actual coherent-nerve isomorphism with precisely its
  represented forward and inverse arrows. -/
def liftIso (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C)
    (i : ComponentCategory.objectOf.{u} C x ≅ ComponentCategory.objectOf.{u} C y) :
    MappingHoHom.object x ≅ MappingHoHom.object y :=
  ((fullyFaithful C hKan).isoEquiv (X := MappingHoHom.object x) (Y := MappingHoHom.object y)).symm i

/-- The complete specified isomorphism is recovered by the actual ordinary readback functor. -/
theorem liftIso_readback (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C)
    (i : ComponentCategory.objectOf.{u} C x ≅ ComponentCategory.objectOf.{u} C y) :
    (readFunctor C).mapIso (liftIso C hKan x y i) = i :=
  ((fullyFaithful C hKan).isoEquiv (X := MappingHoHom.object x)
    (Y := MappingHoHom.object y)).apply_symm_apply i

/-- The supplied original representative of a component isomorphism represents that very lifted isomorphism,
  not only its endpoints. -/
theorem liftIso_originalArrow (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C)
    (i : ComponentCategory.objectOf.{u} C x ≅ ComponentCategory.objectOf.{u} C y)
    (a : (x ⟶[SSet.{u}] y) _⦋0⦌) (ha : SSet.π₀.mk a = i.hom) :
    (MappingEdges.edge x y a).toHoHom = (liftIso C hKan x y i).hom := by
  apply (fullyFaithful C hKan).map_injective
  exact (readFunctor_map_originalEdge C x y a).trans
    (ha.trans (congrArg Iso.hom (liftIso_readback C hKan x y i)).symm)

end CategoryTheory.CoherentRealization.ComponentHomotopyCategory
