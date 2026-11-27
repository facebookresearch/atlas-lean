/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1EmbeddingCoproducts

/-!
# Closed relative T1 embeddings from simplicial monomorphisms

The realization of a simplicial subcomplex inclusion is a closed embedding
whose codomain points outside its image are closed. Its skeletal filtration
gives a sequential transfinite composition with this relative T1 property.
Every simplicial monomorphism has the same realized embedding property.

For any simplicial map, its realized image equals the realized image of its
range-subcomplex inclusion.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomotopicalAlgebra

noncomputable section

namespace SSet

/--
For any simplicial map, the range of its realized map equals the range of
the realized inclusion of its simplicial range subcomplex.
-/
theorem range_toTop_map_eq_range_toTop_map_range_ι {X Y : SSet.{u}} (f : X ⟶ Y) :
    Set.range (SSet.toTop.map f).hom =
      Set.range (SSet.toTop.map (Subcomplex.range f).ι).hom := by
  have h_eq : SSet.toTop.map f =
      SSet.toTop.map (Subcomplex.toRange f) ≫
        SSet.toTop.map (Subcomplex.range f).ι := by
    rw [← Functor.map_comp, Subcomplex.toRange_ι]
  have h_surj : Function.Surjective (SSet.toTop.map (Subcomplex.toRange f)).hom := by
    have : Epi (Subcomplex.toRange f) := inferInstance
    exact (TopCat.epi_iff_surjective _).mp
      (Functor.map_epi SSet.toTop.{u} (f := Subcomplex.toRange f))
  calc Set.range (SSet.toTop.map f).hom
      = Set.range (SSet.toTop.map (Subcomplex.toRange f) ≫
          SSet.toTop.map (Subcomplex.range f).ι).hom := by rw [h_eq]
    _ = Set.range ((SSet.toTop.map (Subcomplex.range f).ι).hom ∘
          (SSet.toTop.map (Subcomplex.toRange f)).hom) := rfl
    _ = Set.range (SSet.toTop.map (Subcomplex.range f).ι).hom :=
        Function.Surjective.range_comp h_surj _

end SSet

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}} (S : X.Subcomplex)

open SSet.relativeCellComplexOfMono

private noncomputable def relCell :
    RelativeCellComplex
      (basicCell := fun (n : ℕ) (_ : Unit) => (SSet.boundary.{u} n).ι)
      (S.ι : (S : SSet.{u}) ⟶ X) :=
  SSet.relativeCellComplexOfMono S.ι

private instance preservesWellOrderContinuous_toTop :
    PreservesWellOrderContinuousOfShape ℕ SSet.toTop.{u} where
  preservesColimitsOfShape _j hj :=
    (Order.not_isSuccLimit_of_isSuccArchimedean hj).elim

private lemma closedT1_toTop_map_l (d : ℕ) :
    TopCat.closedT1Embeddings (SSet.toTop.map (l S.ι d)) := by
  let i : (S : SSet.{u}) ⟶ X := S.ι
  have : Mono i := inferInstance
  let CellT := Cell i d
  let F₁ : CellT → SSet.{u} := fun _ => (SSet.boundary.{u} d : SSet.{u})
  let F₂ : CellT → SSet.{u} := fun _ =>
    SSet.stdSimplex.obj (SimplexCategory.mk d)
  have h₁S : IsColimit (Cofan.mk (sigmaBoundary i d) (Limits.Sigma.ι F₁)) :=
    coproductIsCoproduct F₁
  have h₂S : IsColimit (Cofan.mk (sigmaStdSimplex i d) (Limits.Sigma.ι F₂)) :=
    coproductIsCoproduct F₂
  have h_l_eq : l i d =
      Limits.Sigma.map (fun _ : CellT => (SSet.boundary.{u} d).ι) := rfl
  have h₁T : IsColimit
      (SSet.toTop.mapCocone (Cofan.mk (sigmaBoundary i d) (Limits.Sigma.ι F₁))) :=
    isColimitOfPreserves SSet.toTop.{u} h₁S
  have h₂T : IsColimit
      (SSet.toTop.mapCocone (Cofan.mk (sigmaStdSimplex i d) (Limits.Sigma.ι F₂))) :=
    isColimitOfPreserves SSet.toTop.{u} h₂S
  let X₁ : Discrete CellT ⥤ TopCat.{u} := Discrete.functor F₁ ⋙ SSet.toTop.{u}
  let X₂ : Discrete CellT ⥤ TopCat.{u} := Discrete.functor F₂ ⋙ SSet.toTop.{u}
  let f : X₁ ⟶ X₂ :=
    { app := fun ⟨c⟩ => SSet.toTop.map (SSet.boundary.{u} d).ι
      naturality := by
        intro ⟨a⟩ ⟨b⟩ h
        have : a = b := Discrete.eq_of_hom h
        subst this
        simp }
  have h_colim :
      (TopCat.closedT1Embeddings.colimitsOfShape (Discrete CellT))
        (SSet.toTop.map (l i d)) := by
    refine MorphismProperty.colimitsOfShape.mk' X₁ X₂
      (SSet.toTop.mapCocone (Cofan.mk (sigmaBoundary i d) (Limits.Sigma.ι F₁)))
      (SSet.toTop.mapCocone (Cofan.mk (sigmaStdSimplex i d) (Limits.Sigma.ι F₂)))
      h₁T h₂T f
      (fun ⟨_⟩ => SSet.boundary.closedT1Embeddings_toTop_map_ι d)
      (SSet.toTop.map (l i d)) ?_
    intro ⟨c⟩
    have hσ : Limits.Sigma.ι F₁ c ≫ l i d =
        (SSet.boundary.{u} d).ι ≫ Limits.Sigma.ι F₂ c := by
      calc Limits.Sigma.ι F₁ c ≫ l i d
          = Limits.Sigma.ι F₁ c ≫
            Limits.Sigma.map (fun _ : CellT => (SSet.boundary.{u} d).ι) := by
            rw [h_l_eq]
        _ = (SSet.boundary.{u} d).ι ≫ Limits.Sigma.ι F₂ c :=
          Limits.Sigma.ι_map _ c
    calc (SSet.toTop.mapCocone (Cofan.mk (sigmaBoundary i d)
            (Limits.Sigma.ι F₁))).ι.app ⟨c⟩ ≫ SSet.toTop.map (l i d)
        = SSet.toTop.map (Limits.Sigma.ι F₁ c) ≫ SSet.toTop.map (l i d) := rfl
      _ = SSet.toTop.map (Limits.Sigma.ι F₁ c ≫ l i d) := by
          rw [← Functor.map_comp]
      _ = SSet.toTop.map ((SSet.boundary.{u} d).ι ≫ Limits.Sigma.ι F₂ c) := by
          rw [hσ]
      _ = SSet.toTop.map (SSet.boundary.{u} d).ι ≫
          SSet.toTop.map (Limits.Sigma.ι F₂ c) := by rw [Functor.map_comp]
      _ = f.app ⟨c⟩ ≫
          (SSet.toTop.mapCocone (Cofan.mk (sigmaStdSimplex i d)
            (Limits.Sigma.ι F₂))).ι.app ⟨c⟩ := rfl
  have : TopCat.closedT1Embeddings.IsStableUnderColimitsOfShape
      (Discrete CellT) := inferInstance
  have h_le : TopCat.closedT1Embeddings.colimitsOfShape (Discrete CellT) ≤
      TopCat.closedT1Embeddings :=
    MorphismProperty.colimitsOfShape_le
  exact h_le _ h_colim

private lemma isPushout_toTop_r (d : ℕ) :
    IsPushout (SSet.toTop.map (t S.ι d))
      (SSet.toTop.map (l S.ι d))
      (SSet.toTop.map (r S.ι d))
      (SSet.toTop.map (b S.ι d)) :=
  (isPushout S.ι d).map SSet.toTop.{u}

private lemma closedT1_toTop_r (d : ℕ) :
    TopCat.closedT1Embeddings (SSet.toTop.map (r S.ι d)) := by
  have h_push := isPushout_toTop_r S d
  have h_l := closedT1_toTop_map_l S d
  exact TopCat.isClosedT1Embedding_of_isPushout h_push.flip h_l

private noncomputable def realizedTransfinite :
    (TopCat.closedT1Embeddings.inverseImage SSet.toTop.{u}).TransfiniteCompositionOfShape ℕ
      S.ι where
  toTransfiniteCompositionOfShape := (relCell S).toTransfiniteCompositionOfShape
  map_mem j _ := closedT1_toTop_r S j

/--
The sequential transfinite-composition data exhibiting a realized subcomplex
inclusion as a composition of closed relative T1 embeddings.
-/
noncomputable opaque closedT1Realized :
    TopCat.closedT1Embeddings.TransfiniteCompositionOfShape ℕ (SSet.toTop.map S.ι) :=
  (realizedTransfinite S).map

/--
The realization of an arbitrary subcomplex inclusion is a closed embedding
whose points outside the image are closed in the codomain.
-/
theorem closedT1Embeddings_toTop_map_ι :
    TopCat.closedT1Embeddings (SSet.toTop.map S.ι) := by
  have h_mem : TopCat.closedT1Embeddings.transfiniteCompositionsOfShape ℕ
      (SSet.toTop.map S.ι) := ⟨closedT1Realized S⟩
  have h_le : TopCat.closedT1Embeddings.transfiniteCompositionsOfShape ℕ ≤
      TopCat.closedT1Embeddings :=
    MorphismProperty.transfiniteCompositionsOfShape_le
      (J := ℕ) (W := TopCat.closedT1Embeddings)
  exact h_le _ h_mem

end Subcomplex

end SSet

namespace SSet

/--
The realization of every simplicial monomorphism is a closed relative T1 embedding.
-/
theorem closedT1Embeddings_toTop_map_of_mono {X Y : SSet.{u}} (f : X ⟶ Y)
    [Mono f] : TopCat.closedT1Embeddings (SSet.toTop.map f) := by
  have h_fac : Subcomplex.toRange f ≫ (Subcomplex.range f).ι = f :=
    Subcomplex.toRange_ι f
  have : IsIso (Subcomplex.toRange f) := inferInstance
  have h_iso : TopCat.closedT1Embeddings (SSet.toTop.map (Subcomplex.toRange f)) :=
    Topology.IsClosedT1Embedding.of_homeomorph
      (TopCat.homeoOfIso (SSet.toTop.mapIso (asIso (Subcomplex.toRange f))))
  have h_sub : TopCat.closedT1Embeddings
      (SSet.toTop.map (Subcomplex.range f).ι) :=
    Subcomplex.closedT1Embeddings_toTop_map_ι (S := Subcomplex.range f)
  have h_eq : SSet.toTop.map f =
      SSet.toTop.map (Subcomplex.toRange f) ≫
        SSet.toTop.map (Subcomplex.range f).ι := by
    calc SSet.toTop.map f
        = SSet.toTop.map (Subcomplex.toRange f ≫ (Subcomplex.range f).ι) :=
          congrArg SSet.toTop.map h_fac.symm
      _ = SSet.toTop.map (Subcomplex.toRange f) ≫
          SSet.toTop.map (Subcomplex.range f).ι := by rw [Functor.map_comp]
  rw [h_eq]
  exact h_sub.comp h_iso

end SSet

end
