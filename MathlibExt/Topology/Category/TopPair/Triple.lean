/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/

module

public import MathlibExt.Topology.Category.TopPair.Adjunctions
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Topological triples

This file defines topological triples, their three associated topological
pairs, and the canonical natural transformations between those pairs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w v u

def topTripleEmbeddings : ObjectProperty (ComposableArrows TopCat.{w} 2) :=
  fun S => Topology.IsEmbedding (S.map' 0 1) ∧ Topology.IsEmbedding (S.map' 1 2)

abbrev TopTriple := topTripleEmbeddings.FullSubcategory

noncomputable def topTriplePair01 : TopTriple.{w} ⥤ TopPair.{w} where
  obj T := TopPair.of (T.obj.map' 0 1) T.property.1
  map {T U} f := TopPair.ofHom
      (CategoryTheory.ComposableArrows.app' f.hom 1)
      (CategoryTheory.ComposableArrows.app' f.hom 0) (by
    exact (CategoryTheory.ComposableArrows.naturality' f.hom 0 1).symm)

noncomputable def topTriplePair12 : TopTriple.{w} ⥤ TopPair.{w} where
  obj T := TopPair.of (T.obj.map' 1 2) T.property.2
  map {T U} f := TopPair.ofHom
      (CategoryTheory.ComposableArrows.app' f.hom 2)
      (CategoryTheory.ComposableArrows.app' f.hom 1) (by
    exact (CategoryTheory.ComposableArrows.naturality' f.hom 1 2).symm)

noncomputable def topTriplePair02 : TopTriple.{w} ⥤ TopPair.{w} where
  obj T := TopPair.of (T.obj.map' 0 2) (by
    rw [T.obj.map'_comp 0 1 2]
    exact T.property.2.comp T.property.1)
  map {T U} f := TopPair.ofHom
      (CategoryTheory.ComposableArrows.app' f.hom 2)
      (CategoryTheory.ComposableArrows.app' f.hom 0) (by
    exact (CategoryTheory.ComposableArrows.naturality' f.hom 0 2).symm)

/-- The canonical inclusion `(A, B) ⟶ (X, B)` associated to a triple `B ⟶ A ⟶ X`. -/
noncomputable def topTriplePair01To02 :
    topTriplePair01.{w} ⟶ topTriplePair02.{w} where
  app T := TopPair.ofHom (T.obj.map' 1 2) (𝟙 _) (by
    change 𝟙 (T.obj.obj ⟨0, by omega⟩) ≫ T.obj.map' 0 2 =
      T.obj.map' 0 1 ≫ T.obj.map' 1 2
    simpa using T.obj.map'_comp 0 1 2)
  naturality T U f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change f.hom.app ⟨0, by omega⟩ ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.app ⟨0, by omega⟩
      simp
    · change f.hom.app ⟨1, by omega⟩ ≫ U.obj.map' 1 2 =
        T.obj.map' 1 2 ≫ f.hom.app ⟨2, by omega⟩
      exact (CategoryTheory.ComposableArrows.naturality' f.hom 1 2).symm

/-- The canonical inclusion `(X, B) ⟶ (X, A)` associated to a triple `B ⟶ A ⟶ X`. -/
noncomputable def topTriplePair02To12 :
    topTriplePair02.{w} ⟶ topTriplePair12.{w} where
  app T := TopPair.ofHom (𝟙 _) (T.obj.map' 0 1) (by
    change T.obj.map' 0 1 ≫ T.obj.map' 1 2 = T.obj.map' 0 2 ≫ 𝟙 _
    simpa using (T.obj.map'_comp 0 1 2).symm)
  naturality T U f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change f.hom.app ⟨0, by omega⟩ ≫ U.obj.map' 0 1 =
        T.obj.map' 0 1 ≫ f.hom.app ⟨1, by omega⟩
      exact (CategoryTheory.ComposableArrows.naturality' f.hom 0 1).symm
    · change f.hom.app ⟨2, by omega⟩ ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.app ⟨2, by omega⟩
      simp

/-- The middle diagonal pair `(A, A)` associated to a triple `B ⟶ A ⟶ X`. -/
noncomputable def topTripleMiddleDiag : TopTriple.{w} ⥤ TopPair.{w} :=
  topTriplePair01 ⋙ TopPair.proj₁ ⋙ TopPair.diag

/-- The canonical inclusion `(A, B) ⟶ (A, A)` via the unit of `proj₁ ⊣ diag`. -/
noncomputable def topTriplePair01ToMiddleDiag :
    topTriplePair01.{w} ⟶ topTripleMiddleDiag.{w} :=
  Functor.whiskerLeft topTriplePair01 TopPair.proj₁AdjDiag.unit

/-- The canonical inclusion `(A, A) ⟶ (X, A)` via the counit of `diag ⊣ proj₂`. -/
noncomputable def topTripleMiddleDiagToPair12 :
    topTripleMiddleDiag.{w} ⟶ topTriplePair12.{w} :=
  Functor.whiskerLeft topTriplePair12 TopPair.diagAdjProj₂.counit

/-- The composite between the outer pairs of a triple factors through the
diagonal pair on its middle space. -/
theorem topTriplePair01To02_comp_topTriplePair02To12 :
    topTriplePair01To02.{w} ≫ topTriplePair02To12.{w} =
      topTriplePair01ToMiddleDiag.{w} ≫ topTripleMiddleDiagToPair12.{w} := by
  ext T : 2
  apply MorphismProperty.Arrow.Hom.ext
  · simp only [NatTrans.comp_app, Functor.whiskerLeft,
      topTriplePair01To02, topTriplePair02To12,
      topTriplePair01ToMiddleDiag, topTripleMiddleDiagToPair12,
      topTripleMiddleDiag]
    cat_disch
  · simp only [NatTrans.comp_app, Functor.whiskerLeft,
      topTriplePair01To02, topTriplePair02To12,
      topTriplePair01ToMiddleDiag, topTripleMiddleDiagToPair12,
      topTripleMiddleDiag]
    cat_disch

end AlgebraicTopology
