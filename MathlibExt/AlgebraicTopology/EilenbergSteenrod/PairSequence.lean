/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod

/-!
# Naturality of homology pair sequences

Homology theory data in a category with zero morphisms gives the pair sequence
formed from absolute homology, relative homology and the connecting maps. The
sequence is functorial in topological pairs and in morphisms of homology theory
data, yielding a bifunctor into composable four-arrow diagrams.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u v

namespace TopPair

namespace HomologyTheoryData

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

def subspaceMapNatTrans (E : HomologyTheoryData.{w} C) (n : ℤ) :
    TopPair.proj₂ ⋙ E.H n ⟶ TopPair.proj₁ ⋙ E.H n where
  app X := E.subspaceMap n X
  naturality X Y f := by
    change (E.H n).map (TopPair.Hom.snd f) ≫ (E.H n).map Y.map =
      (E.H n).map X.map ≫ (E.H n).map (TopPair.Hom.fst f)
    rw [← (E.H n).map_comp, ← (E.H n).map_comp]
    exact congrArg (E.H n).map (TopPair.Hom.w f)

def toRelativeNatTrans (E : HomologyTheoryData.{w} C) (n : ℤ) :
    TopPair.proj₁ ⋙ E.H n ⟶ E.Hₚ n where
  app X := E.toRelative n X
  naturality X Y f := by
    change (E.H n).map (TopPair.Hom.fst f) ≫
        ((E.iso n).hom.app Y.fst ≫ (E.Hₚ n).map (TopPair.j Y)) =
      ((E.iso n).hom.app X.fst ≫ (E.Hₚ n).map (TopPair.j X)) ≫
        (E.Hₚ n).map f
    rw [← Category.assoc, (E.iso n).hom.naturality]
    simp only [Functor.comp_map, Category.assoc, ← (E.Hₚ n).map_comp]
    congr 2
    ext x
    · exact PEmpty.elim x
    · rfl

/-- The absolute-to-relative map commutes with transport of the homological
degree. -/
theorem toRelative_comp_eqToHom (E : HomologyTheoryData.{w} C)
    (P : TopPair.{w}) {a b : ℤ} (h : a = b) :
    E.toRelative a P ≫
        eqToHom (congrArg (fun z => (E.Hₚ z).obj P) h) =
      eqToHom (congrArg (fun z => (E.H z).obj P.fst) h) ≫
        E.toRelative b P := by
  cases h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the absolute-to-relative map in the homology theory. -/
@[reassoc]
theorem toRelative_naturality_theory
    {E F : HomologyTheoryData.{w} C} (f : E ⟶ F) (n : ℤ) (X : TopPair.{w}) :
    (f.hom n).app X.fst ≫ F.toRelative n X =
      E.toRelative n X ≫ (f.homₚ n).app X := by
  symm
  simp only [HomologyTheoryData.toRelative]
  calc
    ((E.iso n).hom.app X.fst ≫ (E.Hₚ n).map (TopPair.j X)) ≫
          (f.homₚ n).app X =
        (E.iso n).hom.app X.fst ≫
          ((f.homₚ n).app (TopPair.ofTopCat X.fst) ≫
            (F.Hₚ n).map (TopPair.j X)) := by
          rw [Category.assoc, NatTrans.naturality]
          rfl
    _ = ((f.hom n).app X.fst ≫ (F.iso n).hom.app X.fst) ≫
          (F.Hₚ n).map (TopPair.j X) := by
          rw [← Category.assoc, f.iso_comm_app]
    _ = (f.hom n).app X.fst ≫
          ((F.iso n).hom.app X.fst ≫ (F.Hₚ n).map (TopPair.j X)) := by simp

def pairSequenceMap (E : HomologyTheoryData.{w} C) (n : ℤ)
    {X Y : TopPair.{w}} (f : X ⟶ Y) :
    E.pairSequence n X ⟶ E.pairSequence n Y :=
  ComposableArrows.homMk₄
    ((E.Hₚ n).map f)
    ((E.H (n - 1)).map (TopPair.Hom.snd f))
    ((E.H (n - 1)).map (TopPair.Hom.fst f))
    ((E.Hₚ (n - 1)).map f)
    ((E.H ((n - 1) - 1)).map (TopPair.Hom.snd f))
    (by exact ((E.δ n (n - 1)).naturality f).symm)
    (by exact ((E.subspaceMapNatTrans (n - 1)).naturality f).symm)
    (by exact ((E.toRelativeNatTrans (n - 1)).naturality f).symm)
    (by exact ((E.δ (n - 1) ((n - 1) - 1)).naturality f).symm)

def pairSequenceFunctor (E : HomologyTheoryData.{w} C) (n : ℤ) :
    TopPair.{w} ⥤ ComposableArrows C 4 where
  obj X := E.pairSequence n X
  map f := E.pairSequenceMap n f
  map_id X := by
    apply ComposableArrows.hom_ext₄
    · change (E.Hₚ n).map (𝟙 X) = 𝟙 _
      exact (E.Hₚ n).map_id X
    · change (E.H (n - 1)).map (𝟙 X.snd) = 𝟙 _
      exact (E.H (n - 1)).map_id X.snd
    · change (E.H (n - 1)).map (𝟙 X.fst) = 𝟙 _
      exact (E.H (n - 1)).map_id X.fst
    · change (E.Hₚ (n - 1)).map (𝟙 X) = 𝟙 _
      exact (E.Hₚ (n - 1)).map_id X
    · change (E.H ((n - 1) - 1)).map (𝟙 X.snd) = 𝟙 _
      exact (E.H ((n - 1) - 1)).map_id X.snd
  map_comp f g := by
    apply ComposableArrows.hom_ext₄
    · change (E.Hₚ n).map (f ≫ g) = (E.Hₚ n).map f ≫ (E.Hₚ n).map g
      exact (E.Hₚ n).map_comp f g
    · change (E.H (n - 1)).map (TopPair.Hom.snd f ≫ TopPair.Hom.snd g) =
        (E.H (n - 1)).map (TopPair.Hom.snd f) ≫
          (E.H (n - 1)).map (TopPair.Hom.snd g)
      exact (E.H (n - 1)).map_comp _ _
    · change (E.H (n - 1)).map (TopPair.Hom.fst f ≫ TopPair.Hom.fst g) =
        (E.H (n - 1)).map (TopPair.Hom.fst f) ≫
          (E.H (n - 1)).map (TopPair.Hom.fst g)
      exact (E.H (n - 1)).map_comp _ _
    · change (E.Hₚ (n - 1)).map (f ≫ g) =
        (E.Hₚ (n - 1)).map f ≫ (E.Hₚ (n - 1)).map g
      exact (E.Hₚ (n - 1)).map_comp f g
    · change (E.H ((n - 1) - 1)).map
        (TopPair.Hom.snd f ≫ TopPair.Hom.snd g) =
        (E.H ((n - 1) - 1)).map (TopPair.Hom.snd f) ≫
          (E.H ((n - 1) - 1)).map (TopPair.Hom.snd g)
      exact (E.H ((n - 1) - 1)).map_comp _ _

set_option backward.isDefEq.respectTransparency false in
def pairSequenceHom {E F : HomologyTheoryData.{w} C} (f : E ⟶ F) (n : ℤ)
    (X : TopPair.{w}) : E.pairSequence n X ⟶ F.pairSequence n X :=
  ComposableArrows.homMk₄
    ((f.homₚ n).app X)
    ((f.hom (n - 1)).app X.snd)
    ((f.hom (n - 1)).app X.fst)
    ((f.homₚ (n - 1)).app X)
    ((f.hom ((n - 1) - 1)).app X.snd)
    (by
      change (E.δ n (n - 1)).app X ≫ (f.hom (n - 1)).app X.snd =
        (f.homₚ n).app X ≫ (F.δ n (n - 1)).app X
      exact f.w_app n (n - 1) X)
    (by
      change (E.H (n - 1)).map X.map ≫ (f.hom (n - 1)).app X.fst =
        (f.hom (n - 1)).app X.snd ≫ (F.H (n - 1)).map X.map
      exact (f.hom (n - 1)).naturality X.map)
    (toRelative_naturality_theory f (n - 1) X).symm
    (by
      change (E.δ (n - 1) ((n - 1) - 1)).app X ≫
          (f.hom ((n - 1) - 1)).app X.snd =
        (f.homₚ (n - 1)).app X ≫
          (F.δ (n - 1) ((n - 1) - 1)).app X
      exact f.w_app (n - 1) ((n - 1) - 1) X)

def pairSequenceNatTrans {E F : HomologyTheoryData.{w} C} (f : E ⟶ F) (n : ℤ) :
    E.pairSequenceFunctor n ⟶ F.pairSequenceFunctor n where
  app X := pairSequenceHom f n X
  naturality X Y g := by
    apply ComposableArrows.hom_ext₄
    · change (E.Hₚ n).map g ≫ (f.homₚ n).app Y =
        (f.homₚ n).app X ≫ (F.Hₚ n).map g
      exact (f.homₚ n).naturality g
    · change (E.H (n - 1)).map (TopPair.Hom.snd g) ≫ (f.hom (n - 1)).app Y.snd =
        (f.hom (n - 1)).app X.snd ≫ (F.H (n - 1)).map (TopPair.Hom.snd g)
      exact (f.hom (n - 1)).naturality (TopPair.Hom.snd g)
    · change (E.H (n - 1)).map (TopPair.Hom.fst g) ≫ (f.hom (n - 1)).app Y.fst =
        (f.hom (n - 1)).app X.fst ≫ (F.H (n - 1)).map (TopPair.Hom.fst g)
      exact (f.hom (n - 1)).naturality (TopPair.Hom.fst g)
    · change (E.Hₚ (n - 1)).map g ≫ (f.homₚ (n - 1)).app Y =
        (f.homₚ (n - 1)).app X ≫ (F.Hₚ (n - 1)).map g
      exact (f.homₚ (n - 1)).naturality g
    · change (E.H ((n - 1) - 1)).map (TopPair.Hom.snd g) ≫
          (f.hom ((n - 1) - 1)).app Y.snd =
        (f.hom ((n - 1) - 1)).app X.snd ≫
          (F.H ((n - 1) - 1)).map (TopPair.Hom.snd g)
      exact (f.hom ((n - 1) - 1)).naturality (TopPair.Hom.snd g)

def pairSequenceBifunctor (n : ℤ) :
    HomologyTheoryData.{w} C ⥤ (TopPair.{w} ⥤ ComposableArrows C 4) where
  obj E := E.pairSequenceFunctor n
  map f := pairSequenceNatTrans f n
  map_id E := by
    apply NatTrans.ext
    ext X
    · change ((𝟙 E : E ⟶ E).homₚ n).app X = 𝟙 _
      simp
    · change ((𝟙 E : E ⟶ E).hom (n - 1)).app X.snd = 𝟙 _
      simp
    · change ((𝟙 E : E ⟶ E).hom (n - 1)).app X.fst = 𝟙 _
      simp
    · change ((𝟙 E : E ⟶ E).homₚ (n - 1)).app X = 𝟙 _
      simp
    · change ((𝟙 E : E ⟶ E).hom ((n - 1) - 1)).app X.snd = 𝟙 _
      simp
  map_comp {E F G} f g := by
    apply NatTrans.ext
    ext X
    · change ((f ≫ g).homₚ n).app X =
        (f.homₚ n).app X ≫ (g.homₚ n).app X
      simp
    · change ((f ≫ g).hom (n - 1)).app X.snd =
        (f.hom (n - 1)).app X.snd ≫ (g.hom (n - 1)).app X.snd
      simp
    · change ((f ≫ g).hom (n - 1)).app X.fst =
        (f.hom (n - 1)).app X.fst ≫ (g.hom (n - 1)).app X.fst
      simp
    · change ((f ≫ g).homₚ (n - 1)).app X =
        (f.homₚ (n - 1)).app X ≫ (g.homₚ (n - 1)).app X
      simp
    · change ((f ≫ g).hom ((n - 1) - 1)).app X.snd =
        (f.hom ((n - 1) - 1)).app X.snd ≫
          (g.hom ((n - 1) - 1)).app X.snd
      simp

end HomologyTheoryData

end TopPair
