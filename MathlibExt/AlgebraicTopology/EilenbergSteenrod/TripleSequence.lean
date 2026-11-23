/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequence
public import MathlibExt.Topology.Category.TopPair.Triple

/-!
# Triple sequences in a homology theory

This file defines the composite triple boundary and the object-level
five-arrow sequence for a homology theory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TopPair.HomologyTheoryData

open AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The composite triple boundary as a natural transformation
`Hₙ(X, A) ⟶ Hₙ₋₁(A, B)` obtained from `δ` followed by `toRelative`. -/
noncomputable def tripleBoundaryNatTrans
    (E : HomologyTheoryData.{w} C) (n : ℤ) :
    topTriplePair12.{w} ⋙ E.Hₚ n ⟶
      topTriplePair01.{w} ⋙ E.Hₚ (n - 1) :=
  Functor.whiskerLeft topTriplePair12 (E.δ n (n - 1)) ≫
    Functor.whiskerLeft topTriplePair01 (E.toRelativeNatTrans (n - 1))

/-- The app of `tripleBoundaryNatTrans` is the composite `boundary ≫ toRelative`. -/
@[simp] lemma tripleBoundaryNatTrans_app
    (E : HomologyTheoryData.{w} C) (n : ℤ) (T : TopTriple.{w}) :
    (E.tripleBoundaryNatTrans n).app T =
      E.boundary n (topTriplePair12.obj T) ≫
        E.toRelative (n - 1) (topTriplePair01.obj T) := rfl

/-- The object-level five-arrow triple sequence
`Hₙ(A,B) → Hₙ(X,B) → Hₙ(X,A) → Hₙ₋₁(A,B) → Hₙ₋₁(X,B)`. -/
noncomputable def tripleSequence
    (E : HomologyTheoryData.{w} C) (n : ℤ) (T : TopTriple.{w}) :
    ComposableArrows C 4 :=
  ComposableArrows.mk₄
    ((E.Hₚ n).map (topTriplePair01To02.app T))
    ((E.Hₚ n).map (topTriplePair02To12.app T))
    ((E.tripleBoundaryNatTrans n).app T)
    ((E.Hₚ (n - 1)).map (topTriplePair01To02.app T))

set_option backward.isDefEq.respectTransparency false in
/-- The triple sequence as a functor in the triple. -/
noncomputable def tripleSequenceFunctor
    (E : HomologyTheoryData.{w} C) (n : ℤ) :
    TopTriple.{w} ⥤ ComposableArrows C 4 where
  obj T := E.tripleSequence n T
  map {T U} f :=
    ComposableArrows.homMk₄
      ((topTriplePair01 ⋙ E.Hₚ n).map f)
      ((topTriplePair02 ⋙ E.Hₚ n).map f)
      ((topTriplePair12 ⋙ E.Hₚ n).map f)
      ((topTriplePair01 ⋙ E.Hₚ (n - 1)).map f)
      ((topTriplePair02 ⋙ E.Hₚ (n - 1)).map f)
      ((Functor.whiskerRight topTriplePair01To02 (E.Hₚ n)).naturality f).symm
      ((Functor.whiskerRight topTriplePair02To12 (E.Hₚ n)).naturality f).symm
      ((E.tripleBoundaryNatTrans n).naturality f).symm
      ((Functor.whiskerRight topTriplePair01To02 (E.Hₚ (n - 1))).naturality f).symm
  map_id T := by
    apply ComposableArrows.hom_ext₄
    · change ((topTriplePair01 ⋙ E.Hₚ n).map (𝟙 T) = 𝟙 _)
      simp
    · change ((topTriplePair02 ⋙ E.Hₚ n).map (𝟙 T) = 𝟙 _)
      simp
    · change ((topTriplePair12 ⋙ E.Hₚ n).map (𝟙 T) = 𝟙 _)
      simp
    · change ((topTriplePair01 ⋙ E.Hₚ (n - 1)).map (𝟙 T) = 𝟙 _)
      simp
    · change ((topTriplePair02 ⋙ E.Hₚ (n - 1)).map (𝟙 T) = 𝟙 _)
      simp
  map_comp {T U V} f g := by
    apply ComposableArrows.hom_ext₄
    · change ((topTriplePair01 ⋙ E.Hₚ n).map (f ≫ g) =
          ((topTriplePair01 ⋙ E.Hₚ n).map f ≫
            (topTriplePair01 ⋙ E.Hₚ n).map g))
      exact (topTriplePair01 ⋙ E.Hₚ n).map_comp f g
    · change ((topTriplePair02 ⋙ E.Hₚ n).map (f ≫ g) =
          ((topTriplePair02 ⋙ E.Hₚ n).map f ≫
            (topTriplePair02 ⋙ E.Hₚ n).map g))
      exact (topTriplePair02 ⋙ E.Hₚ n).map_comp f g
    · change ((topTriplePair12 ⋙ E.Hₚ n).map (f ≫ g) =
          ((topTriplePair12 ⋙ E.Hₚ n).map f ≫
            (topTriplePair12 ⋙ E.Hₚ n).map g))
      exact (topTriplePair12 ⋙ E.Hₚ n).map_comp f g
    · change ((topTriplePair01 ⋙ E.Hₚ (n - 1)).map (f ≫ g) =
          ((topTriplePair01 ⋙ E.Hₚ (n - 1)).map f ≫
            (topTriplePair01 ⋙ E.Hₚ (n - 1)).map g))
      exact (topTriplePair01 ⋙ E.Hₚ (n - 1)).map_comp f g
    · change ((topTriplePair02 ⋙ E.Hₚ (n - 1)).map (f ≫ g) =
          ((topTriplePair02 ⋙ E.Hₚ (n - 1)).map f ≫
            (topTriplePair02 ⋙ E.Hₚ (n - 1)).map g))
      exact (topTriplePair02 ⋙ E.Hₚ (n - 1)).map_comp f g

/-- The object part of `tripleSequenceFunctor` is `tripleSequence`. -/
@[simp] lemma tripleSequenceFunctor_obj
    (E : HomologyTheoryData.{w} C) (n : ℤ) (T : TopTriple.{w}) :
    (E.tripleSequenceFunctor n).obj T = E.tripleSequence n T := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of triple sequences induced by a morphism of homology theories. -/
noncomputable def tripleSequenceHom {E F : HomologyTheoryData.{w} C}
    (f : E ⟶ F) (n : ℤ) (T : TopTriple.{w}) :
    E.tripleSequence n T ⟶ F.tripleSequence n T :=
  ComposableArrows.homMk₄
    ((f.homₚ n).app (topTriplePair01.obj T))
    ((f.homₚ n).app (topTriplePair02.obj T))
    ((f.homₚ n).app (topTriplePair12.obj T))
    ((f.homₚ (n - 1)).app (topTriplePair01.obj T))
    ((f.homₚ (n - 1)).app (topTriplePair02.obj T))
    (by
      change (E.Hₚ n).map (topTriplePair01To02.app T) ≫
          (f.homₚ n).app (topTriplePair02.obj T) =
        (f.homₚ n).app (topTriplePair01.obj T) ≫
          (F.Hₚ n).map (topTriplePair01To02.app T)
      exact (f.homₚ n).naturality (topTriplePair01To02.app T))
    (by
      change (E.Hₚ n).map (topTriplePair02To12.app T) ≫
          (f.homₚ n).app (topTriplePair12.obj T) =
        (f.homₚ n).app (topTriplePair02.obj T) ≫
          (F.Hₚ n).map (topTriplePair02To12.app T)
      exact (f.homₚ n).naturality (topTriplePair02To12.app T))
    (by
      have h₁ := ComposableArrows.naturality'
        (pairSequenceHom f n (topTriplePair01.obj T)) 2 3
      have h₂ := f.w_app n (n - 1) (topTriplePair12.obj T)
      change E.toRelative (n - 1) (topTriplePair01.obj T) ≫
          (f.homₚ (n - 1)).app (topTriplePair01.obj T) =
        (f.hom (n - 1)).app (topTriplePair01.obj T).fst ≫
          F.toRelative (n - 1) (topTriplePair01.obj T) at h₁
      change (E.δ n (n - 1)).app (topTriplePair12.obj T) ≫
          (f.hom (n - 1)).app (topTriplePair01.obj T).fst =
        (f.homₚ n).app (topTriplePair12.obj T) ≫
          (F.δ n (n - 1)).app (topTriplePair12.obj T) at h₂
      calc (E.tripleBoundaryNatTrans n).app T ≫
            (f.homₚ (n - 1)).app (topTriplePair01.obj T)
          = ((E.δ n (n - 1)).app (topTriplePair12.obj T) ≫
              E.toRelative (n - 1) (topTriplePair01.obj T)) ≫
              (f.homₚ (n - 1)).app (topTriplePair01.obj T) := rfl
        _ = (E.δ n (n - 1)).app (topTriplePair12.obj T) ≫
              (E.toRelative (n - 1) (topTriplePair01.obj T) ≫
                (f.homₚ (n - 1)).app (topTriplePair01.obj T)) := by
          simp only [Category.assoc]
        _ = (E.δ n (n - 1)).app (topTriplePair12.obj T) ≫
              ((f.hom (n - 1)).app (topTriplePair01.obj T).fst ≫
                F.toRelative (n - 1) (topTriplePair01.obj T)) := by
          rw [h₁]
        _ = ((E.δ n (n - 1)).app (topTriplePair12.obj T) ≫
              (f.hom (n - 1)).app (topTriplePair01.obj T).fst) ≫
              F.toRelative (n - 1) (topTriplePair01.obj T) := by
          simp only [Category.assoc]
        _ = ((f.homₚ n).app (topTriplePair12.obj T) ≫
              (F.δ n (n - 1)).app (topTriplePair12.obj T)) ≫
              F.toRelative (n - 1) (topTriplePair01.obj T) := by
          rw [h₂]
        _ = (f.homₚ n).app (topTriplePair12.obj T) ≫
              ((F.δ n (n - 1)).app (topTriplePair12.obj T) ≫
                F.toRelative (n - 1) (topTriplePair01.obj T)) := by
          simp only [Category.assoc]
        _ = (f.homₚ n).app (topTriplePair12.obj T) ≫
              (F.tripleBoundaryNatTrans n).app T := rfl)
    (by
      change (E.Hₚ (n - 1)).map (topTriplePair01To02.app T) ≫
          (f.homₚ (n - 1)).app (topTriplePair02.obj T) =
        (f.homₚ (n - 1)).app (topTriplePair01.obj T) ≫
          (F.Hₚ (n - 1)).map (topTriplePair01To02.app T)
      exact (f.homₚ (n - 1)).naturality (topTriplePair01To02.app T))

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation of triple-sequence functors induced by such a theory morphism. -/
noncomputable def tripleSequenceNatTrans {E F : HomologyTheoryData.{w} C}
    (f : E ⟶ F) (n : ℤ) :
    E.tripleSequenceFunctor n ⟶ F.tripleSequenceFunctor n where
  app T := tripleSequenceHom f n T
  naturality T U g := by
    apply ComposableArrows.hom_ext₄
    · change (E.Hₚ n).map (topTriplePair01.map g) ≫
          (f.homₚ n).app (topTriplePair01.obj U) =
        (f.homₚ n).app (topTriplePair01.obj T) ≫
          (F.Hₚ n).map (topTriplePair01.map g)
      exact (f.homₚ n).naturality (topTriplePair01.map g)
    · change (E.Hₚ n).map (topTriplePair02.map g) ≫
          (f.homₚ n).app (topTriplePair02.obj U) =
        (f.homₚ n).app (topTriplePair02.obj T) ≫
          (F.Hₚ n).map (topTriplePair02.map g)
      exact (f.homₚ n).naturality (topTriplePair02.map g)
    · change (E.Hₚ n).map (topTriplePair12.map g) ≫
          (f.homₚ n).app (topTriplePair12.obj U) =
        (f.homₚ n).app (topTriplePair12.obj T) ≫
          (F.Hₚ n).map (topTriplePair12.map g)
      exact (f.homₚ n).naturality (topTriplePair12.map g)
    · change (E.Hₚ (n - 1)).map (topTriplePair01.map g) ≫
          (f.homₚ (n - 1)).app (topTriplePair01.obj U) =
        (f.homₚ (n - 1)).app (topTriplePair01.obj T) ≫
          (F.Hₚ (n - 1)).map (topTriplePair01.map g)
      exact (f.homₚ (n - 1)).naturality (topTriplePair01.map g)
    · change (E.Hₚ (n - 1)).map (topTriplePair02.map g) ≫
          (f.homₚ (n - 1)).app (topTriplePair02.obj U) =
        (f.homₚ (n - 1)).app (topTriplePair02.obj T) ≫
          (F.Hₚ (n - 1)).map (topTriplePair02.map g)
      exact (f.homₚ (n - 1)).naturality (topTriplePair02.map g)

set_option backward.isDefEq.respectTransparency false in
/-- Triple sequences as a bifunctor of the homology theory and topological triple. -/
noncomputable def tripleSequenceBifunctor (n : ℤ) :
    HomologyTheoryData.{w} C ⥤ (TopTriple.{w} ⥤ ComposableArrows C 4) where
  obj E := E.tripleSequenceFunctor n
  map f := tripleSequenceNatTrans f n
  map_id E := by
    apply NatTrans.ext
    ext T
    · change ((𝟙 E : E ⟶ E).homₚ n).app (topTriplePair01.obj T) = 𝟙 _
      simp
    · change ((𝟙 E : E ⟶ E).homₚ n).app (topTriplePair02.obj T) = 𝟙 _
      simp
    · change ((𝟙 E : E ⟶ E).homₚ n).app (topTriplePair12.obj T) = 𝟙 _
      simp
    · change ((𝟙 E : E ⟶ E).homₚ (n - 1)).app (topTriplePair01.obj T) = 𝟙 _
      simp
    · change ((𝟙 E : E ⟶ E).homₚ (n - 1)).app (topTriplePair02.obj T) = 𝟙 _
      simp
  map_comp {E F G} f g := by
    apply NatTrans.ext
    ext T
    · change ((f ≫ g).homₚ n).app (topTriplePair01.obj T) =
        (f.homₚ n).app (topTriplePair01.obj T) ≫
          (g.homₚ n).app (topTriplePair01.obj T)
      simp
    · change ((f ≫ g).homₚ n).app (topTriplePair02.obj T) =
        (f.homₚ n).app (topTriplePair02.obj T) ≫
          (g.homₚ n).app (topTriplePair02.obj T)
      simp
    · change ((f ≫ g).homₚ n).app (topTriplePair12.obj T) =
        (f.homₚ n).app (topTriplePair12.obj T) ≫
          (g.homₚ n).app (topTriplePair12.obj T)
      simp
    · change ((f ≫ g).homₚ (n - 1)).app (topTriplePair01.obj T) =
        (f.homₚ (n - 1)).app (topTriplePair01.obj T) ≫
          (g.homₚ (n - 1)).app (topTriplePair01.obj T)
      simp
    · change ((f ≫ g).homₚ (n - 1)).app (topTriplePair02.obj T) =
        (f.homₚ (n - 1)).app (topTriplePair02.obj T) ≫
          (g.homₚ (n - 1)).app (topTriplePair02.obj T)
      simp

@[simp] lemma tripleSequenceBifunctor_obj
    (E : HomologyTheoryData.{w} C) (n : ℤ) :
    (tripleSequenceBifunctor (C := C) n).obj E =
      E.tripleSequenceFunctor n :=
  rfl

@[simp] lemma tripleSequenceBifunctor_map_app
    {E F : HomologyTheoryData.{w} C}
    (f : E ⟶ F) (n : ℤ) (T : TopTriple.{w}) :
    ((tripleSequenceBifunctor (C := C) n).map f).app T =
      tripleSequenceHom f n T :=
  rfl

end TopPair.HomologyTheoryData
