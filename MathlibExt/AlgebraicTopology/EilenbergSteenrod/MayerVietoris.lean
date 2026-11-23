/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopPair.OrderedTwoSetCover
public import MathlibExt.Topology.Category.TopPair.Range
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-!
# Abstract Mayer–Vietoris connecting morphism

Coefficient-agnostic Mayer–Vietoris boundary obtained from Eilenberg–Steenrod
excision and the long exact sequence of a pair, natural in ordered two-set covers.
-/

@[expose] public section

namespace TopPair.HomologyTheoryData

open AlgebraicTopology AlgebraicTopology.OrderedTwoSetCover
open CategoryTheory CategoryTheory.Limits

universe w u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace IsExcisive

/-- Excision for an ordered two-set cover, packaged naturally in the cover. -/
noncomputable def orderedTwoSetCoverExcisionNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExcisive] (n : ℤ) :
    rightInterPairFunctor ⋙ E.Hₚ n ≅ spaceLeftPairFunctor ⋙ E.Hₚ n := by
  let α := Functor.whiskerRight excisionNatTrans (E.Hₚ n)
  letI (U : OrderedTwoSetCover.{w}) : IsIso (α.app U) :=
    HomologyTheoryData.IsExcisive.isIso_map_excision
      n U.X U.left U.right U.interior_cover
  exact NatIso.ofComponents (fun U => asIso (α.app U))
    (fun f => α.naturality f)

/-- Excision transports the isomorphism property of a cover morphism between its
right/intersection pair and its ambient/left pair. -/
theorem isIso_map_spaceLeftPairFunctor_map_iff
    (E : HomologyTheoryData.{w} C) [E.IsExcisive] (n : ℤ)
    {U V : OrderedTwoSetCover.{w}} (f : U ⟶ V) :
    IsIso ((E.Hₚ n).map (rightInterPairFunctor.map f)) ↔
      IsIso ((E.Hₚ n).map (spaceLeftPairFunctor.map f)) := by
  simpa only [Functor.comp_map] using
    NatIso.isIso_map_iff (orderedTwoSetCoverExcisionNatIso E n) f

end IsExcisive

/-- The abstract Mayer--Vietoris boundary, natural in ordered covers. -/
noncomputable def mayerVietorisBoundaryNatTrans
    (E : HomologyTheoryData.{w} C) [E.IsExcisive] (n : ℤ) :
    spaceFunctor ⋙ E.H n ⟶ interFunctor ⋙ E.H (n - 1) := by
  let excisionMap := Functor.whiskerRight excisionNatTrans (E.Hₚ n)
  letI (U : OrderedTwoSetCover.{w}) : IsIso (excisionMap.app U) :=
    HomologyTheoryData.IsExcisive.isIso_map_excision
      n U.X U.left U.right U.interior_cover
  let excisionIso :
      rightInterPairFunctor ⋙ E.Hₚ n ≅ spaceLeftPairFunctor ⋙ E.Hₚ n :=
    NatIso.ofComponents
      (fun U => asIso (excisionMap.app U))
      (fun f => excisionMap.naturality f)
  exact
    Functor.whiskerLeft spaceLeftPairFunctor (E.toRelativeNatTrans n) ≫
      excisionIso.inv ≫
        Functor.whiskerLeft rightInterPairFunctor (E.δ n (n - 1))

/-- The abstract Mayer--Vietoris connecting morphism at an ordered cover. -/
noncomputable abbrev mayerVietorisBoundary
    (E : HomologyTheoryData.{w} C) [E.IsExcisive]
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :=
  (E.mayerVietorisBoundaryNatTrans n).app U

/-- The Mayer--Vietoris boundary followed by the range replacement of its
intersection target is the pair boundary after range-normalized inverse
excision. -/
public theorem mayerVietorisBoundary_comp_rangeIso_snd
    (E : HomologyTheoryData.{w} C) [E.IsExcisive]
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    let P := rightInterPairFunctor.obj U
    let e := TopPair.rangeIso P
    let Q := TopPair.rangePair P
    let g : Q ⟶ spaceLeftPairFunctor.obj U :=
      e.inv ≫ excisionNatTrans.app U
    let _ : IsIso ((E.Hₚ n).map g) := by
      dsimp only [g]
      rw [Functor.map_comp]
      let _ : IsIso ((E.Hₚ n).map (excisionNatTrans.app U)) :=
        HomologyTheoryData.IsExcisive.isIso_map_excision
          n U.X U.left U.right U.interior_cover
      infer_instance
    E.mayerVietorisBoundary n U ≫
        (E.H (n - 1)).map (TopPair.Hom.snd e.hom) =
      E.toRelative n (spaceLeftPairFunctor.obj U) ≫
        inv ((E.Hₚ n).map g) ≫ E.boundary n Q := by
  dsimp only
  let P := rightInterPairFunctor.obj U
  let e := TopPair.rangeIso P
  let Q := TopPair.rangePair P
  let f := excisionNatTrans.app U
  let g : Q ⟶ spaceLeftPairFunctor.obj U := e.inv ≫ f
  let _ : IsIso ((E.Hₚ n).map f) :=
    HomologyTheoryData.IsExcisive.isIso_map_excision
      n U.X U.left U.right U.interior_cover
  let _ : IsIso ((E.Hₚ n).map g) := by
    dsimp only [g]
    rw [Functor.map_comp]
    infer_instance
  have hMapG :
      (E.Hₚ n).map g = (E.Hₚ n).map e.inv ≫ (E.Hₚ n).map f := by
    dsimp only [g]
    exact (E.Hₚ n).map_comp e.inv f
  have hInv :
      inv ((E.Hₚ n).map g) =
        inv ((E.Hₚ n).map f) ≫ (E.Hₚ n).map e.hom := by
    apply (cancel_mono ((E.Hₚ n).map g)).1
    rw [IsIso.inv_hom_id, hMapG]
    simp only [Category.assoc, Iso.hom_inv_id_map_assoc,
      IsIso.inv_hom_id]
  have hBoundary :
      (E.Hₚ n).map e.hom ≫ E.boundary n Q =
        E.boundary n P ≫
          (E.H (n - 1)).map (TopPair.Hom.snd e.hom) := by
    exact (E.δ n (n - 1)).naturality e.hom
  have hTail :
      inv ((E.Hₚ n).map f) ≫ E.boundary n P ≫
          (E.H (n - 1)).map (TopPair.Hom.snd e.hom) =
        inv ((E.Hₚ n).map g) ≫ E.boundary n Q := by
    have hBoundaryPre :
        inv ((E.Hₚ n).map f) ≫ E.boundary n P ≫
            (E.H (n - 1)).map (TopPair.Hom.snd e.hom) =
          inv ((E.Hₚ n).map f) ≫
            ((E.Hₚ n).map e.hom ≫ E.boundary n Q) :=
      congrArg (fun m => inv ((E.Hₚ n).map f) ≫ m) hBoundary.symm
    have hAssoc :
        inv ((E.Hₚ n).map f) ≫
            ((E.Hₚ n).map e.hom ≫ E.boundary n Q) =
          (inv ((E.Hₚ n).map f) ≫ (E.Hₚ n).map e.hom) ≫
            E.boundary n Q :=
      (Category.assoc _ _ _).symm
    have hInvPost :
        (inv ((E.Hₚ n).map f) ≫ (E.Hₚ n).map e.hom) ≫
            E.boundary n Q =
          inv ((E.Hₚ n).map g) ≫ E.boundary n Q :=
      congrArg (fun m => m ≫ E.boundary n Q) hInv.symm
    exact hBoundaryPre.trans (hAssoc.trans hInvPost)
  change
    (E.toRelative n (spaceLeftPairFunctor.obj U) ≫
        inv ((E.Hₚ n).map f) ≫ E.boundary n P) ≫
          (E.H (n - 1)).map (TopPair.Hom.snd e.hom) =
      E.toRelative n (spaceLeftPairFunctor.obj U) ≫
        inv ((E.Hₚ n).map g) ≫ E.boundary n Q
  simpa only [Category.assoc] using congrArg
    (fun m => E.toRelative n (spaceLeftPairFunctor.obj U) ≫ m) hTail

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the Mayer--Vietoris boundary in the homology theory. -/
theorem mayerVietorisBoundary_naturality_theory
    {E F : HomologyTheoryData.{w} C}
    [E.IsExcisive] [F.IsExcisive] (f : E ⟶ F)
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    (E.mayerVietorisBoundaryNatTrans n).app U ≫
        (f.hom (n - 1)).app (interFunctor.obj U) =
      (f.hom n).app (spaceFunctor.obj U) ≫
        (F.mayerVietorisBoundaryNatTrans n).app U := by
  let eE := (E.Hₚ n).map (excisionNatTrans.app U)
  let eF := (F.Hₚ n).map (excisionNatTrans.app U)
  let _ : IsIso eE :=
    HomologyTheoryData.IsExcisive.isIso_map_excision
      n U.X U.left U.right U.interior_cover
  let _ : IsIso eF :=
    HomologyTheoryData.IsExcisive.isIso_map_excision
      n U.X U.left U.right U.interior_cover
  have hExcision : eE ≫ (f.homₚ n).app (spaceLeftPairFunctor.obj U) =
      (f.homₚ n).app (rightInterPairFunctor.obj U) ≫ eF :=
    (f.homₚ n).naturality (excisionNatTrans.app U)
  have hInv : (f.homₚ n).app (spaceLeftPairFunctor.obj U) ≫ inv eF =
      inv eE ≫ (f.homₚ n).app (rightInterPairFunctor.obj U) := by
    apply (cancel_epi eE).mp
    calc
      eE ≫ ((f.homₚ n).app (spaceLeftPairFunctor.obj U) ≫ inv eF) =
          (eE ≫ (f.homₚ n).app (spaceLeftPairFunctor.obj U)) ≫ inv eF := by
            rw [Category.assoc]
      _ = ((f.homₚ n).app (rightInterPairFunctor.obj U) ≫ eF) ≫ inv eF := by
            rw [hExcision]
      _ = (f.homₚ n).app (rightInterPairFunctor.obj U) := by simp
      _ = eE ≫ (inv eE ≫ (f.homₚ n).app (rightInterPairFunctor.obj U)) := by
            simp
  have hTo := toRelative_naturality_theory f n (spaceLeftPairFunctor.obj U)
  have hDelta := f.w_app n (n - 1) (rightInterPairFunctor.obj U)
  change (f.hom n).app (spaceFunctor.obj U) ≫
      F.toRelative n (spaceLeftPairFunctor.obj U) =
    E.toRelative n (spaceLeftPairFunctor.obj U) ≫
      (f.homₚ n).app (spaceLeftPairFunctor.obj U) at hTo
  change (E.δ n (n - 1)).app (rightInterPairFunctor.obj U) ≫
      (f.hom (n - 1)).app (interFunctor.obj U) =
    (f.homₚ n).app (rightInterPairFunctor.obj U) ≫
      (F.δ n (n - 1)).app (rightInterPairFunctor.obj U) at hDelta
  change
    (E.toRelative n (spaceLeftPairFunctor.obj U) ≫ inv eE ≫
        (E.δ n (n - 1)).app (rightInterPairFunctor.obj U)) ≫
        (f.hom (n - 1)).app (interFunctor.obj U) =
      (f.hom n).app (spaceFunctor.obj U) ≫
        (F.toRelative n (spaceLeftPairFunctor.obj U) ≫ inv eF ≫
          (F.δ n (n - 1)).app (rightInterPairFunctor.obj U))
  calc
    (E.toRelative n (spaceLeftPairFunctor.obj U) ≫ inv eE ≫
          (E.δ n (n - 1)).app (rightInterPairFunctor.obj U)) ≫
          (f.hom (n - 1)).app (interFunctor.obj U) =
        E.toRelative n (spaceLeftPairFunctor.obj U) ≫ inv eE ≫
          ((E.δ n (n - 1)).app (rightInterPairFunctor.obj U) ≫
            (f.hom (n - 1)).app (interFunctor.obj U)) := by simp only [Category.assoc]
    _ = E.toRelative n (spaceLeftPairFunctor.obj U) ≫ inv eE ≫
          ((f.homₚ n).app (rightInterPairFunctor.obj U) ≫
            (F.δ n (n - 1)).app (rightInterPairFunctor.obj U)) := by rw [hDelta]
    _ = E.toRelative n (spaceLeftPairFunctor.obj U) ≫
          (inv eE ≫ (f.homₚ n).app (rightInterPairFunctor.obj U)) ≫
            (F.δ n (n - 1)).app (rightInterPairFunctor.obj U) := by
          simp only [Category.assoc]
    _ = E.toRelative n (spaceLeftPairFunctor.obj U) ≫
          ((f.homₚ n).app (spaceLeftPairFunctor.obj U) ≫ inv eF) ≫
            (F.δ n (n - 1)).app (rightInterPairFunctor.obj U) := by rw [hInv]
    _ = (E.toRelative n (spaceLeftPairFunctor.obj U) ≫
          (f.homₚ n).app (spaceLeftPairFunctor.obj U)) ≫ inv eF ≫
            (F.δ n (n - 1)).app (rightInterPairFunctor.obj U) := by
          simp only [Category.assoc]
    _ = ((f.hom n).app (spaceFunctor.obj U) ≫
          F.toRelative n (spaceLeftPairFunctor.obj U)) ≫ inv eF ≫
            (F.δ n (n - 1)).app (rightInterPairFunctor.obj U) := by rw [hTo]
    _ = (f.hom n).app (spaceFunctor.obj U) ≫
          (F.toRelative n (spaceLeftPairFunctor.obj U) ≫ inv eF ≫
            (F.δ n (n - 1)).app (rightInterPairFunctor.obj U)) := by
          simp only [Category.assoc]

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

private noncomputable abbrev mvInterFunctor (E : HomologyTheoryData.{w} C) (n : ℤ) :
    OrderedTwoSetCover.{w} ⥤ C :=
  interFunctor ⋙ E.H n

private noncomputable abbrev mvLeftFunctor (E : HomologyTheoryData.{w} C) (n : ℤ) :
    OrderedTwoSetCover.{w} ⥤ C :=
  leftFunctor ⋙ E.H n

private noncomputable abbrev mvRightFunctor (E : HomologyTheoryData.{w} C) (n : ℤ) :
    OrderedTwoSetCover.{w} ⥤ C :=
  rightFunctor ⋙ E.H n

private noncomputable abbrev mvSpaceFunctor (E : HomologyTheoryData.{w} C) (n : ℤ) :
    OrderedTwoSetCover.{w} ⥤ C :=
  spaceFunctor ⋙ E.H n

private noncomputable def mvInterToLeft (E : HomologyTheoryData.{w} C) (n : ℤ) :
    mvInterFunctor E n ⟶ mvLeftFunctor E n :=
  Functor.whiskerRight interToLeft (E.H n)

private noncomputable def mvInterToRight (E : HomologyTheoryData.{w} C) (n : ℤ) :
    mvInterFunctor E n ⟶ mvRightFunctor E n :=
  Functor.whiskerRight interToRight (E.H n)

private noncomputable def mvLeftToSpace (E : HomologyTheoryData.{w} C) (n : ℤ) :
    mvLeftFunctor E n ⟶ mvSpaceFunctor E n :=
  Functor.whiskerRight leftToSpace (E.H n)

private noncomputable def mvRightToSpace (E : HomologyTheoryData.{w} C) (n : ℤ) :
    mvRightFunctor E n ⟶ mvSpaceFunctor E n :=
  Functor.whiskerRight rightToSpace (E.H n)

/-- The functor sending an ordered two-set cover to the biproduct of the degree-`n`
homologies of its two pieces. -/
noncomputable def mayerVietorisPiecesFunctor (E : HomologyTheoryData.{w} C) (n : ℤ) :
    OrderedTwoSetCover.{w} ⥤ C :=
  (pointwiseBinaryBicone (leftFunctor ⋙ E.H n) (rightFunctor ⋙ E.H n)).pt

@[simp]
lemma mayerVietorisPiecesFunctor_obj (E : HomologyTheoryData.{w} C) (n : ℤ)
    (U : OrderedTwoSetCover.{w}) :
    (E.mayerVietorisPiecesFunctor (C := C) n).obj U =
      ((E.H n).obj (leftFunctor.obj U) ⊞ (E.H n).obj (rightFunctor.obj U) : C) :=
  rfl

@[simp]
lemma mayerVietorisPiecesFunctor_map {E : HomologyTheoryData.{w} C} {n : ℤ}
    {U V : OrderedTwoSetCover.{w}} (f : U ⟶ V) :
    (E.mayerVietorisPiecesFunctor (C := C) n).map f =
      biprod.map ((E.H n).map (leftFunctor.map f)) ((E.H n).map (rightFunctor.map f)) :=
  rfl

/-- The Mayer--Vietoris map from the homology of the intersection to the pieces: the
inclusion into the left piece and the negated inclusion into the right piece. -/
noncomputable def mayerVietorisToPiecesNatTrans (E : HomologyTheoryData.{w} C) (n : ℤ) :
    interFunctor ⋙ E.H n ⟶ E.mayerVietorisPiecesFunctor (C := C) n where
  app U := biprod.lift ((E.H n).map (interToLeft.app U)) (-((E.H n).map (interToRight.app U)))
  naturality U V f := by
    change (interFunctor ⋙ E.H n).map f ≫
        biprod.lift ((E.H n).map (interToLeft.app V)) (-((E.H n).map (interToRight.app V))) =
      biprod.lift ((E.H n).map (interToLeft.app U)) (-((E.H n).map (interToRight.app U))) ≫
        biprod.map ((E.H n).map (leftFunctor.map f)) ((E.H n).map (rightFunctor.map f))
    apply biprod.hom_ext
    · simp only [biprod.lift_fst, biprod.lift_fst_assoc, biprod.map_fst,
        Category.assoc]
      have h := (mvInterToLeft (C := C) E n).naturality f
      simp only [mvInterFunctor, mvLeftFunctor, mvInterToLeft, Functor.whiskerRight_app] at h
      exact h
    · simp only [biprod.lift_snd, biprod.lift_snd_assoc, biprod.map_snd,
        Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp]
      have h := (mvInterToRight (C := C) E n).naturality f
      simp only [mvInterFunctor, mvRightFunctor, mvInterToRight, Functor.whiskerRight_app] at h
      exact congrArg Neg.neg h

@[simp]
lemma mayerVietorisToPiecesNatTrans_app (E : HomologyTheoryData.{w} C) (n : ℤ)
    (U : OrderedTwoSetCover.{w}) :
    (E.mayerVietorisToPiecesNatTrans (C := C) n).app U =
      biprod.lift ((E.H n).map (interToLeft.app U)) (-((E.H n).map (interToRight.app U))) :=
  rfl

/-- The Mayer--Vietoris map from the pieces to the whole space: the sum of the maps
induced by the two inclusions. -/
noncomputable def mayerVietorisToUnionNatTrans (E : HomologyTheoryData.{w} C) (n : ℤ) :
    E.mayerVietorisPiecesFunctor (C := C) n ⟶ spaceFunctor ⋙ E.H n where
  app U := biprod.desc ((E.H n).map (leftToSpace.app U)) ((E.H n).map (rightToSpace.app U))
  naturality U V f := by
    change biprod.map ((E.H n).map (leftFunctor.map f)) ((E.H n).map (rightFunctor.map f)) ≫
        biprod.desc ((E.H n).map (leftToSpace.app V)) ((E.H n).map (rightToSpace.app V)) =
      biprod.desc ((E.H n).map (leftToSpace.app U)) ((E.H n).map (rightToSpace.app U)) ≫
        (spaceFunctor ⋙ E.H n).map f
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
      have h := (mvLeftToSpace (C := C) E n).naturality f
      simp only [mvLeftFunctor, mvSpaceFunctor, mvLeftToSpace, Functor.whiskerRight_app] at h
      exact h
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
      have h := (mvRightToSpace (C := C) E n).naturality f
      simp only [mvRightFunctor, mvSpaceFunctor, mvRightToSpace, Functor.whiskerRight_app] at h
      exact h

@[simp]
lemma mayerVietorisToUnionNatTrans_app (E : HomologyTheoryData.{w} C) (n : ℤ)
    (U : OrderedTwoSetCover.{w}) :
    (E.mayerVietorisToUnionNatTrans (C := C) n).app U =
      biprod.desc ((E.H n).map (leftToSpace.app U)) ((E.H n).map (rightToSpace.app U)) :=
  rfl

/-- The five-term Mayer--Vietoris sequence of an ordered two-set cover, from degree `n`
of the intersection to degree `n - 1` of the pieces. -/
noncomputable def mayerVietorisSequence (E : HomologyTheoryData.{w} C) [E.IsExcisive]
    (n : ℤ) (U : OrderedTwoSetCover.{w}) : ComposableArrows C 4 :=
  ComposableArrows.mk₄
    ((E.mayerVietorisToPiecesNatTrans (C := C) n).app U)
    ((E.mayerVietorisToUnionNatTrans (C := C) n).app U)
    ((E.mayerVietorisBoundaryNatTrans n).app U)
    ((E.mayerVietorisToPiecesNatTrans (C := C) (n - 1)).app U)

/-- The Mayer--Vietoris sequence, functorial in the ordered two-set cover. -/
noncomputable def mayerVietorisSequenceFunctor (E : HomologyTheoryData.{w} C) [E.IsExcisive]
    (n : ℤ) : OrderedTwoSetCover.{w} ⥤ ComposableArrows C 4 where
  obj U := E.mayerVietorisSequence (C := C) n U
  map {U V} f :=
    ComposableArrows.homMk₄
      ((interFunctor ⋙ E.H n).map f)
      ((E.mayerVietorisPiecesFunctor (C := C) n).map f)
      ((spaceFunctor ⋙ E.H n).map f)
      ((interFunctor ⋙ E.H (n - 1)).map f)
      ((E.mayerVietorisPiecesFunctor (C := C) (n - 1)).map f)
      (by exact ((E.mayerVietorisToPiecesNatTrans (C := C) n).naturality f).symm)
      (by exact ((E.mayerVietorisToUnionNatTrans (C := C) n).naturality f).symm)
      (by exact ((E.mayerVietorisBoundaryNatTrans n).naturality f).symm)
      (by exact ((E.mayerVietorisToPiecesNatTrans (C := C) (n - 1)).naturality f).symm)
  map_id U := by
    apply ComposableArrows.hom_ext₄
    · change (mvInterFunctor (C := C) E n).map (𝟙 U) = 𝟙 _
      exact (mvInterFunctor (C := C) E n).map_id U
    · change (E.mayerVietorisPiecesFunctor (C := C) n).map (𝟙 U) = 𝟙 _
      exact (E.mayerVietorisPiecesFunctor (C := C) n).map_id U
    · change (mvSpaceFunctor (C := C) E n).map (𝟙 U) = 𝟙 _
      exact (mvSpaceFunctor (C := C) E n).map_id U
    · change (mvInterFunctor (C := C) E (n - 1)).map (𝟙 U) = 𝟙 _
      exact (mvInterFunctor (C := C) E (n - 1)).map_id U
    · change (E.mayerVietorisPiecesFunctor (C := C) (n - 1)).map (𝟙 U) = 𝟙 _
      exact (E.mayerVietorisPiecesFunctor (C := C) (n - 1)).map_id U
  map_comp {U V W} f g := by
    apply ComposableArrows.hom_ext₄
    · change (mvInterFunctor (C := C) E n).map (f ≫ g) =
        (mvInterFunctor (C := C) E n).map f ≫ (mvInterFunctor (C := C) E n).map g
      exact (mvInterFunctor (C := C) E n).map_comp f g
    · change (E.mayerVietorisPiecesFunctor (C := C) n).map (f ≫ g) =
        (E.mayerVietorisPiecesFunctor (C := C) n).map f ≫
          (E.mayerVietorisPiecesFunctor (C := C) n).map g
      exact (E.mayerVietorisPiecesFunctor (C := C) n).map_comp f g
    · change (mvSpaceFunctor (C := C) E n).map (f ≫ g) =
        (mvSpaceFunctor (C := C) E n).map f ≫ (mvSpaceFunctor (C := C) E n).map g
      exact (mvSpaceFunctor (C := C) E n).map_comp f g
    · change (mvInterFunctor (C := C) E (n - 1)).map (f ≫ g) =
        (mvInterFunctor (C := C) E (n - 1)).map f ≫ (mvInterFunctor (C := C) E (n - 1)).map g
      exact (mvInterFunctor (C := C) E (n - 1)).map_comp f g
    · change (E.mayerVietorisPiecesFunctor (C := C) (n - 1)).map (f ≫ g) =
        (E.mayerVietorisPiecesFunctor (C := C) (n - 1)).map f ≫
          (E.mayerVietorisPiecesFunctor (C := C) (n - 1)).map g
      exact (E.mayerVietorisPiecesFunctor (C := C) (n - 1)).map_comp f g

@[simp]
lemma mayerVietorisSequenceFunctor_obj (E : HomologyTheoryData.{w} C) [E.IsExcisive]
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    (E.mayerVietorisSequenceFunctor (C := C) n).obj U = E.mayerVietorisSequence (C := C) n U :=
  rfl

private lemma mvBiprodMapComp {A B A' B' A'' B'' : C}
    (f : A ⟶ A') (g : B ⟶ B') (f' : A' ⟶ A'') (g' : B' ⟶ B'') :
    biprod.map f g ≫ biprod.map f' g' = biprod.map (f ≫ f') (g ≫ g') := by
  apply biprod.hom_ext' <;> simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of Mayer--Vietoris sequences induced by a theory morphism. -/
noncomputable def mayerVietorisSequenceHom
    {E F : HomologyTheoryData.{w} C}
    [E.IsExcisive] [F.IsExcisive] (f : E ⟶ F)
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    E.mayerVietorisSequence n U ⟶ F.mayerVietorisSequence n U :=
  ComposableArrows.homMk₄
    ((f.hom n).app (interFunctor.obj U))
    (biprod.map ((f.hom n).app (leftFunctor.obj U))
      ((f.hom n).app (rightFunctor.obj U)))
    ((f.hom n).app (spaceFunctor.obj U))
    ((f.hom (n - 1)).app (interFunctor.obj U))
    (biprod.map ((f.hom (n - 1)).app (leftFunctor.obj U))
      ((f.hom (n - 1)).app (rightFunctor.obj U)))
    (by
      change biprod.lift ((E.H n).map (interToLeft.app U))
            (-((E.H n).map (interToRight.app U))) ≫
          biprod.map ((f.hom n).app (leftFunctor.obj U))
            ((f.hom n).app (rightFunctor.obj U)) =
        (f.hom n).app (interFunctor.obj U) ≫
          biprod.lift ((F.H n).map (interToLeft.app U))
            (-((F.H n).map (interToRight.app U)))
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.map_fst, ← Category.assoc,
          biprod.lift_fst, Category.assoc, biprod.lift_fst]
        exact (f.hom n).naturality (interToLeft.app U)
      · rw [Category.assoc, biprod.map_snd, ← Category.assoc,
          biprod.lift_snd, Category.assoc, biprod.lift_snd,
          Preadditive.comp_neg, Preadditive.neg_comp]
        rw [(f.hom n).naturality (interToRight.app U)])
    (by
      change biprod.desc ((E.H n).map (leftToSpace.app U))
            ((E.H n).map (rightToSpace.app U)) ≫
          (f.hom n).app (spaceFunctor.obj U) =
        biprod.map ((f.hom n).app (leftFunctor.obj U))
            ((f.hom n).app (rightFunctor.obj U)) ≫
          biprod.desc ((F.H n).map (leftToSpace.app U))
            ((F.H n).map (rightToSpace.app U))
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
        exact (f.hom n).naturality (leftToSpace.app U)
      · rw [biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc]
        exact (f.hom n).naturality (rightToSpace.app U))
    (mayerVietorisBoundary_naturality_theory f n U)
    (by
      change biprod.lift ((E.H (n - 1)).map (interToLeft.app U))
            (-((E.H (n - 1)).map (interToRight.app U))) ≫
          biprod.map ((f.hom (n - 1)).app (leftFunctor.obj U))
            ((f.hom (n - 1)).app (rightFunctor.obj U)) =
        (f.hom (n - 1)).app (interFunctor.obj U) ≫
          biprod.lift ((F.H (n - 1)).map (interToLeft.app U))
            (-((F.H (n - 1)).map (interToRight.app U)))
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.map_fst, ← Category.assoc,
          biprod.lift_fst, Category.assoc, biprod.lift_fst]
        exact (f.hom (n - 1)).naturality (interToLeft.app U)
      · rw [Category.assoc, biprod.map_snd, ← Category.assoc,
          biprod.lift_snd, Category.assoc, biprod.lift_snd,
          Preadditive.comp_neg, Preadditive.neg_comp]
        rw [(f.hom (n - 1)).naturality (interToRight.app U)])

set_option backward.isDefEq.respectTransparency false in
/-- Natural transformation of Mayer--Vietoris sequence functors induced by a theory morphism. -/
noncomputable def mayerVietorisSequenceNatTrans
    {E F : HomologyTheoryData.{w} C}
    [E.IsExcisive] [F.IsExcisive] (f : E ⟶ F) (n : ℤ) :
    E.mayerVietorisSequenceFunctor n ⟶ F.mayerVietorisSequenceFunctor n where
  app U := mayerVietorisSequenceHom f n U
  naturality U V g := by
    apply ComposableArrows.hom_ext₄
    · change (E.H n).map (interFunctor.map g) ≫
          (f.hom n).app (interFunctor.obj V) =
        (f.hom n).app (interFunctor.obj U) ≫ (F.H n).map (interFunctor.map g)
      exact (f.hom n).naturality (interFunctor.map g)
    · change biprod.map ((E.H n).map (leftFunctor.map g))
            ((E.H n).map (rightFunctor.map g)) ≫
          biprod.map ((f.hom n).app (leftFunctor.obj V))
            ((f.hom n).app (rightFunctor.obj V)) =
        biprod.map ((f.hom n).app (leftFunctor.obj U))
            ((f.hom n).app (rightFunctor.obj U)) ≫
          biprod.map ((F.H n).map (leftFunctor.map g))
            ((F.H n).map (rightFunctor.map g))
      rw [mvBiprodMapComp, mvBiprodMapComp,
        (f.hom n).naturality (leftFunctor.map g),
        (f.hom n).naturality (rightFunctor.map g)]
    · change (E.H n).map (spaceFunctor.map g) ≫
          (f.hom n).app (spaceFunctor.obj V) =
        (f.hom n).app (spaceFunctor.obj U) ≫ (F.H n).map (spaceFunctor.map g)
      exact (f.hom n).naturality (spaceFunctor.map g)
    · change (E.H (n - 1)).map (interFunctor.map g) ≫
          (f.hom (n - 1)).app (interFunctor.obj V) =
        (f.hom (n - 1)).app (interFunctor.obj U) ≫
          (F.H (n - 1)).map (interFunctor.map g)
      exact (f.hom (n - 1)).naturality (interFunctor.map g)
    · change biprod.map ((E.H (n - 1)).map (leftFunctor.map g))
            ((E.H (n - 1)).map (rightFunctor.map g)) ≫
          biprod.map ((f.hom (n - 1)).app (leftFunctor.obj V))
            ((f.hom (n - 1)).app (rightFunctor.obj V)) =
        biprod.map ((f.hom (n - 1)).app (leftFunctor.obj U))
            ((f.hom (n - 1)).app (rightFunctor.obj U)) ≫
          biprod.map ((F.H (n - 1)).map (leftFunctor.map g))
            ((F.H (n - 1)).map (rightFunctor.map g))
      rw [mvBiprodMapComp, mvBiprodMapComp,
        (f.hom (n - 1)).naturality (leftFunctor.map g),
        (f.hom (n - 1)).naturality (rightFunctor.map g)]

set_option backward.isDefEq.respectTransparency false in
/-- The Mayer--Vietoris sequence, functorial in both the excisive homology theory and the
cover. -/
noncomputable def mayerVietorisSequenceBifunctor (n : ℤ) :
    (isExcisive (C := C)).FullSubcategory ⥤
      (OrderedTwoSetCover.{w} ⥤ ComposableArrows C 4) where
  obj E :=
    letI : E.obj.IsExcisive := E.property
    E.obj.mayerVietorisSequenceFunctor (C := C) n
  map {E F} f :=
    letI : E.obj.IsExcisive := E.property
    letI : F.obj.IsExcisive := F.property
    mayerVietorisSequenceNatTrans (C := C) f.hom n
  map_id E := by
    let : E.obj.IsExcisive := E.property
    apply NatTrans.ext
    ext U
    · change ((HomologyPretheory.Hom.hom (𝟙 E.obj) n).app (interFunctor.obj U)) = 𝟙 _
      simp
    · change biprod.map ((HomologyPretheory.Hom.hom (𝟙 E.obj) n).app (leftFunctor.obj U))
          ((HomologyPretheory.Hom.hom (𝟙 E.obj) n).app (rightFunctor.obj U)) = 𝟙 _
      apply biprod.hom_ext <;> simp
    · change ((HomologyPretheory.Hom.hom (𝟙 E.obj) n).app (spaceFunctor.obj U)) = 𝟙 _
      simp
    · change ((HomologyPretheory.Hom.hom (𝟙 E.obj) (n - 1)).app (interFunctor.obj U)) = 𝟙 _
      simp
    · change biprod.map ((HomologyPretheory.Hom.hom (𝟙 E.obj) (n - 1)).app (leftFunctor.obj U))
          ((HomologyPretheory.Hom.hom (𝟙 E.obj) (n - 1)).app (rightFunctor.obj U)) = 𝟙 _
      apply biprod.hom_ext <;> simp
  map_comp {E F G} f g := by
    let : E.obj.IsExcisive := E.property
    let : F.obj.IsExcisive := F.property
    let : G.obj.IsExcisive := G.property
    apply NatTrans.ext
    ext U
    · change ((HomologyPretheory.Hom.hom (f.hom ≫ g.hom) n).app (interFunctor.obj U)) =
          (HomologyPretheory.Hom.hom f.hom n).app (interFunctor.obj U) ≫
            (HomologyPretheory.Hom.hom g.hom n).app (interFunctor.obj U)
      simp
    · change biprod.map ((HomologyPretheory.Hom.hom (f.hom ≫ g.hom) n).app (leftFunctor.obj U))
            ((HomologyPretheory.Hom.hom (f.hom ≫ g.hom) n).app (rightFunctor.obj U)) =
          biprod.map ((HomologyPretheory.Hom.hom f.hom n).app (leftFunctor.obj U))
            ((HomologyPretheory.Hom.hom f.hom n).app (rightFunctor.obj U)) ≫
          biprod.map ((HomologyPretheory.Hom.hom g.hom n).app (leftFunctor.obj U))
            ((HomologyPretheory.Hom.hom g.hom n).app (rightFunctor.obj U))
      apply biprod.hom_ext <;> simp
    · change ((HomologyPretheory.Hom.hom (f.hom ≫ g.hom) n).app (spaceFunctor.obj U)) =
          (HomologyPretheory.Hom.hom f.hom n).app (spaceFunctor.obj U) ≫
            (HomologyPretheory.Hom.hom g.hom n).app (spaceFunctor.obj U)
      simp
    · change ((HomologyPretheory.Hom.hom (f.hom ≫ g.hom) (n - 1)).app (interFunctor.obj U)) =
          (HomologyPretheory.Hom.hom f.hom (n - 1)).app (interFunctor.obj U) ≫
            (HomologyPretheory.Hom.hom g.hom (n - 1)).app (interFunctor.obj U)
      simp
    · change biprod.map
          ((HomologyPretheory.Hom.hom (f.hom ≫ g.hom) (n - 1)).app (leftFunctor.obj U))
            ((HomologyPretheory.Hom.hom (f.hom ≫ g.hom) (n - 1)).app (rightFunctor.obj U)) =
          biprod.map ((HomologyPretheory.Hom.hom f.hom (n - 1)).app (leftFunctor.obj U))
            ((HomologyPretheory.Hom.hom f.hom (n - 1)).app (rightFunctor.obj U)) ≫
          biprod.map ((HomologyPretheory.Hom.hom g.hom (n - 1)).app (leftFunctor.obj U))
            ((HomologyPretheory.Hom.hom g.hom (n - 1)).app (rightFunctor.obj U))
      apply biprod.hom_ext <;> simp

@[simp]
lemma mayerVietorisSequenceBifunctor_obj_obj
    (E : (isExcisive (C := C)).FullSubcategory)
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    ((mayerVietorisSequenceBifunctor (C := C) n).obj E).obj U =
      @mayerVietorisSequence _ _ _ _ E.obj E.property n U :=
  rfl

@[simp]
lemma mayerVietorisSequenceBifunctor_map_app
    {E F : (isExcisive (C := C)).FullSubcategory} (f : E ⟶ F)
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    ((mayerVietorisSequenceBifunctor (C := C) n).map f).app U =
      @mayerVietorisSequenceHom _ _ _ _ E.obj F.obj
        E.property F.property f.hom n U :=
  rfl

end

end TopPair.HomologyTheoryData
