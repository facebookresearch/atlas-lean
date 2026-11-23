/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Contractible
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.MayerVietoris
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceExact
public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.Braid

/-!
# Exact Mayer--Vietoris sequences

Exactness of the abstract Mayer--Vietoris sequence, derived from the
Eilenberg--Steenrod exactness and excision axioms via the exact braid lemma.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TopPair.HomologyTheoryData

open AlgebraicTopology AlgebraicTopology.OrderedTwoSetCover

universe w u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private noncomputable def mvNegIso (X : C) : X ≅ X where
  hom := -𝟙 X
  inv := -𝟙 X
  hom_inv_id := by simp
  inv_hom_id := by simp

private lemma mvExactNegF {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : f ≫ g = 0) (h : (ShortComplex.mk f g hfg).Exact) :
    (ShortComplex.mk (-f) g (by simp [hfg])).Exact := by
  let S := ShortComplex.mk f g hfg
  let T := ShortComplex.mk (-f) g (by simp [hfg])
  let e : S ≅ T := ShortComplex.isoMk (mvNegIso X) (Iso.refl Y) (Iso.refl Z)
    (by simp [S, T, mvNegIso]) (by simp [S, T])
  exact ShortComplex.exact_of_iso e h

private lemma mvExactNegG {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : f ≫ g = 0) (h : (ShortComplex.mk f g hfg).Exact) :
    (ShortComplex.mk f (-g) (by simp [hfg])).Exact := by
  let S := ShortComplex.mk f g hfg
  let T := ShortComplex.mk f (-g) (by simp [hfg])
  let e : S ≅ T := ShortComplex.isoMk (Iso.refl X) (Iso.refl Y) (mvNegIso Z)
    (by simp [S, T]) (by simp [S, T, mvNegIso])
  exact ShortComplex.exact_of_iso e h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def mayerVietorisExactBraid
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive]
    (k : ℤ) (U : OrderedTwoSetCover.{w}) : CategoryTheory.ExactBraid C := by
  let src := rightInterPairFunctor.obj U
  let tgt := spaceLeftPairFunctor.obj U
  let h := excisionNatTrans.app U
  let eK := (E.Hₚ k).map h
  let eD := (E.Hₚ (k - 1)).map h
  letI : IsIso eK :=
    HomologyTheoryData.IsExcisive.isIso_map_excision
      k U.X U.left U.right U.interior_cover
  letI : IsIso eD :=
    HomologyTheoryData.IsExcisive.isIso_map_excision
      (k - 1) U.X U.left U.right U.interior_cover
  refine
    { A := (E.Hₚ k).obj tgt
      X := (E.H (k - 1)).obj tgt.snd
      P := (E.H (k - 1)).obj src.snd
      Q := (E.H (k - 1)).obj tgt.snd ⊞ (E.H (k - 1)).obj src.fst
      R := (E.H (k - 1)).obj tgt.fst
      B₁ := (E.H (k - 1)).obj src.fst
      A₁ := (E.Hₚ (k - 1)).obj src
      X₁ := (E.H ((k - 1) - 1)).obj tgt.snd
      P₁ := (E.H ((k - 1) - 1)).obj src.snd
      Q₁ := (E.H ((k - 1) - 1)).obj tgt.snd ⊞
        (E.H ((k - 1) - 1)).obj src.fst
      B₂ := (E.H ((k - 1) - 1)).obj src.fst
      ax := E.boundary k tgt
      aP := inv eK ≫ E.boundary k src
      pB := -(E.subspaceMap (k - 1) src)
      bA := E.toRelative (k - 1) src
      aP₁ := E.boundary (k - 1) src
      pB₂ := -(E.subspaceMap ((k - 1) - 1) src)
      xQ := biprod.inl
      qB := biprod.snd
      bX := 0
      xQ₁ := biprod.inl
      qB₂ := biprod.snd
      xR := E.subspaceMap (k - 1) tgt
      rA := E.toRelative (k - 1) tgt ≫ inv eD
      aX := E.boundary (k - 1) src ≫
        (E.H ((k - 1) - 1)).map (TopPair.Hom.snd h)
      pQ := biprod.lift ((E.H (k - 1)).map (TopPair.Hom.snd h))
        (-(E.subspaceMap (k - 1) src))
      qR := biprod.desc (E.subspaceMap (k - 1) tgt)
        ((E.H (k - 1)).map (TopPair.Hom.fst h))
      pQ₁ := biprod.lift ((E.H ((k - 1) - 1)).map (TopPair.Hom.snd h))
        (-(E.subspaceMap ((k - 1) - 1) src))
      z_pB_bA := by
        rw [Preadditive.neg_comp,
          IsExact.subspaceMap_comp_toRelative E (k - 1) src, neg_zero]
      z_xQ_qB := by simp
      z_ax_xR := IsExact.boundary_comp_subspaceMap E k tgt
      z_bA_aP₁ := IsExact.toRelative_comp_boundary E (k - 1) src
      z_qB_bX := by simp
      z_xR_rA := by
        calc
          E.subspaceMap (k - 1) tgt ≫
                (E.toRelative (k - 1) tgt ≫ inv eD) =
              (E.subspaceMap (k - 1) tgt ≫
                E.toRelative (k - 1) tgt) ≫ inv eD := by
                  rw [Category.assoc]
          _ = 0 := by
            rw [IsExact.subspaceMap_comp_toRelative E (k - 1) tgt,
              zero_comp]
      z_rA_aX := by
        have hn := (E.δ (k - 1) ((k - 1) - 1)).naturality h
        change eD ≫ E.boundary (k - 1) tgt =
          E.boundary (k - 1) src ≫
            (E.H ((k - 1) - 1)).map (TopPair.Hom.snd h) at hn
        calc
          (E.toRelative (k - 1) tgt ≫ inv eD) ≫
                (E.boundary (k - 1) src ≫
                  (E.H ((k - 1) - 1)).map (TopPair.Hom.snd h)) =
              E.toRelative (k - 1) tgt ≫
                (inv eD ≫ (eD ≫ E.boundary (k - 1) tgt)) := by
                  rw [← hn]
                  simp only [Category.assoc]
          _ = 0 := by
            rw [IsIso.inv_hom_id_assoc,
              IsExact.toRelative_comp_boundary E (k - 1) tgt]
      z_aP₁_pB₂ := by
        rw [Preadditive.comp_neg,
          IsExact.boundary_comp_subspaceMap E (k - 1) src, neg_zero]
      z_bX_xQ₁ := by simp
      hABB := by
        apply mvExactNegF (E.subspaceMap (k - 1) src)
          (E.toRelative (k - 1) src)
          (IsExact.subspaceMap_comp_toRelative E (k - 1) src)
        exact IsExact.exact_subspaceMap_toRelative E (k - 1) src
      hXBQ := (ShortComplex.Splitting.ofHasBinaryBiproduct
        ((E.H (k - 1)).obj tgt.snd) ((E.H (k - 1)).obj src.fst)).exact
      hXA₀ := IsExact.exact_boundary_subspaceMap E k tgt
      hABA := IsExact.exact_toRelative_boundary E (k - 1) src
      hXBB := by
        apply (ShortComplex.exact_iff_epi _ rfl).2
        infer_instance
      hXAR := by
        let S := ShortComplex.mk (E.subspaceMap (k - 1) tgt)
          (E.toRelative (k - 1) tgt)
          (IsExact.subspaceMap_comp_toRelative E (k - 1) tgt)
        let T := ShortComplex.mk (E.subspaceMap (k - 1) tgt)
          (E.toRelative (k - 1) tgt ≫ inv eD)
          (by rw [← Category.assoc,
            IsExact.subspaceMap_comp_toRelative E (k - 1) tgt, zero_comp])
        let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
          (asIso eD).symm (by simp [S, T]) (by simp [S, T])
        exact ShortComplex.exact_of_iso e
          (IsExact.exact_subspaceMap_toRelative E (k - 1) tgt)
      hXAA := by
        have hn := (E.δ (k - 1) ((k - 1) - 1)).naturality h
        change eD ≫ E.boundary (k - 1) tgt =
          E.boundary (k - 1) src ≫
            (E.H ((k - 1) - 1)).map (TopPair.Hom.snd h) at hn
        let S := ShortComplex.mk (E.toRelative (k - 1) tgt)
          (E.boundary (k - 1) tgt)
          (IsExact.toRelative_comp_boundary E (k - 1) tgt)
        let T := ShortComplex.mk (E.toRelative (k - 1) tgt ≫ inv eD)
          (E.boundary (k - 1) src ≫
            (E.H ((k - 1) - 1)).map (TopPair.Hom.snd h))
          (by
            calc
              (E.toRelative (k - 1) tgt ≫ inv eD) ≫
                    (E.boundary (k - 1) src ≫
                      (E.H ((k - 1) - 1)).map (TopPair.Hom.snd h)) =
                  E.toRelative (k - 1) tgt ≫
                    (inv eD ≫ (eD ≫ E.boundary (k - 1) tgt)) := by
                      rw [← hn]
                      simp only [Category.assoc]
              _ = 0 := by
                rw [IsIso.inv_hom_id_assoc,
                  IsExact.toRelative_comp_boundary E (k - 1) tgt])
        let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) (asIso eD).symm
          (Iso.refl _) (by simp [S, T]) (by
            dsimp [S, T]
            simpa only [Category.assoc, IsIso.inv_hom_id_assoc,
              Category.comp_id] using
              congrArg (fun q => inv eD ≫ q) hn.symm)
        exact ShortComplex.exact_of_iso e
          (IsExact.exact_toRelative_boundary E (k - 1) tgt)
      hABP₁ := by
        apply mvExactNegG (E.boundary (k - 1) src)
          (E.subspaceMap ((k - 1) - 1) src)
          (IsExact.boundary_comp_subspaceMap E (k - 1) src)
        exact IsExact.exact_boundary_subspaceMap E (k - 1) src
      hXBX := by
        apply (ShortComplex.exact_iff_mono _ rfl).2
        infer_instance
      comm_aP := by
        have hn := (E.δ k (k - 1)).naturality h
        change eK ≫ E.boundary k tgt =
          E.boundary k src ≫ (E.H (k - 1)).map (TopPair.Hom.snd h) at hn
        apply biprod.hom_ext
        · simp only [Category.assoc, biprod.lift_fst, biprod.inl_fst,
            Category.comp_id]
          rw [← hn, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
        · simp only [Category.assoc, biprod.lift_snd, biprod.inl_snd,
            comp_zero, Preadditive.comp_neg]
          simp only [IsExact.boundary_comp_subspaceMap E k src,
            comp_zero, neg_zero]
      comm_pB := by simp only [biprod.lift_snd]
      comm_xR := by simp only [biprod.inl_desc]
      comm_rA := by
        have hn := (E.toRelativeNatTrans (k - 1)).naturality h
        change (E.H (k - 1)).map (TopPair.Hom.fst h) ≫
            E.toRelative (k - 1) tgt =
          E.toRelative (k - 1) src ≫ eD at hn
        apply biprod.hom_ext'
        · simp only [biprod.inl_desc_assoc, biprod.inl_snd_assoc, zero_comp]
          rw [← Category.assoc,
            IsExact.subspaceMap_comp_toRelative E (k - 1) tgt, zero_comp]
        · simp only [biprod.inr_desc_assoc, biprod.inr_snd_assoc]
          rw [← Category.assoc, hn, Category.assoc,
            IsIso.hom_inv_id, Category.comp_id]
      comm_bX := by
        rw [← Category.assoc,
          IsExact.toRelative_comp_boundary E (k - 1) src, zero_comp]
      comm_aP₁ := by
        apply biprod.hom_ext
        · simp only [Category.assoc, biprod.lift_fst, biprod.inl_fst,
            Category.comp_id]
        · simp only [Category.assoc, biprod.lift_snd, biprod.inl_snd,
            comp_zero, Preadditive.comp_neg]
          simp only [IsExact.boundary_comp_subspaceMap E (k - 1) src,
            neg_zero]
      comm_pB₂ := by simp only [biprod.lift_snd]
      zero_pq := by
        rw [biprod.lift_desc]
        have hn := (E.subspaceMapNatTrans (k - 1)).naturality h
        change (E.H (k - 1)).map (TopPair.Hom.snd h) ≫
            E.subspaceMap (k - 1) tgt =
          E.subspaceMap (k - 1) src ≫
            (E.H (k - 1)).map (TopPair.Hom.fst h) at hn
        rw [hn, Preadditive.neg_comp]
        exact add_neg_cancel _ }

private lemma mvExcision_snd (U : OrderedTwoSetCover.{w}) :
    TopPair.Hom.snd (excisionNatTrans.app U) = interToLeft.app U :=
  rfl

private lemma mvExcision_fst (U : OrderedTwoSetCover.{w}) :
    TopPair.Hom.fst (excisionNatTrans.app U) = rightToSpace.app U :=
  rfl

private lemma mvExcision_src_map (U : OrderedTwoSetCover.{w}) :
    (rightInterPairFunctor.obj U).map = interToRight.app U :=
  rfl

private lemma mvExcision_tgt_map (U : OrderedTwoSetCover.{w}) :
    (spaceLeftPairFunctor.obj U).map = leftToSpace.app U :=
  rfl

namespace IsExact

private theorem exact_mayerVietorisSequence_aux
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive]
    (k n : ℤ) (hn : k - 1 = n) (U : OrderedTwoSetCover.{w}) :
    (E.mayerVietorisSequence n U).Exact := by
  subst n
  let eN := (E.Hₚ (k - 1)).map (excisionNatTrans.app U)
  let _ : IsIso eN :=
    HomologyTheoryData.IsExcisive.isIso_map_excision
      (k - 1) U.X U.left U.right U.interior_cover
  have hb : (E.toRelative (k - 1) (spaceLeftPairFunctor.obj U) ≫ inv eN) ≫
          E.boundary (k - 1) (rightInterPairFunctor.obj U) =
      (E.mayerVietorisBoundaryNatTrans (k - 1)).app U :=
    by
      change (E.toRelative (k - 1) (spaceLeftPairFunctor.obj U) ≫ inv eN) ≫
          E.boundary (k - 1) (rightInterPairFunctor.obj U) =
        E.toRelative (k - 1) (spaceLeftPairFunctor.obj U) ≫
          inv eN ≫ E.boundary (k - 1) (rightInterPairFunctor.obj U)
      rw [Category.assoc]
  dsimp only [eN] at hb
  have h := (mayerVietorisExactBraid E k U).exact
  dsimp only [mayerVietorisExactBraid] at h
  change (ComposableArrows.mk₄
    ((E.mayerVietorisToPiecesNatTrans (k - 1)).app U)
    ((E.mayerVietorisToUnionNatTrans (k - 1)).app U)
    ((E.mayerVietorisBoundaryNatTrans (k - 1)).app U)
    ((E.mayerVietorisToPiecesNatTrans ((k - 1) - 1)).app U)).Exact
  have h' := h
  simp only [mvExcision_snd, mvExcision_fst,
    HomologyTheoryData.subspaceMap, mvExcision_src_map, mvExcision_tgt_map,
    hb] at h'
  exact h'

/-- Exactness of the abstract Mayer--Vietoris sequence. -/
theorem exact_mayerVietorisSequence
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive]
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    (E.mayerVietorisSequence n U).Exact :=
  exact_mayerVietorisSequence_aux E (n + 1) n (by omega) U

end IsExact

/-- The exact Mayer--Vietoris sequence for a fixed exact, excisive theory. -/
noncomputable def exactMayerVietorisSequenceFunctor
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive] (n : ℤ) :
    OrderedTwoSetCover.{w} ⥤ ComposableArrows.ExactSequences C 4 :=
  (ComposableArrows.exactSequences C 4).lift (E.mayerVietorisSequenceFunctor n)
    (fun U => IsExact.exact_mayerVietorisSequence E n U)

@[simp]
lemma exactMayerVietorisSequenceFunctor_obj_obj
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive]
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    ((exactMayerVietorisSequenceFunctor (C := C) E n).obj U).obj =
      E.mayerVietorisSequence n U :=
  rfl

@[simp]
lemma exactMayerVietorisSequenceFunctor_map_hom
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive]
    (n : ℤ) {U V : OrderedTwoSetCover.{w}} (f : U ⟶ V) :
    ((exactMayerVietorisSequenceFunctor (C := C) E n).map f).hom =
      (E.mayerVietorisSequenceFunctor n).map f :=
  rfl

/-- Exact Mayer--Vietoris sequences, functorial in exact excisive theories. -/
noncomputable def exactMayerVietorisSequenceBifunctor (n : ℤ) :
    (isExact (C := C) ⊓ isExcisive (C := C)).FullSubcategory ⥤
      (OrderedTwoSetCover.{w} ⥤ ComposableArrows.ExactSequences C 4) where
  obj E := by
    let _ : E.obj.IsExact := E.property.1
    let _ : E.obj.IsExcisive := E.property.2
    exact exactMayerVietorisSequenceFunctor E.obj n
  map {E F} f := by
    letI : E.obj.IsExact := E.property.1
    letI : E.obj.IsExcisive := E.property.2
    letI : F.obj.IsExact := F.property.1
    letI : F.obj.IsExcisive := F.property.2
    exact
      { app := fun U => ObjectProperty.homMk (mayerVietorisSequenceHom f.hom n U)
        naturality := fun U V g => by
          apply ObjectProperty.hom_ext
          exact (mayerVietorisSequenceNatTrans f.hom n).naturality g }
  map_id E := by
    let _ : E.obj.IsExact := E.property.1
    let _ : E.obj.IsExcisive := E.property.2
    apply NatTrans.ext
    funext U
    apply ObjectProperty.hom_ext
    let EE : (isExcisive (C := C)).FullSubcategory := ⟨E.obj, E.property.2⟩
    change ((mayerVietorisSequenceBifunctor (C := C) n).map (𝟙 EE)).app U = 𝟙 _
    exact congrArg (fun k => k.app U)
      ((mayerVietorisSequenceBifunctor (C := C) n).map_id EE)
  map_comp {E F G} f g := by
    let _ : E.obj.IsExact := E.property.1
    let _ : E.obj.IsExcisive := E.property.2
    let _ : F.obj.IsExact := F.property.1
    let _ : F.obj.IsExcisive := F.property.2
    let _ : G.obj.IsExact := G.property.1
    let _ : G.obj.IsExcisive := G.property.2
    apply NatTrans.ext
    funext U
    apply ObjectProperty.hom_ext
    let EE : (isExcisive (C := C)).FullSubcategory := ⟨E.obj, E.property.2⟩
    let FF : (isExcisive (C := C)).FullSubcategory := ⟨F.obj, F.property.2⟩
    let GG : (isExcisive (C := C)).FullSubcategory := ⟨G.obj, G.property.2⟩
    let ef : EE ⟶ FF := ⟨f.hom⟩
    let fg : FF ⟶ GG := ⟨g.hom⟩
    change ((mayerVietorisSequenceBifunctor (C := C) n).map (ef ≫ fg)).app U =
      ((mayerVietorisSequenceBifunctor (C := C) n).map ef).app U ≫
        ((mayerVietorisSequenceBifunctor (C := C) n).map fg).app U
    exact congrArg (fun k => k.app U)
      ((mayerVietorisSequenceBifunctor (C := C) n).map_comp ef fg)

@[simp]
lemma exactMayerVietorisSequenceBifunctor_obj_obj_obj
    (E : (isExact (C := C) ⊓ isExcisive (C := C)).FullSubcategory)
    (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    (((exactMayerVietorisSequenceBifunctor (C := C) n).obj E).obj U).obj =
      @mayerVietorisSequence _ _ _ _ E.obj E.property.2 n U :=
  rfl

@[simp]
lemma exactMayerVietorisSequenceBifunctor_map_app_hom
    {E F : (isExact (C := C) ⊓ isExcisive (C := C)).FullSubcategory}
    (f : E ⟶ F) (n : ℤ) (U : OrderedTwoSetCover.{w}) :
    (((exactMayerVietorisSequenceBifunctor (C := C) n).map f).app U).hom =
      @mayerVietorisSequenceHom _ _ _ _ E.obj F.obj
        E.property.2 F.property.2 f.hom n U :=
  rfl

end TopPair.HomologyTheoryData

namespace TopPair.OrdinaryHomologyTheory

open AlgebraicTopology AlgebraicTopology.OrderedTwoSetCover

universe w u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The Mayer--Vietoris connecting isomorphism when both members of the cover
are contractible and the degree below the connecting map is nonzero. -/
noncomputable def contractibleCoverMayerVietorisIso
    (E : OrdinaryHomologyTheory.{u, v, w} C)
    (U : OrderedTwoSetCover.{w}) (n : ℕ) (hn : n ≠ 0)
    [ContractibleSpace ↥U.left] [ContractibleSpace ↥U.right] :
    (E.H ((n + 1 : ℕ) : ℤ)).obj U.X ≅
      (E.H (((n + 1 : ℕ) : ℤ) - 1)).obj
        (TopCat.of (U.left ∩ U.right : Set U.X)) := by
  let seq := E.obj.mayerVietorisSequence ((n + 1 : ℕ) : ℤ) U
  have hPiecesSucc : IsZero
      ((E.obj.H ((n + 1 : ℕ) : ℤ)).obj (TopCat.of U.left) ⊞
        (E.obj.H ((n + 1 : ℕ) : ℤ)).obj (TopCat.of U.right)) :=
    (biprod_isZero_iff _ _).mpr ⟨
      E.isZero_of_contractible ((n + 1 : ℕ) : ℤ) (by omega) ↥U.left,
      E.isZero_of_contractible ((n + 1 : ℕ) : ℤ) (by omega) ↥U.right⟩
  have hPieces : IsZero
      ((E.obj.H (((n + 1 : ℕ) : ℤ) - 1)).obj (TopCat.of U.left) ⊞
        (E.obj.H (((n + 1 : ℕ) : ℤ) - 1)).obj (TopCat.of U.right)) :=
    (biprod_isZero_iff _ _).mpr ⟨
      E.isZero_of_contractible (((n + 1 : ℕ) : ℤ) - 1)
        (by simpa using (show (n : ℤ) ≠ 0 by exact_mod_cast hn)) ↥U.left,
      E.isZero_of_contractible (((n + 1 : ℕ) : ℤ) - 1)
        (by simpa using (show (n : ℤ) ≠ 0 by exact_mod_cast hn)) ↥U.right⟩
  have hExact : seq.Exact :=
    HomologyTheoryData.IsExact.exact_mayerVietorisSequence
      E.obj ((n + 1 : ℕ) : ℤ) U
  have hToUnionZero : seq.map' 1 2 = 0 := by
    change (E.obj.mayerVietorisToUnionNatTrans (C := C)
      ((n + 1 : ℕ) : ℤ)).app U = 0
    exact hPiecesSucc.eq_of_src _ _
  have hToPiecesZero : seq.map' 3 4 = 0 := by
    change (E.obj.mayerVietorisToPiecesNatTrans (C := C)
      (((n + 1 : ℕ) : ℤ) - 1)).app U = 0
    exact hPieces.eq_of_tgt _ _
  exact @asIso C _ _ _ _
    (hExact.isIso_map' 1 (by omega) hToUnionZero hToPiecesZero)

end TopPair.OrdinaryHomologyTheory

namespace TopPair.OrdinaryHomologyTheory

open AlgebraicTopology AlgebraicTopology.OrderedTwoSetCover

universe w u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The contractible-cover Mayer--Vietoris connecting isomorphism, natural in
ordinary homology theories. -/
noncomputable def contractibleCoverMayerVietorisNatIso
    (U : OrderedTwoSetCover.{w}) (n : ℕ) (hn : n ≠ 0)
    [ContractibleSpace ↥U.left] [ContractibleSpace ↥U.right] :
    hFunctor (C := C) ((n + 1 : ℕ) : ℤ) ⋙
        (evaluation TopCat.{w} C).obj U.X ≅
      hFunctor (C := C) (((n + 1 : ℕ) : ℤ) - 1) ⋙
        (evaluation TopCat.{w} C).obj
          (TopCat.of (U.left ∩ U.right : Set U.X)) :=
  NatIso.ofComponents
    (fun E => contractibleCoverMayerVietorisIso E U n hn)
    (fun {E F} f => by
      set_option backward.isDefEq.respectTransparency false in
        have hE :
            (contractibleCoverMayerVietorisIso E U n hn).hom =
              (E.obj.mayerVietorisBoundaryNatTrans
                ((n + 1 : ℕ) : ℤ)).app U := rfl
        have hF :
            (contractibleCoverMayerVietorisIso F U n hn).hom =
              (F.obj.mayerVietorisBoundaryNatTrans
                ((n + 1 : ℕ) : ℤ)).app U := rfl
        rw [hE, hF]
        exact
          (HomologyTheoryData.mayerVietorisBoundary_naturality_theory
            (E := E.obj) (F := F.obj) f.hom
            ((n + 1 : ℕ) : ℤ) U).symm)

@[simp]
theorem contractibleCoverMayerVietorisNatIso_app
    (U : OrderedTwoSetCover.{w}) (n : ℕ) (hn : n ≠ 0)
    [ContractibleSpace ↥U.left] [ContractibleSpace ↥U.right]
    (E : OrdinaryHomologyTheory.{u, v, w} C) :
    (contractibleCoverMayerVietorisNatIso (C := C) U n hn).app E =
      contractibleCoverMayerVietorisIso E U n hn :=
  rfl

end TopPair.OrdinaryHomologyTheory
