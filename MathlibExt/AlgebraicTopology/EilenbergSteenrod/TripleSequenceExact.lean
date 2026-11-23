/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceExact
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.TripleSequence
public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.Braid

/-!
# Exact triple sequences

Abstract exactness for the five-term triple sequence as an
Eilenberg–Steenrod consequence for an arbitrary abelian target
category. The proof assembles an `ExactBraid` from the three exact
pair sequences and applies the braid exactness theorem.

This file is an abstract consequence; it does not import singular
homology, modules, or abelian groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe w u v

namespace TopPair.HomologyTheoryData

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Functoriality of the absolute homology on the composite `B ⟶ A ⟶ X`. -/
private lemma comp_subspaceMaps (E : HomologyTheoryData.{w} C) (n : ℤ)
    (T : TopTriple.{w}) :
    (E.H (n - 1)).map (T.obj.map' 0 1) ≫ (E.H (n - 1)).map (T.obj.map' 1 2) =
      (E.H (n - 1)).map (T.obj.map' 0 2) := by
  rw [← (E.H (n - 1)).map_comp]
  congr 1
  exact (T.obj.map'_comp 0 1 2).symm

/-- The first two visible triple maps compose to zero through the
diagonal pair `(A, A)` whose relative homology vanishes. -/
private lemma triple_pQ_qR_zero (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (T : TopTriple.{w}) :
    (E.Hₚ n).map (topTriplePair01To02.app T) ≫
        (E.Hₚ n).map (topTriplePair02To12.app T) = 0 := by
  have h_eq :
      topTriplePair01To02.app T ≫ topTriplePair02To12.app T =
        topTriplePair01ToMiddleDiag.app T ≫ topTripleMiddleDiagToPair12.app T := by
    have h :=
      congrArg (fun f : topTriplePair01.{w} ⟶ topTriplePair12.{w} => f.app T)
        AlgebraicTopology.topTriplePair01To02_comp_topTriplePair02To12
    simpa using h
  calc (E.Hₚ n).map (topTriplePair01To02.app T) ≫
          (E.Hₚ n).map (topTriplePair02To12.app T)
      = (E.Hₚ n).map (topTriplePair01To02.app T ≫ topTriplePair02To12.app T) := by
        rw [← (E.Hₚ n).map_comp]
    _ = (E.Hₚ n).map
          (topTriplePair01ToMiddleDiag.app T ≫ topTripleMiddleDiagToPair12.app T) := by
        rw [h_eq]
    _ = (E.Hₚ n).map (topTriplePair01ToMiddleDiag.app T) ≫
          (E.Hₚ n).map (topTripleMiddleDiagToPair12.app T) := by
        rw [(E.Hₚ n).map_comp]
    _ = 0 := by
        have hZero : IsZero ((E.Hₚ n).obj (topTripleMiddleDiag.obj T)) :=
          IsExact.isZero_relative_diag (E := E) n ((topTriplePair01.obj T).fst)
        have hmap : (E.Hₚ n).map (topTripleMiddleDiagToPair12.app T) = 0 :=
          IsZero.eq_of_src hZero _ 0
        simp [hmap]

set_option backward.isDefEq.respectTransparency false in
/-- The exact braid assembled from the three exact pair sequences of a triple. -/
noncomputable def tripleExactBraid (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (T : TopTriple.{w}) : CategoryTheory.ExactBraid C where
  A := (E.H n).obj ((topTriplePair01.obj T).fst)
  X := (E.H n).obj ((topTriplePair12.obj T).fst)
  P := (E.Hₚ n).obj (topTriplePair01.obj T)
  Q := (E.Hₚ n).obj (topTriplePair02.obj T)
  R := (E.Hₚ n).obj (topTriplePair12.obj T)
  B₁ := (E.H (n - 1)).obj ((topTriplePair01.obj T).snd)
  A₁ := (E.H (n - 1)).obj ((topTriplePair01.obj T).fst)
  X₁ := (E.H (n - 1)).obj ((topTriplePair12.obj T).fst)
  P₁ := (E.Hₚ (n - 1)).obj (topTriplePair01.obj T)
  Q₁ := (E.Hₚ (n - 1)).obj (topTriplePair02.obj T)
  B₂ := (E.H ((n - 1) - 1)).obj ((topTriplePair01.obj T).snd)
  ax := (E.H n).map (T.obj.map' 1 2)
  aP := E.toRelative n (topTriplePair01.obj T)
  pB := E.boundary n (topTriplePair01.obj T)
  bA := (E.H (n - 1)).map (T.obj.map' 0 1)
  aP₁ := E.toRelative (n - 1) (topTriplePair01.obj T)
  pB₂ := E.boundary (n - 1) (topTriplePair01.obj T)
  xQ := E.toRelative n (topTriplePair02.obj T)
  qB := E.boundary n (topTriplePair02.obj T)
  bX := (E.H (n - 1)).map (T.obj.map' 0 2)
  xQ₁ := E.toRelative (n - 1) (topTriplePair02.obj T)
  qB₂ := E.boundary (n - 1) (topTriplePair02.obj T)
  xR := E.toRelative n (topTriplePair12.obj T)
  rA := E.boundary n (topTriplePair12.obj T)
  aX := (E.H (n - 1)).map (T.obj.map' 1 2)
  pQ := (E.Hₚ n).map (topTriplePair01To02.app T)
  qR := (E.Hₚ n).map (topTriplePair02To12.app T)
  pQ₁ := (E.Hₚ (n - 1)).map (topTriplePair01To02.app T)
  z_pB_bA := IsExact.boundary_comp_subspaceMap E n (topTriplePair01.obj T)
  z_xQ_qB := IsExact.toRelative_comp_boundary E n (topTriplePair02.obj T)
  z_ax_xR := IsExact.subspaceMap_comp_toRelative E n (topTriplePair12.obj T)
  z_bA_aP₁ := IsExact.subspaceMap_comp_toRelative E (n - 1) (topTriplePair01.obj T)
  z_qB_bX := IsExact.boundary_comp_subspaceMap E n (topTriplePair02.obj T)
  z_xR_rA := IsExact.toRelative_comp_boundary E n (topTriplePair12.obj T)
  z_rA_aX := IsExact.boundary_comp_subspaceMap E n (topTriplePair12.obj T)
  z_aP₁_pB₂ := IsExact.toRelative_comp_boundary E (n - 1) (topTriplePair01.obj T)
  z_bX_xQ₁ := IsExact.subspaceMap_comp_toRelative E (n - 1) (topTriplePair02.obj T)
  hABB := IsExact.exact_boundary_subspaceMap E n (topTriplePair01.obj T)
  hXBQ := IsExact.exact_toRelative_boundary E n (topTriplePair02.obj T)
  hXA₀ := IsExact.exact_subspaceMap_toRelative E n (topTriplePair12.obj T)
  hABA := IsExact.exact_subspaceMap_toRelative E (n - 1) (topTriplePair01.obj T)
  hXBB := IsExact.exact_boundary_subspaceMap E n (topTriplePair02.obj T)
  hXAR := IsExact.exact_toRelative_boundary E n (topTriplePair12.obj T)
  hXAA := IsExact.exact_boundary_subspaceMap E n (topTriplePair12.obj T)
  hABP₁ := IsExact.exact_toRelative_boundary E (n - 1) (topTriplePair01.obj T)
  hXBX := IsExact.exact_subspaceMap_toRelative E (n - 1) (topTriplePair02.obj T)
  comm_aP := ((E.toRelativeNatTrans n).naturality (topTriplePair01To02.app T)).symm
  comm_pB := by
    have h := (E.δ n (n - 1)).naturality (topTriplePair01To02.app T)
    have h_snd : (TopPair.proj₂ ⋙ E.H (n - 1)).map (topTriplePair01To02.app T) = 𝟙 _ := by
      calc (TopPair.proj₂ ⋙ E.H (n - 1)).map (topTriplePair01To02.app T)
          = (E.H (n - 1)).map (TopPair.Hom.snd (topTriplePair01To02.app T)) := rfl
        _ = (E.H (n - 1)).map (𝟙 _) := by rfl
        _ = 𝟙 _ := (E.H (n - 1)).map_id _
    rw [h_snd] at h
    simp only [Category.comp_id] at h
    exact h
  comm_xR := by
    have h := (E.toRelativeNatTrans n).naturality (topTriplePair02To12.app T)
    have h_fst : (TopPair.proj₁ ⋙ E.H n).map (topTriplePair02To12.app T) = 𝟙 _ := by
      calc (TopPair.proj₁ ⋙ E.H n).map (topTriplePair02To12.app T)
          = (E.H n).map (TopPair.Hom.fst (topTriplePair02To12.app T)) := rfl
        _ = (E.H n).map (𝟙 _) := by rfl
        _ = 𝟙 _ := (E.H n).map_id _
    rw [h_fst] at h
    simp only [Category.id_comp] at h
    exact h.symm
  comm_rA := by
    have h := (E.δ n (n - 1)).naturality (topTriplePair02To12.app T)
    have h_proj : (TopPair.proj₂ ⋙ E.H (n - 1)).map (topTriplePair02To12.app T) =
        (E.H (n - 1)).map (T.obj.map' 0 1) := by
      calc (TopPair.proj₂ ⋙ E.H (n - 1)).map (topTriplePair02To12.app T)
          = (E.H (n - 1)).map (TopPair.Hom.snd (topTriplePair02To12.app T)) := rfl
        _ = (E.H (n - 1)).map (T.obj.map' 0 1) := by rfl
    rw [h_proj] at h
    exact h
  comm_bX := by exact comp_subspaceMaps E n T
  comm_aP₁ := ((E.toRelativeNatTrans (n - 1)).naturality (topTriplePair01To02.app T)).symm
  comm_pB₂ := by
    have h := (E.δ (n - 1) ((n - 1) - 1)).naturality (topTriplePair01To02.app T)
    have h_snd : (TopPair.proj₂ ⋙ E.H ((n - 1) - 1)).map (topTriplePair01To02.app T) = 𝟙 _ := by
      calc (TopPair.proj₂ ⋙ E.H ((n - 1) - 1)).map (topTriplePair01To02.app T)
          = (E.H ((n - 1) - 1)).map (TopPair.Hom.snd (topTriplePair01To02.app T)) := rfl
        _ = (E.H ((n - 1) - 1)).map (𝟙 _) := by rfl
        _ = 𝟙 _ := (E.H ((n - 1) - 1)).map_id _
    rw [h_snd] at h
    simp only [Category.comp_id] at h
    exact h
  zero_pq := by exact triple_pQ_qR_zero E n T

end TopPair.HomologyTheoryData

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exactness of the five-term triple sequence. -/
theorem exact_tripleSequence (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (T : TopTriple.{w}) : (E.tripleSequence n T).Exact :=
  (TopPair.HomologyTheoryData.tripleExactBraid (E := E) n T).exact

/-- The triple boundary is an isomorphism when the adjacent relative groups
of the outer pair vanish. -/
theorem isIso_tripleBoundary_of_isZero_pair02
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (T : TopTriple.{w})
    (hZeroN : IsZero ((E.Hₚ n).obj (topTriplePair02.obj T)))
    (hZeroPrev : IsZero ((E.Hₚ (n - 1)).obj (topTriplePair02.obj T))) :
    IsIso ((E.tripleBoundaryNatTrans n).app T) := by
  let S := E.tripleSequence n T
  have hExact := exact_tripleSequence E n T
  have hPrev : S.map' 1 2 = 0 := by
    exact hZeroN.eq_of_src _ _
  have hNext : S.map' 3 4 = 0 := by
    exact hZeroPrev.eq_of_tgt _ _
  let _ : Mono ((E.tripleBoundaryNatTrans n).app T) := by
    change Mono (S.map' 2 3)
    exact (hExact.exact 1).mono_g_iff.mpr hPrev
  let _ : Epi ((E.tripleBoundaryNatTrans n).app T) := by
    change Epi (S.map' 2 3)
    exact (hExact.exact 2).epi_f_iff.mpr hNext
  exact isIso_of_mono_of_epi _

/-- The triple boundary is a natural isomorphism on a functorial family of
triples whose adjacent outer-pair groups vanish. -/
noncomputable def tripleBoundaryNatIsoOfIsZeroPair02
    {D : Type*} [Category D]
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (T : D ⥤ TopTriple.{w})
    (hZeroN : ∀ X, IsZero ((E.Hₚ n).obj (topTriplePair02.obj (T.obj X))))
    (hZeroPrev : ∀ X, IsZero ((E.Hₚ (n - 1)).obj (topTriplePair02.obj (T.obj X)))) :
    T ⋙ topTriplePair12 ⋙ E.Hₚ n ≅
      T ⋙ topTriplePair01 ⋙ E.Hₚ (n - 1) := by
  let α := Functor.whiskerLeft T (E.tripleBoundaryNatTrans n)
  let _ (X : D) : IsIso (α.app X) :=
    isIso_tripleBoundary_of_isZero_pair02 E n (T.obj X)
      (hZeroN X) (hZeroPrev X)
  let _ : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

end TopPair.HomologyTheoryData.IsExact

namespace TopPair.HomologyTheoryData

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- The triple sequence valued in exact diagrams. -/
noncomputable def exactTripleSequenceFunctor (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) : TopTriple.{w} ⥤ ComposableArrows.ExactSequences C 4 :=
  (ComposableArrows.exactSequences C 4).lift (E.tripleSequenceFunctor n)
    (fun T => IsExact.exact_tripleSequence (E := E) n T)

@[simp]
lemma exactTripleSequenceFunctor_obj_obj (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (T : TopTriple.{w}) :
    ((exactTripleSequenceFunctor (C := C) E n).obj T).obj = E.tripleSequence n T :=
  rfl

@[simp]
lemma exactTripleSequenceFunctor_map_hom (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) {T U : TopTriple.{w}} (f : T ⟶ U) :
    ((exactTripleSequenceFunctor (C := C) E n).map f).hom =
      (E.tripleSequenceFunctor n).map f :=
  rfl

/-- The exact triple sequence bifunctor, covariant in exact theories and triples. -/
noncomputable def exactTripleSequenceBifunctor (n : ℤ) :
    (isExact (C := C)).FullSubcategory ⥤
      (TopTriple.{w} ⥤ ComposableArrows.ExactSequences C 4) where
  obj E := @exactTripleSequenceFunctor _ _ _ E.obj E.property n
  map {E F} f :=
    { app := fun T =>
        ObjectProperty.homMk (((tripleSequenceBifunctor (C := C) n).map f.hom).app T)
      naturality := fun T U g => by
        apply ObjectProperty.hom_ext
        exact ((tripleSequenceBifunctor (C := C) n).map f.hom).naturality g }
  map_id E := by
    apply NatTrans.ext
    funext T
    apply ObjectProperty.hom_ext
    change ((tripleSequenceBifunctor (C := C) n).map (𝟙 E.obj)).app T = 𝟙 _
    exact congrArg (fun k => k.app T) ((tripleSequenceBifunctor (C := C) n).map_id E.obj)
  map_comp {E F G} f g := by
    apply NatTrans.ext
    funext T
    apply ObjectProperty.hom_ext
    change ((tripleSequenceBifunctor (C := C) n).map (f.hom ≫ g.hom)).app T =
        ((tripleSequenceBifunctor (C := C) n).map f.hom).app T ≫
          ((tripleSequenceBifunctor (C := C) n).map g.hom).app T
    exact congrArg (fun k => k.app T) ((tripleSequenceBifunctor (C := C) n).map_comp f.hom g.hom)

@[simp]
lemma exactTripleSequenceBifunctor_obj_obj_obj
    (E : (isExact (C := C)).FullSubcategory) (n : ℤ) (T : TopTriple.{w}) :
    (((exactTripleSequenceBifunctor (C := C) n).obj E).obj T).obj =
      E.obj.tripleSequence n T :=
  rfl

@[simp]
lemma exactTripleSequenceBifunctor_map_app_hom
    {E F : (isExact (C := C)).FullSubcategory} (f : E ⟶ F)
    (n : ℤ) (T : TopTriple.{w}) :
    (((exactTripleSequenceBifunctor (C := C) n).map f).app T).hom =
      tripleSequenceHom f.hom n T :=
  rfl

end TopPair.HomologyTheoryData
