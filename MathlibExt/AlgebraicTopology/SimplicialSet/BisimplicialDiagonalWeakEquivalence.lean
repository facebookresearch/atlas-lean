/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMap
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyProduct
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexDirectedSup

/-!
# Rowwise realization equivalences induce a diagonal equivalence

For a map of bisimplicial sets in any universe, componentwise realization weak
equivalences in the outer simplicial direction induce a realization weak
equivalence on the diagonal.  The finite-stage proof uses the cofibrant cube
lemma on the genuine skeletal attachment squares; in particular it never
assumes that `diagonalAttachmentTopMap` is a monomorphism.  The final passage
to the full diagonal uses only the sequential-mono colimit theorem.

This file installs no global TopCat model structure, left-properness instance,
or arbitrary filtered-colimit stability, and makes no additivity, Theorem A,
or realization-equivalence claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MorphismProperty MonoidalCategory Opposite
open HomotopicalAlgebra

open scoped Simplicial

universe u

namespace SSet

/-- Taking product on the right with a finite simplicial set preserves
realization weak equivalences. -/
theorem realizationWeakEquivalences.prodMap_id_of_finite_right
    {A B K : SSet.{u}} (f : A ⟶ B)
    (hf : realizationWeakEquivalences f) [K.Finite] :
    realizationWeakEquivalences (Limits.prod.map f (𝟙 K)) := by
  let _ : IsIso (Limits.prodComparison SSet.toTop K A) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary K A
  let _ : IsIso (Limits.prodComparison SSet.toTop A K) :=
    SSet.isIso_prodComparison_swap K A
  let _ : IsIso (Limits.prodComparison SSet.toTop K B) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary K B
  let _ : IsIso (Limits.prodComparison SSet.toTop B K) :=
    SSet.isIso_prodComparison_swap K B
  let eA := asIso (Limits.prodComparison SSet.toTop A K)
  let eB := asIso (Limits.prodComparison SSet.toTop B K)
  have hfTop : TopCat.weakHomotopyEquivalences (SSet.toTop.map f) := by
    exact hf
  have hProd : TopCat.weakHomotopyEquivalences
      (Limits.prod.map (SSet.toTop.map f) (𝟙 (SSet.toTop.obj K))) :=
    TopCat.weakHomotopyEquivalences.prodMap hfTop
      (TopCat.weakHomotopyEquivalences.id_mem _)
  have hNat := Limits.prodComparison_natural (F := SSet.toTop) f (𝟙 K)
  have hEq : SSet.toTop.map (Limits.prod.map f (𝟙 K)) =
      eA.hom ≫ Limits.prod.map (SSet.toTop.map f) (𝟙 (SSet.toTop.obj K)) ≫
        eB.inv := by
    calc
      SSet.toTop.map (Limits.prod.map f (𝟙 K)) =
          SSet.toTop.map (Limits.prod.map f (𝟙 K)) ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      _ = SSet.toTop.map (Limits.prod.map f (𝟙 K)) ≫
          (eB.hom ≫ eB.inv) := by rw [eB.hom_inv_id]
      _ = (SSet.toTop.map (Limits.prod.map f (𝟙 K)) ≫ eB.hom) ≫
          eB.inv := (Category.assoc _ _ _).symm
      _ = (eA.hom ≫ Limits.prod.map (SSet.toTop.map f)
          (SSet.toTop.map (𝟙 K))) ≫ eB.inv := by
        exact congrArg (fun z => z ≫ eB.inv) hNat
      _ = eA.hom ≫ Limits.prod.map (SSet.toTop.map f)
          (𝟙 (SSet.toTop.obj K)) ≫ eB.inv := by simp
  have hPost := RespectsIso.postcomp TopCat.weakHomotopyEquivalences
    eB.inv _ hProd
  have hPre := RespectsIso.precomp TopCat.weakHomotopyEquivalences
    eA.hom _ hPost
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (Limits.prod.map f (𝟙 K)))
  rw [hEq]
  exact hPre

/-- Transport realization weak equivalences across an isomorphism square. -/
private theorem realizationWeakEquivalence_of_iso_square
    {A B A' B' : SSet.{u}} (eA : A ≅ A') (eB : B ≅ B')
    (f : A ⟶ B) (f' : A' ⟶ B')
    (h : eA.hom ≫ f' = f ≫ eB.hom)
    (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences f' := by
  have hPost := RespectsIso.postcomp realizationWeakEquivalences eB.hom f hf
  rw [← h] at hPost
  exact (realizationWeakEquivalences.cancel_left_of_respectsIso eA.hom f').mp hPost

/-- Transport a realization weak equivalence backwards across an isomorphism
square. -/
private theorem realizationWeakEquivalence_of_iso_square_rev
    {A B A' B' : SSet.{u}} (eA : A ≅ A') (eB : B ≅ B')
    (f : A ⟶ B) (f' : A' ⟶ B')
    (h : eA.hom ≫ f' = f ≫ eB.hom)
    (hf' : realizationWeakEquivalences f') :
    realizationWeakEquivalences f := by
  have hPre := RespectsIso.precomp realizationWeakEquivalences
    eA.hom f' hf'
  rw [h] at hPre
  exact (realizationWeakEquivalences.cancel_right_of_respectsIso
    f eB.hom).mp hPre

/-- Realized simplicial objects are cofibrant in the proof-local TopCat model
used by the cube argument. -/
private theorem realizationWeakEquivalence_map_of_isPushouts
    {A B X P A' B' X' P' : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    {i' : A' ⟶ B'} {g' : A' ⟶ X'}
    {p' : B' ⟶ P'} {q' : X' ⟶ P'}
    (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
    {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
    [Mono i] [Mono i']
    (ha : realizationWeakEquivalences a)
    (hb : realizationWeakEquivalences b)
    (hc : realizationWeakEquivalences c) :
    realizationWeakEquivalences d := by
  let : ModelCategory TopCat.{u} := TopCat.modelCategory
  have sqTop := SSet.toTop.map_isPushout sq
  have sqTop' := SSet.toTop.map_isPushout sq'
  let : Cofibration (SSet.toTop.map i) := by
    rw [cofibration_iff]
    exact SSet.toTop_map_mem_realizedBoundaryLLP i
  let : Cofibration (SSet.toTop.map i') := by
    rw [cofibration_iff]
    exact SSet.toTop_map_mem_realizedBoundaryLLP i'
  let : WeakEquivalence (SSet.toTop.map a) := by
    rw [weakEquivalence_iff]
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map a)
    exact ha
  let : WeakEquivalence (SSet.toTop.map b) := by
    rw [weakEquivalence_iff]
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map b)
    exact hb
  let : WeakEquivalence (SSet.toTop.map c) := by
    rw [weakEquivalence_iff]
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map c)
    exact hc
  have hCofibrant (Z : SSet.{u}) : IsCofibrant (SSet.toTop.obj Z) := by
    let : Cofibration (SSet.toTop.map (initial.to Z)) := by
      rw [cofibration_iff]
      exact SSet.toTop_map_mem_realizedBoundaryLLP (initial.to Z)
    have hInit : IsInitial (SSet.toTop.obj (⊥_ SSet.{u})) :=
      initialIsInitial.isInitialObj (G := SSet.toTop.{u})
    exact (isCofibrant_iff_of_isInitial
      (SSet.toTop.map (initial.to Z)) hInit).2 (by infer_instance)
  let : IsCofibrant (SSet.toTop.obj A) := hCofibrant A
  let : IsCofibrant (SSet.toTop.obj A') := hCofibrant A'
  let : IsCofibrant (SSet.toTop.obj X) := hCofibrant X
  let : IsCofibrant (SSet.toTop.obj X') := hCofibrant X'
  have hiTop : SSet.toTop.map i ≫ SSet.toTop.map b =
      SSet.toTop.map a ≫ SSet.toTop.map i' := by
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, hi]
  have hgTop : SSet.toTop.map g ≫ SSet.toTop.map c =
      SSet.toTop.map a ≫ SSet.toTop.map g' := by
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, hg]
  have hpTop : SSet.toTop.map p ≫ SSet.toTop.map d =
      SSet.toTop.map b ≫ SSet.toTop.map p' := by
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, hp]
  have hqTop : SSet.toTop.map q ≫ SSet.toTop.map d =
      SSet.toTop.map c ≫ SSet.toTop.map q' := by
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, hq]
  have hdTop : WeakEquivalence (SSet.toTop.map d) :=
    weakEquivalence_map_of_isPushouts_of_cofibrant
      sqTop sqTop' hiTop hgTop hpTop hqTop
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map d)
  exact (weakEquivalence_iff (f := SSet.toTop.map d)).mp hdTop

/-! ## Finite latching stages -/

/-- Immediately before a successor degeneracy, the partial latching object is
the preceding finite stage. -/
private theorem outerLatchingStageBefore_succ_eq_stage
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageBefore X (n + 1) r.succ =
      outerLatchingStage X (n + 1) r.castSucc := by
  apply le_antisymm
  · unfold outerLatchingStageBefore outerLatchingStage
    rw [iSup_le_iff]
    intro i
    rw [iSup_le_iff]
    intro hi
    have hir : i ≤ r.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      exact Nat.le_of_lt_succ (Fin.lt_def.mp hi)
    exact le_iSup_of_le i (le_iSup_of_le hir (by rfl))
  · unfold outerLatchingStageBefore outerLatchingStage
    rw [iSup_le_iff]
    intro i
    rw [iSup_le_iff]
    intro hi
    have hir : i < r.succ := by
      apply Fin.lt_def.mpr
      exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hi)
    exact le_iSup_of_le i (le_iSup_of_le hir (by rfl))

/-- The canonical source-overlap identification commutes with maps of
bisimplicial sets. -/
private theorem outerLatchingStageSourceOverlap_succ_naturality
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    (Subcomplex.eqToIso
        (outerLatchingStageSourceOverlap_succ X n r)).hom ≫
        outerLatchingStageMap eta n r =
      outerLatchingStageSourceOverlapMap eta (n + 1) r.succ ≫
        (Subcomplex.eqToIso
          (outerLatchingStageSourceOverlap_succ Y n r)).hom := by
  apply (cancel_mono (outerLatchingStage Y n r).ι).mp
  simp

/-- The canonical stage-before identification commutes with maps of
bisimplicial sets. -/
private theorem outerLatchingStageBefore_succ_naturality
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    (Subcomplex.eqToIso
        (outerLatchingStageBefore_succ_eq_stage X n r)).hom ≫
        outerLatchingStageMap eta (n + 1) r.castSucc =
      outerLatchingStageBeforeMap eta (n + 1) r.succ ≫
        (Subcomplex.eqToIso
          (outerLatchingStageBefore_succ_eq_stage Y n r)).hom := by
  apply (cancel_mono (outerLatchingStage Y (n + 1) r.castSucc).ι).mp
  simp

/-- The first-stage isomorphism is natural in the bisimplicial set. -/
private theorem outerLatchingStage_zero_iso_naturality
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    (outerLatchingStage_zero_iso X n).hom ≫
        outerLatchingStageMap eta n 0 =
      eta.app (Opposite.op (SimplexCategory.mk n)) ≫
        (outerLatchingStage_zero_iso Y n).hom := by
  apply (cancel_mono (outerLatchingStage Y n 0).ι).mp
  simp only [Category.assoc, outerLatchingStageMap_ι,
    outerLatchingStage_zero_iso_hom_ι,
    outerLatchingStage_zero_iso_hom_ι_assoc]
  exact SimplicialObject.σ_naturality eta 0

/-- The last-stage identification with the full outer latching object is
natural in the bisimplicial set. -/
private theorem outerLatchingStage_last_naturality
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    (Subcomplex.eqToIso (outerLatchingStage_last X n)).hom ≫
        outerLatchingMap eta (n + 1) =
      outerLatchingStageMap eta n (Fin.last n) ≫
        (Subcomplex.eqToIso (outerLatchingStage_last Y n)).hom := by
  apply (cancel_mono (outerLatching Y (n + 1)).ι).mp
  simp

/-- Every finite outer-latching stage map is a realization weak equivalence
when all outer row maps are. -/
private theorem outerLatchingStageMap_mem_realizationWeakEquivalences
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hEta : ∀ n,
      realizationWeakEquivalences
        (eta.app (Opposite.op (SimplexCategory.mk n)))) :
    ∀ (n : ℕ) (r : Fin (n + 1)),
      realizationWeakEquivalences (outerLatchingStageMap eta n r) := by
  intro n
  induction n with
  | zero =>
      intro r
      have hr : r = 0 := Fin.eq_zero r
      subst r
      exact realizationWeakEquivalence_of_iso_square
        (outerLatchingStage_zero_iso X 0)
        (outerLatchingStage_zero_iso Y 0)
        (eta.app (Opposite.op (SimplexCategory.mk 0)))
        (outerLatchingStageMap eta 0 0)
        (outerLatchingStage_zero_iso_naturality eta 0) (hEta 0)
  | succ n ih =>
      intro r
      induction r using Fin.induction with
      | zero =>
          exact realizationWeakEquivalence_of_iso_square
            (outerLatchingStage_zero_iso X (n + 1))
            (outerLatchingStage_zero_iso Y (n + 1))
            (eta.app (Opposite.op (SimplexCategory.mk (n + 1))))
            (outerLatchingStageMap eta (n + 1) 0)
            (outerLatchingStage_zero_iso_naturality eta (n + 1))
            (hEta (n + 1))
      | succ r ihr =>
          let eSourceX := Subcomplex.eqToIso
            (outerLatchingStageSourceOverlap_succ X n r)
          let eSourceY := Subcomplex.eqToIso
            (outerLatchingStageSourceOverlap_succ Y n r)
          let eBeforeX := Subcomplex.eqToIso
            (outerLatchingStageBefore_succ_eq_stage X n r)
          let eBeforeY := Subcomplex.eqToIso
            (outerLatchingStageBefore_succ_eq_stage Y n r)
          have hSource : realizationWeakEquivalences
              (outerLatchingStageSourceOverlapMap eta (n + 1) r.succ) :=
            realizationWeakEquivalence_of_iso_square_rev eSourceX
              eSourceY
              (outerLatchingStageSourceOverlapMap eta (n + 1) r.succ)
              (outerLatchingStageMap eta n r)
              (outerLatchingStageSourceOverlap_succ_naturality eta n r)
              (ih r)
          have hBefore : realizationWeakEquivalences
              (outerLatchingStageBeforeMap eta (n + 1) r.succ) :=
            realizationWeakEquivalence_of_iso_square_rev eBeforeX
              eBeforeY
              (outerLatchingStageBeforeMap eta (n + 1) r.succ)
              (outerLatchingStageMap eta (n + 1) r.castSucc)
              (outerLatchingStageBefore_succ_naturality eta n r)
              ihr
          exact realizationWeakEquivalence_map_of_isPushouts
            (outerLatchingStageSource_isPushout X (n + 1) r.succ).flip
            (outerLatchingStageSource_isPushout Y (n + 1) r.succ).flip
            (outerLatchingStageSource_left_naturality
              eta (n + 1) r.succ).symm
            (outerLatchingStageSource_top_naturality
              eta (n + 1) r.succ).symm
            (outerLatchingStageSource_bottom_naturality
              eta (n + 1) r.succ).symm
            (outerLatchingStageSource_right_naturality
              eta (n + 1) r.succ).symm
            hSource (hEta (n + 1)) hBefore

/-- Outer latching maps are realization weak equivalences under the rowwise
hypothesis. -/
private theorem outerLatchingMap_mem_realizationWeakEquivalences
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hEta : ∀ n,
      realizationWeakEquivalences
        (eta.app (Opposite.op (SimplexCategory.mk n))))
    (n : ℕ) : realizationWeakEquivalences (outerLatchingMap eta n) := by
  cases n with
  | zero =>
      let e0 :
          ((⊥ : (X.obj (Opposite.op (SimplexCategory.mk 0))).Subcomplex) :
            SSet.{u}) ≅
            ((⊥ : (Y.obj (Opposite.op (SimplexCategory.mk 0))).Subcomplex) :
              SSet.{u}) :=
        Iso.mk default default (by subsingleton) (by subsingleton)
      let _ : IsIso e0.hom := e0.isIso_hom
      have he0 : realizationWeakEquivalences e0.hom := by
        have h := RespectsIso.precomp realizationWeakEquivalences e0.hom
          (𝟙 _) (realizationWeakEquivalences.id_mem _)
        simpa using h
      exact realizationWeakEquivalence_of_iso_square
        (Subcomplex.eqToIso (outerLatching_zero X)).symm
        (Subcomplex.eqToIso (outerLatching_zero Y)).symm
        e0.hom
        (outerLatchingMap eta 0) (by subsingleton)
        he0
  | succ n =>
      exact realizationWeakEquivalence_of_iso_square
        (Subcomplex.eqToIso (outerLatchingStage_last X n))
        (Subcomplex.eqToIso (outerLatchingStage_last Y n))
        (outerLatchingStageMap eta n (Fin.last n))
        (outerLatchingMap eta (n + 1))
        (outerLatchingStage_last_naturality eta n)
        (outerLatchingStageMap_mem_realizationWeakEquivalences eta hEta n
          (Fin.last n))

/-! ## Union-product attachment domains -/

/-- Taking the objectwise product on the right with a finite simplicial set
preserves realization weak equivalences. -/
private theorem realizationWeakEquivalences.tensorHom_id_of_finite_right
    {A B K : SSet.{u}} (f : A ⟶ B)
    (hf : realizationWeakEquivalences f) [K.Finite] :
    realizationWeakEquivalences (f ⊗ₘ 𝟙 K) := by
  let eA : A ⊗ K ≅ A ⨯ K :=
    IsLimit.conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A K)
      (limit.isLimit (pair A K))
  let eB : B ⊗ K ≅ B ⨯ K :=
    IsLimit.conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct B K)
      (limit.isLimit (pair B K))
  have eA_fst : eA.hom ≫ Limits.prod.fst =
      CartesianMonoidalCategory.fst A K := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A K)
      (limit.isLimit (pair A K)) ⟨WalkingPair.left⟩
  have eA_snd : eA.hom ≫ Limits.prod.snd =
      CartesianMonoidalCategory.snd A K := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A K)
      (limit.isLimit (pair A K)) ⟨WalkingPair.right⟩
  have eB_fst : eB.hom ≫ Limits.prod.fst =
      CartesianMonoidalCategory.fst B K := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct B K)
      (limit.isLimit (pair B K)) ⟨WalkingPair.left⟩
  have eB_snd : eB.hom ≫ Limits.prod.snd =
      CartesianMonoidalCategory.snd B K := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct B K)
      (limit.isLimit (pair B K)) ⟨WalkingPair.right⟩
  apply realizationWeakEquivalence_of_iso_square_rev eA eB
    (f ⊗ₘ 𝟙 K) (Limits.prod.map f (𝟙 K))
  · apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prod.map_fst, ← Category.assoc,
        eA_fst, Category.assoc, eB_fst]
      ext a z
      rfl
    · rw [Category.assoc, Limits.prod.map_snd, ← Category.assoc,
        eA_snd, Category.assoc, eB_snd]
      ext a z
      rfl
  · exact realizationWeakEquivalences.prodMap_id_of_finite_right f hf

/-- Naturality on the row-boundary leg of the union-product attachment
domain. -/
private theorem diagonalAttachmentDomainMap_ι₁_naturality
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    Subcomplex.unionProd.ι₁ (outerLatching X (n + 1))
        (boundary (n + 1)) ≫ diagonalAttachmentDomainMap eta n =
      (eta.app (Opposite.op (SimplexCategory.mk (n + 1))) ⊗ₘ
          𝟙 (boundary (n + 1) : SSet.{u})) ≫
        Subcomplex.unionProd.ι₁ (outerLatching Y (n + 1))
          (boundary (n + 1)) := by
  ext a z
  rfl

/-- Naturality on the latching-simplex leg of the union-product attachment
domain. -/
private theorem diagonalAttachmentDomainMap_ι₂_naturality
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    Subcomplex.unionProd.ι₂ (outerLatching X (n + 1))
        (boundary (n + 1)) ≫ diagonalAttachmentDomainMap eta n =
      (outerLatchingMap eta (n + 1) ⊗ₘ 𝟙 Δ[n + 1]) ≫
        Subcomplex.unionProd.ι₂ (outerLatching Y (n + 1))
          (boundary (n + 1)) := by
  ext a z
  rfl

/-- The map on a union-product attachment domain is a realization weak
equivalence under the rowwise hypothesis. -/
private theorem diagonalAttachmentDomainMap_mem_realizationWeakEquivalences
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hEta : ∀ n,
      realizationWeakEquivalences
        (eta.app (Opposite.op (SimplexCategory.mk n))))
    (n : ℕ) :
    realizationWeakEquivalences (diagonalAttachmentDomainMap eta n) := by
  have hL := outerLatchingMap_mem_realizationWeakEquivalences eta hEta
    (n + 1)
  have hLB : realizationWeakEquivalences
      (outerLatchingMap eta (n + 1) ⊗ₘ
        𝟙 (boundary (n + 1) : SSet.{u})) := by
    exact realizationWeakEquivalences.tensorHom_id_of_finite_right
      (outerLatchingMap eta (n + 1)) hL
  have hRowB : realizationWeakEquivalences
      (eta.app (Opposite.op (SimplexCategory.mk (n + 1))) ⊗ₘ
        𝟙 (boundary (n + 1) : SSet.{u})) := by
    exact realizationWeakEquivalences.tensorHom_id_of_finite_right
      (eta.app (Opposite.op (SimplexCategory.mk (n + 1))))
      (hEta (n + 1))
  have hLS : realizationWeakEquivalences
      (outerLatchingMap eta (n + 1) ⊗ₘ 𝟙 Δ[n + 1]) := by
    exact realizationWeakEquivalences.tensorHom_id_of_finite_right
      (outerLatchingMap eta (n + 1)) hL
  let _ : Mono ((outerLatching X (n + 1)).ι ▷
      (boundary (n + 1) : SSet.{u})) := by
    rw [NatTrans.mono_iff_mono_app]
    intro a
    rw [mono_iff_injective]
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
    change (x₁.val, x₂) = (y₁.val, y₂) at h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · have h₂ := congrArg Prod.snd h
      exact h₂
  let _ : Mono ((outerLatching Y (n + 1)).ι ▷
      (boundary (n + 1) : SSet.{u})) := by
    rw [NatTrans.mono_iff_mono_app]
    intro a
    rw [mono_iff_injective]
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
    change (x₁.val, x₂) = (y₁.val, y₂) at h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · have h₂ := congrArg Prod.snd h
      exact h₂
  exact realizationWeakEquivalence_map_of_isPushouts
    (Subcomplex.unionProd.isPushout (outerLatching X (n + 1))
      (boundary (n + 1)))
    (Subcomplex.unionProd.isPushout (outerLatching Y (n + 1))
      (boundary (n + 1)))
    (by ext a z <;> rfl)
    (by ext a z <;> rfl)
    (diagonalAttachmentDomainMap_ι₁_naturality eta n)
    (diagonalAttachmentDomainMap_ι₂_naturality eta n)
    hLB hRowB hLS

/-! ## Finite diagonal-filtration stages -/

@[reassoc]
private theorem diagonalFiltration_zero_iso_hom_ι
    (X : SimplicialObject SSet.{u}) :
    (diagonalFiltration_zero_iso X).hom ≫
        (diagonalFiltration X 0).ι = diagonalCellMap X 0 := by
  simp [diagonalFiltration_zero_iso]

/-- The zeroth-filtration isomorphism is natural in maps of bisimplicial
sets. -/
private theorem diagonalFiltration_zero_iso_naturality
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) :
    (diagonalFiltration_zero_iso X).hom ≫
        diagonalFiltrationNatMap eta 0 =
      (eta.app (Opposite.op (SimplexCategory.mk 0)) ⊗ₘ 𝟙 Δ[0]) ≫
        (diagonalFiltration_zero_iso Y).hom := by
  apply (cancel_mono (diagonalFiltration Y 0).ι).mp
  simp only [Category.assoc, diagonalFiltrationNatMap_ι,
    diagonalFiltration_zero_iso_hom_ι,
    diagonalFiltration_zero_iso_hom_ι_assoc]
  exact (diagonalCellMap_naturality eta 0).symm

/-- Every finite diagonal-filtration map is a realization weak equivalence
under the rowwise hypothesis. -/
private theorem diagonalFiltrationNatMap_mem_realizationWeakEquivalences
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hEta : ∀ n,
      realizationWeakEquivalences
        (eta.app (Opposite.op (SimplexCategory.mk n)))) :
    ∀ n, realizationWeakEquivalences (diagonalFiltrationNatMap eta n) := by
  intro n
  induction n with
  | zero =>
      have hCell : realizationWeakEquivalences
          (eta.app (Opposite.op (SimplexCategory.mk 0)) ⊗ₘ 𝟙 Δ[0]) :=
        realizationWeakEquivalences.tensorHom_id_of_finite_right
          (eta.app (Opposite.op (SimplexCategory.mk 0))) (hEta 0)
      exact realizationWeakEquivalence_of_iso_square
        (diagonalFiltration_zero_iso X)
        (diagonalFiltration_zero_iso Y)
        (eta.app (Opposite.op (SimplexCategory.mk 0)) ⊗ₘ 𝟙 Δ[0])
        (diagonalFiltrationNatMap eta 0)
        (diagonalFiltration_zero_iso_naturality eta) hCell
  | succ n ih =>
      have hDomain :=
        diagonalAttachmentDomainMap_mem_realizationWeakEquivalences
          eta hEta n
      have hCell : realizationWeakEquivalences
          (eta.app (Opposite.op (SimplexCategory.mk (n + 1))) ⊗ₘ
            𝟙 Δ[n + 1]) :=
        realizationWeakEquivalences.tensorHom_id_of_finite_right
          (eta.app (Opposite.op (SimplexCategory.mk (n + 1))))
          (hEta (n + 1))
      exact realizationWeakEquivalence_map_of_isPushouts
        (diagonalFiltrationSucc_isPushout X n).flip
        (diagonalFiltrationSucc_isPushout Y n).flip
        (diagonalAttachmentDomainMap_ι eta n).symm
        (diagonalAttachmentTopMap_naturality eta n).symm
        (diagonalCellToFiltrationSucc_naturality eta n).symm
        (diagonalFiltrationMap_naturality eta (Nat.le_succ n)).symm
        hDomain hCell ih

/-! ## The sequential filtration and its colimit -/

/-- The finite diagonal-filtration stages, with their inclusion maps. -/
noncomputable abbrev diagonalFiltrationFunctor
    (X : SimplicialObject SSet.{u}) : Functor ℕ SSet.{u} where
  obj n := diagonalFiltration X n
  map {n m} f := diagonalFiltrationMap X (leOfHom f)
  map_id n := by
    apply (cancel_mono (diagonalFiltration X n).ι).mp
    simp [diagonalFiltrationMap]
  map_comp {n m k} f g := by
    apply (cancel_mono (diagonalFiltration X k).ι).mp
    simp [diagonalFiltrationMap]

@[simp]
theorem diagonalFiltrationFunctor_obj
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (diagonalFiltrationFunctor X).obj n =
      (diagonalFiltration X n : SSet.{u}) :=
  rfl

theorem diagonalFiltrationFunctor_map
    (X : SimplicialObject SSet.{u}) {n m : ℕ} (f : n ⟶ m) :
    (diagonalFiltrationFunctor X).map f =
      diagonalFiltrationMap X (leOfHom f) :=
  rfl

/-- The canonical cocone from the finite filtration to the full diagonal. -/
noncomputable def diagonalFiltrationCocone
    (X : SimplicialObject SSet.{u}) :
    Cocone (diagonalFiltrationFunctor X) where
  pt := simplicialDiagonalFunctor.obj X
  ι :=
    { app := fun n => (diagonalFiltration X n).ι
      naturality := by
        intro n m f
        change diagonalFiltrationMap X (leOfHom f) ≫
            (diagonalFiltration X m).ι =
          (diagonalFiltration X n).ι ≫ 𝟙 _
        rw [Category.comp_id]
        exact Subcomplex.homOfLE_ι
          (diagonalFiltration_monotone X (leOfHom f)) }

@[simp]
theorem diagonalFiltrationCocone_ι_app
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (diagonalFiltrationCocone X).ι.app n =
      (diagonalFiltration X n).ι :=
  rfl

/-- The finite diagonal filtration has colimit the full diagonal. -/
noncomputable def diagonalFiltrationCoconeIsColimit
    (X : SimplicialObject SSet.{u}) :
    IsColimit (diagonalFiltrationCocone X) :=
  IsColimit.ofIsoColimit
    (isColimitOfPreserves Subcomplex.toSSetFunctor
      (CompleteLattice.colimitCocone
        (diagonalFiltration_monotone X).functor).isColimit)
    (Cocone.ext
      (Subcomplex.eqToIso (iSup_diagonalFiltration_eq_top X) ≪≫
        Subcomplex.topIso (simplicialDiagonalFunctor.obj X)))

/-- A map of bisimplicial sets induces a map of diagonal-filtration
diagrams. -/
noncomputable def diagonalFiltrationNatTrans
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) :
    diagonalFiltrationFunctor X ⟶ diagonalFiltrationFunctor Y where
  app n := diagonalFiltrationNatMap eta n
  naturality {n m} f := by
    simpa only [diagonalFiltrationFunctor_map] using
      (diagonalFiltrationMap_naturality eta (leOfHom f)).symm

@[simp]
theorem diagonalFiltrationNatTrans_app
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    (diagonalFiltrationNatTrans eta).app n =
      diagonalFiltrationNatMap eta n :=
  rfl

/-! ## Rowwise weak equivalences -/

/-- A map of bisimplicial sets that is a realization weak
equivalence in every outer degree induces a realization weak equivalence on
the simplicial diagonal. -/
theorem simplicialDiagonal_map_mem_realizationWeakEquivalences
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hEta : ∀ n,
      realizationWeakEquivalences
        (eta.app (Opposite.op (SimplexCategory.mk n)))) :
    realizationWeakEquivalences (simplicialDiagonalFunctor.map eta) := by
  apply realizationWeakEquivalences.of_isColimit_nat_mono
    (diagonalFiltrationNatTrans eta)
    (diagonalFiltrationCoconeIsColimit X)
    (diagonalFiltrationCoconeIsColimit Y)
    (simplicialDiagonalFunctor.map eta)
  · intro n
    exact (diagonalFiltrationNatMap_ι eta n).symm
  · intro i j f
    change Mono (Subcomplex.homOfLE
      (diagonalFiltration_monotone X (leOfHom f)))
    infer_instance
  · intro i j f
    change Mono (Subcomplex.homOfLE
      (diagonalFiltration_monotone Y (leOfHom f)))
    infer_instance
  · exact diagonalFiltrationNatMap_mem_realizationWeakEquivalences eta hEta

/-- Inner-row realization weak equivalences induce a realization weak
equivalence on the diagonal, by transposing the bisimplicial set. -/
theorem simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hEta : ∀ n, realizationWeakEquivalences
      ((simplicialTransposeFunctor.map eta).app
        (Opposite.op (SimplexCategory.mk n)))) :
    realizationWeakEquivalences (simplicialDiagonalFunctor.map eta) := by
  apply realizationWeakEquivalence_of_iso_square
    (simplicialDiagonalTransposeIso X)
    (simplicialDiagonalTransposeIso Y)
    (simplicialDiagonalFunctor.map (simplicialTransposeFunctor.map eta))
    (simplicialDiagonalFunctor.map eta)
    (simplicialDiagonalTransposeIso_naturality eta).symm
  exact simplicialDiagonal_map_mem_realizationWeakEquivalences
    (simplicialTransposeFunctor.map eta) hEta

end SSet

end
