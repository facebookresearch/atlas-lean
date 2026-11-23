/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.Topology.Category.CGWH.Products
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnderlyingFiniteLimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Binary products of simplicial-set realizations in CGWH

The direct realization functor from simplicial sets to compactly generated
weak Hausdorff spaces preserves binary products.  The inverse continuity is
proved on compact probes by factoring both coordinates through finite
subcomplexes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology
open scoped MonoidalCategory

namespace SSet

private theorem prodComparison_toTop_bijective (X Y : SSet.{v}) :
    Function.Bijective (Limits.prodComparison SSet.toTop X Y) := by
  let cTop := Limits.prodComparison SSet.toTop X Y
  let cForget := Limits.prodComparison (CategoryTheory.forget TopCat)
    (SSet.toTop.obj X) (SSet.toTop.obj Y)
  let _ : IsIso cForget := inferInstance
  let _ : IsIso ((CategoryTheory.forget TopCat).map cTop ≫ cForget) := by
    rw [← Limits.prodComparison_comp]
    infer_instance
  let _ : IsIso ((CategoryTheory.forget TopCat).map cTop) :=
    IsIso.of_isIso_comp_right _ cForget
  exact (CategoryTheory.isIso_iff_bijective
    ((CategoryTheory.forget TopCat).map cTop)).mp inferInstance

private theorem prodComparison_forget (X Y : SSet.{v}) :
    CGWH.cgwhToTop.{u, v}.map
        (Limits.prodComparison SSet.toCGWH.{u, v} X Y) ≫
      CGWH.prodComparisonToTop
        (SSet.toCGWH.{u, v}.obj X) (SSet.toCGWH.{u, v}.obj Y) =
    (SSet.realizationToTopIso.{u, v}).hom.app (X ⨯ Y) ≫
      Limits.prodComparison SSet.toTop X Y ≫
      Limits.prod.map
        ((SSet.realizationToTopIso.{u, v}).inv.app X)
        ((SSet.realizationToTopIso.{u, v}).inv.app Y) ≫
      (TopCat.prodIsoProd
        (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj X))
        (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj Y))).hom := by
  unfold CGWH.prodComparisonToTop
  rw [← Category.assoc, ← Limits.prodComparison_comp]
  rw [Limits.prodComparison_natural_of_natTrans_assoc]
  simp

private theorem prodComparison_toCGWH_bijective (X Y : SSet.{v}) :
    Function.Bijective
      (Limits.prodComparison SSet.toCGWH.{u, v} X Y) := by
  let c := Limits.prodComparison SSet.toCGWH.{u, v} X Y
  let d := CGWH.prodComparisonToTop
    (SSet.toCGWH.{u, v}.obj X) (SSet.toCGWH.{u, v}.obj Y)
  have hRight : Function.Bijective
      ((SSet.realizationToTopIso.{u, v}).hom.app (X ⨯ Y) ≫
        Limits.prodComparison SSet.toTop X Y ≫
        Limits.prod.map
          ((SSet.realizationToTopIso.{u, v}).inv.app X)
          ((SSet.realizationToTopIso.{u, v}).inv.app Y) ≫
        (TopCat.prodIsoProd
          (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj X))
          (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj Y))).hom) := by
    have hδ : Function.Bijective
        (SSet.realizationToTopIso.{u, v}.hom.app (X ⨯ Y)) :=
      ConcreteCategory.bijective_of_isIso _
    have hr : Function.Bijective
        (Limits.prodComparison SSet.toTop X Y) :=
      prodComparison_toTop_bijective X Y
    have hm : Function.Bijective
        (Limits.prod.map
          ((SSet.realizationToTopIso.{u, v}).inv.app X)
          ((SSet.realizationToTopIso.{u, v}).inv.app Y)) :=
      ConcreteCategory.bijective_of_isIso _
    have hp : Function.Bijective
        (TopCat.prodIsoProd
          (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj X))
          (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj Y))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact hp.comp (hm.comp (hr.comp hδ))
  have hComp : Function.Bijective
      (CGWH.cgwhToTop.map c ≫ d) := by
    rw [prodComparison_forget]
    exact hRight
  have hd : Function.Bijective d :=
    CGWH.prodComparisonToTop_bijective _ _
  have hcTop : Function.Bijective (CGWH.cgwhToTop.map c) :=
    (hd.of_comp_iff' _).mp hComp
  exact hcTop

private theorem prodComparison_toTop_isIso_of_finite
    (A B : SSet.{v}) [A.Finite] [B.Finite] :
    IsIso (Limits.prodComparison SSet.toTop A B) := by
  let tensorProdIso : A ⊗ B ≅ A ⨯ B :=
    IsLimit.conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A B)
      (limit.isLimit _)
  let _ : SSet.Finite (A ⨯ B) :=
    SSet.finite_of_iso tensorProdIso
  let _ : CompactSpace (SSet.toTop.obj (A ⨯ B)) := inferInstance
  let rawPair := TopCat.of
    (↑(SSet.toTop.obj A) × ↑(SSet.toTop.obj B))
  let selectedToRaw := TopCat.homeoOfIso
    (TopCat.prodIsoProd (SSet.toTop.obj A) (SSet.toTop.obj B))
  let _ : T2Space rawPair := inferInstance
  let _ : T2Space ↑(SSet.toTop.obj A ⨯ SSet.toTop.obj B) :=
    selectedToRaw.symm.t2Space
  have hbij := prodComparison_toTop_bijective A B
  have hhomeo : IsHomeomorph
      (Limits.prodComparison SSet.toTop A B) :=
    (Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective
        (Limits.prodComparison SSet.toTop A B) hbij)
      (Limits.prodComparison SSet.toTop A B).hom.continuous).isHomeomorph
  exact (TopCat.isIso_iff_isHomeomorph _).mpr hhomeo

private theorem prodComparison_toCGWH_isIso_of_finite
    (A B : SSet.{v}) [A.Finite] [B.Finite] :
    IsIso (Limits.prodComparison SSet.toCGWH.{u, v} A B) := by
  let eA := TopCat.homeoOfIso
    (SSet.realizationToTopIso.{u, v}.app A)
  let _ : CompactSpace (SSet.toCGWH.{u, v}.obj A) :=
    eA.symm.compactSpace
  let _ : T2Space (SSet.toCGWH.{u, v}.obj A) :=
    eA.symm.t2Space
  let _ : LocallyCompactSpace (SSet.toCGWH.{u, v}.obj A) :=
    inferInstance
  let c := Limits.prodComparison SSet.toCGWH.{u, v} A B
  let d := CGWH.prodComparisonToTop
    (SSet.toCGWH.{u, v}.obj A) (SSet.toCGWH.{u, v}.obj B)
  have hdHomeo : IsHomeomorph d :=
    CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_left _ _
  let _ : IsIso d :=
    (TopCat.isIso_iff_isHomeomorph _).mpr hdHomeo
  let _ : IsIso (Limits.prodComparison SSet.toTop A B) :=
    prodComparison_toTop_isIso_of_finite A B
  have hComp : IsIso (CGWH.cgwhToTop.map c ≫ d) := by
    rw [prodComparison_forget]
    infer_instance
  let _ : IsIso (CGWH.cgwhToTop.map c) :=
    IsIso.of_isIso_comp_right _ d
  exact CGWH.fullyFaithfulCgwhToTop.isIso_of_isIso_map c

private theorem exists_finite_subcomplex_factor
    {K : Type u} [TopologicalSpace K] [CompactSpace K] {X : SSet.{v}}
    (g : K → SSet.toTop.obj X) (hg : Continuous g) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{v}))
      (gA : K → SSet.toTop.obj (A : SSet.{v})),
      Continuous gA ∧ ∀ x, SSet.toTop.map A.ι (gA x) = g x := by
  have hRange : IsCompact (Set.range g) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hg
  obtain ⟨A, hA, hsub⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact X (Set.range g) hRange
  choose gA hgA using fun x : K ↦ hsub (Set.mem_range_self x)
  have hEmb : IsEmbedding (SSet.toTop.map A.ι).hom :=
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι A).isEmbedding
  have hcont : Continuous gA := hEmb.continuous_iff.mpr (by
    apply hg.congr
    intro x
    exact (hgA x).symm)
  exact ⟨A, hA, gA, hcont, hgA⟩

private theorem prodComparison_inverse_continuous (X Y : SSet.{v}) :
    Continuous
      (Equiv.ofBijective
        (Limits.prodComparison SSet.toCGWH.{u, v} X Y)
        (prodComparison_toCGWH_bijective X Y)).symm := by
  let F := SSet.toCGWH.{u, v}
  let J := CGWH.cgwhToTop.{u, v}
  let δ := SSet.realizationToTopIso.{u, v}
  let cXY := Limits.prodComparison F X Y
  let hbij := prodComparison_toCGWH_bijective X Y
  let e := Equiv.ofBijective cXY hbij
  apply continuous_from_uCompactlyGeneratedSpace.{u, v, v} e.symm
  intro K g
  let gX : K → SSet.toTop.obj X := fun k ↦
    δ.hom.app X
      (J.map (Limits.prod.fst : F.obj X ⨯ F.obj Y ⟶ F.obj X) (g k))
  let gY : K → SSet.toTop.obj Y := fun k ↦
    δ.hom.app Y
      (J.map (Limits.prod.snd : F.obj X ⨯ F.obj Y ⟶ F.obj Y) (g k))
  have hgX : Continuous gX :=
    (δ.hom.app X).hom.continuous.comp
      ((J.map (Limits.prod.fst : F.obj X ⨯ F.obj Y ⟶ F.obj X)).hom.continuous.comp
        g.continuous)
  have hgY : Continuous gY :=
    (δ.hom.app Y).hom.continuous.comp
      ((J.map (Limits.prod.snd : F.obj X ⨯ F.obj Y ⟶ F.obj Y)).hom.continuous.comp
        g.continuous)
  obtain ⟨A, hA, gA, hgA, hgAeq⟩ :=
    exists_finite_subcomplex_factor gX hgX
  obtain ⟨B, hB, gB, hgB, hgBeq⟩ :=
    exists_finite_subcomplex_factor gY hgY
  let _ : SSet.Finite (A : SSet.{v}) := hA
  let _ : SSet.Finite (B : SSet.{v}) := hB
  let cAB := Limits.prodComparison F (A : SSet.{v}) (B : SSet.{v})
  let _ : IsIso cAB :=
    prodComparison_toCGWH_isIso_of_finite (A : SSet.{v}) (B : SSet.{v})
  let eA := TopCat.homeoOfIso (δ.app (A : SSet.{v}))
  let _ : CompactSpace (F.obj (A : SSet.{v})) := eA.symm.compactSpace
  let _ : T2Space (F.obj (A : SSet.{v})) := eA.symm.t2Space
  let _ : LocallyCompactSpace (F.obj (A : SSet.{v})) := inferInstance
  let dAB := CGWH.prodComparisonToTop
    (F.obj (A : SSet.{v})) (F.obj (B : SSet.{v}))
  let _ : IsIso dAB :=
    (TopCat.isIso_iff_isHomeomorph dAB).mpr
      (CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_left _ _)
  let pairMap : K →
      (↑(J.obj (F.obj (A : SSet.{v}))) ×
        ↑(J.obj (F.obj (B : SSet.{v})))) := fun k ↦
    (δ.inv.app (A : SSet.{v}) (gA k),
      δ.inv.app (B : SSet.{v}) (gB k))
  have hpairMap : Continuous pairMap :=
    ((δ.inv.app (A : SSet.{v})).hom.continuous.comp hgA).prodMk
      ((δ.inv.app (B : SSet.{v})).hom.continuous.comp hgB)
  let nativePair : K →
      (F.obj (A : SSet.{v}) ⨯ F.obj (B : SSet.{v}) : CGWH.{u, v}) :=
    fun k ↦ inv dAB (pairMap k)
  have hnativePair : Continuous nativePair :=
    (inv dAB).hom.continuous.comp hpairMap
  let localFinite : K → F.obj ((A : SSet.{v}) ⨯ (B : SSet.{v})) :=
    fun k ↦ inv cAB (nativePair k)
  have hlocalFinite : Continuous localFinite :=
    (ConcreteCategory.hom (inv cAB)).continuous.comp hnativePair
  let localMap : K → F.obj (X ⨯ Y) := fun k ↦
    F.map (Limits.prod.map A.ι B.ι) (localFinite k)
  have hlocalMap : Continuous localMap :=
    (ConcreteCategory.hom (F.map (Limits.prod.map A.ι B.ι))).continuous.comp
      hlocalFinite
  have hdFst (P Q : CGWH.{u, v}) (z : (P ⨯ Q : CGWH.{u, v})) :
      (CGWH.prodComparisonToTop P Q z).1 =
        (Limits.prod.fst : P ⨯ Q ⟶ P) z := by
    exact ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst P Q) z
  have hdSnd (P Q : CGWH.{u, v}) (z : (P ⨯ Q : CGWH.{u, v})) :
      (CGWH.prodComparisonToTop P Q z).2 =
        (Limits.prod.snd : P ⨯ Q ⟶ Q) z := by
    exact ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd P Q) z
  have hlocal (k : K) : localMap k = e.symm (g k) := by
    apply hbij.1
    have hNat := ConcreteCategory.congr_hom
      (Limits.prodComparison_natural (F := F) A.ι B.ι) (localFinite k)
    have hcAB : cAB (localFinite k) = nativePair k := by
      simpa only [ConcreteCategory.comp_apply,
        CategoryTheory.id_apply] using
        ConcreteCategory.congr_hom (IsIso.inv_hom_id cAB) (nativePair k)
    have hright :
        (Limits.prod.map (F.map A.ι) (F.map B.ι)) (nativePair k) =
          g k := by
      apply (CGWH.prodComparisonToTop_bijective _ _).1
      apply Prod.ext
      · rw [hdFst, hdFst]
        have hMap := ConcreteCategory.congr_hom
          (Limits.prod.map_fst (F.map A.ι) (F.map B.ι)) (nativePair k)
        have hdInv : dAB (nativePair k) = pairMap k := by
          simpa only [ConcreteCategory.comp_apply,
            CategoryTheory.id_apply] using
            ConcreteCategory.congr_hom (IsIso.inv_hom_id dAB) (pairMap k)
        have hNativeFst :
            (Limits.prod.fst :
              F.obj (A : SSet.{v}) ⨯ F.obj (B : SSet.{v}) ⟶
                F.obj (A : SSet.{v})) (nativePair k) =
              δ.inv.app (A : SSet.{v}) (gA k) := by
          have h := congrArg (fun p ↦ p.1) hdInv
          rw [hdFst] at h
          exact h
        have hCoord :
            F.map A.ι (δ.inv.app (A : SSet.{v}) (gA k)) =
              (Limits.prod.fst : F.obj X ⨯ F.obj Y ⟶ F.obj X) (g k) := by
          apply (TopCat.homeoOfIso (δ.app X)).injective
          calc
            δ.hom.app X
                  (F.map A.ι (δ.inv.app (A : SSet.{v}) (gA k))) =
                SSet.toTop.map A.ι
                  (δ.hom.app (A : SSet.{v})
                    (δ.inv.app (A : SSet.{v}) (gA k))) :=
              ConcreteCategory.congr_hom (δ.hom.naturality A.ι) _
            _ = SSet.toTop.map A.ι (gA k) :=
              congrArg (SSet.toTop.map A.ι)
                (TopCat.inv_hom_id_apply (δ.app (A : SSet.{v})) (gA k))
            _ = gX k := hgAeq k
            _ = δ.hom.app X
                ((Limits.prod.fst : F.obj X ⨯ F.obj Y ⟶ F.obj X) (g k)) := rfl
        exact hMap.trans ((congrArg (F.map A.ι) hNativeFst).trans hCoord)
      · rw [hdSnd, hdSnd]
        have hMap := ConcreteCategory.congr_hom
          (Limits.prod.map_snd (F.map A.ι) (F.map B.ι)) (nativePair k)
        have hdInv : dAB (nativePair k) = pairMap k := by
          simpa only [ConcreteCategory.comp_apply,
            CategoryTheory.id_apply] using
            ConcreteCategory.congr_hom (IsIso.inv_hom_id dAB) (pairMap k)
        have hNativeSnd :
            (Limits.prod.snd :
              F.obj (A : SSet.{v}) ⨯ F.obj (B : SSet.{v}) ⟶
                F.obj (B : SSet.{v})) (nativePair k) =
              δ.inv.app (B : SSet.{v}) (gB k) := by
          have h := congrArg (fun p ↦ p.2) hdInv
          rw [hdSnd] at h
          exact h
        have hCoord :
            F.map B.ι (δ.inv.app (B : SSet.{v}) (gB k)) =
              (Limits.prod.snd : F.obj X ⨯ F.obj Y ⟶ F.obj Y) (g k) := by
          apply (TopCat.homeoOfIso (δ.app Y)).injective
          calc
            δ.hom.app Y
                  (F.map B.ι (δ.inv.app (B : SSet.{v}) (gB k))) =
                SSet.toTop.map B.ι
                  (δ.hom.app (B : SSet.{v})
                    (δ.inv.app (B : SSet.{v}) (gB k))) :=
              ConcreteCategory.congr_hom (δ.hom.naturality B.ι) _
            _ = SSet.toTop.map B.ι (gB k) :=
              congrArg (SSet.toTop.map B.ι)
                (TopCat.inv_hom_id_apply (δ.app (B : SSet.{v})) (gB k))
            _ = gY k := hgBeq k
            _ = δ.hom.app Y
                ((Limits.prod.snd : F.obj X ⨯ F.obj Y ⟶ F.obj Y) (g k)) := rfl
        exact hMap.trans ((congrArg (F.map B.ι) hNativeSnd).trans hCoord)
    have hRight : cXY (e.symm (g k)) = g k := e.apply_symm_apply (g k)
    exact hNat.trans ((congrArg
      (Limits.prod.map (F.map A.ι) (F.map B.ι)) hcAB).trans
        (hright.trans hRight.symm))
  change Continuous (fun k : K ↦ e.symm (g k))
  exact hlocalMap.congr hlocal

private theorem realizationProdIsoCGWH_exists (X Y : SSet.{v}) :
    ∃ e : SSet.toCGWH.{u, v}.obj (X ⨯ Y) ≅
        SSet.toCGWH.{u, v}.obj X ⨯ SSet.toCGWH.{u, v}.obj Y,
      e.hom = Limits.prodComparison SSet.toCGWH.{u, v} X Y := by
  let c := Limits.prodComparison SSet.toCGWH.{u, v} X Y
  let hbij := prodComparison_toCGWH_bijective X Y
  let e := Equiv.ofBijective c hbij
  let eInv : SSet.toCGWH.{u, v}.obj X ⨯ SSet.toCGWH.{u, v}.obj Y ⟶
      SSet.toCGWH.{u, v}.obj (X ⨯ Y) :=
    ConcreteCategory.ofHom
      ⟨e.symm, prodComparison_inverse_continuous X Y⟩
  let i : SSet.toCGWH.{u, v}.obj (X ⨯ Y) ≅
      SSet.toCGWH.{u, v}.obj X ⨯ SSet.toCGWH.{u, v}.obj Y :=
    { hom := c
      inv := eInv
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        exact e.apply_symm_apply y }
  exact ⟨i, rfl⟩

/-- The canonical binary-product comparison for direct realization in CGWH. -/
noncomputable def realizationProdIsoCGWH (X Y : SSet.{v}) :
    SSet.toCGWH.{u, v}.obj (X ⨯ Y) ≅
      SSet.toCGWH.{u, v}.obj X ⨯ SSet.toCGWH.{u, v}.obj Y :=
  Classical.choose (show
    ∃ e : SSet.toCGWH.{u, v}.obj (X ⨯ Y) ≅
        SSet.toCGWH.{u, v}.obj X ⨯ SSet.toCGWH.{u, v}.obj Y,
      e.hom = Limits.prodComparison SSet.toCGWH.{u, v} X Y from by
    exact realizationProdIsoCGWH_exists X Y)

/-- The hom of the realization product isomorphism is the canonical product
comparison. -/
@[simp]
theorem realizationProdIsoCGWH_hom (X Y : SSet.{v}) :
    (realizationProdIsoCGWH.{u, v} X Y).hom =
      Limits.prodComparison SSet.toCGWH.{u, v} X Y :=
  Classical.choose_spec (show
    ∃ e : SSet.toCGWH.{u, v}.obj (X ⨯ Y) ≅
        SSet.toCGWH.{u, v}.obj X ⨯ SSet.toCGWH.{u, v}.obj Y,
      e.hom = Limits.prodComparison SSet.toCGWH.{u, v} X Y from by
    exact realizationProdIsoCGWH_exists X Y)

/-- Direct realization in CGWH preserves binary products. -/
noncomputable instance toCGWH_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair)
      SSet.toCGWH.{u, v} := by
  let _ : ∀ {X Y : SSet.{v}},
      IsIso (Limits.prodComparison SSet.toCGWH.{u, v} X Y) :=
    fun {X Y} => by
      rw [← realizationProdIsoCGWH_hom X Y]
      infer_instance
  exact preservesBinaryProducts_of_isIso_prodComparison _

/-- The realization product isomorphism has the expected first projection. -/
@[simp, reassoc]
theorem realizationProdIsoCGWH_hom_fst (X Y : SSet.{v}) :
    (realizationProdIsoCGWH.{u, v} X Y).hom ≫ Limits.prod.fst =
      SSet.toCGWH.{u, v}.map (Limits.prod.fst : X ⨯ Y ⟶ X) := by
  rw [realizationProdIsoCGWH_hom, Limits.prodComparison_fst]

/-- The realization product isomorphism has the expected second projection. -/
@[simp, reassoc]
theorem realizationProdIsoCGWH_hom_snd (X Y : SSet.{v}) :
    (realizationProdIsoCGWH.{u, v} X Y).hom ≫ Limits.prod.snd =
      SSet.toCGWH.{u, v}.map (Limits.prod.snd : X ⨯ Y ⟶ Y) := by
  rw [realizationProdIsoCGWH_hom, Limits.prodComparison_snd]

/-- The realization product isomorphism is natural in both variables. -/
theorem realizationProdIsoCGWH_naturality
    {X X' Y Y' : SSet.{v}} (f : X ⟶ X') (g : Y ⟶ Y') :
    SSet.toCGWH.{u, v}.map (Limits.prod.map f g) ≫
        (realizationProdIsoCGWH X' Y').hom =
      (realizationProdIsoCGWH X Y).hom ≫
        Limits.prod.map (SSet.toCGWH.map f) (SSet.toCGWH.map g) := by
  simpa only [realizationProdIsoCGWH_hom] using
    (Limits.prodComparison_natural (F := SSet.toCGWH.{u, v}) f g)

/-- After forgetting to TopCat, the native product comparison agrees with
the raw realization comparison and both realization comparison isomorphisms. -/
theorem realizationProdIsoCGWH_forget (X Y : SSet.{v}) :
    CGWH.cgwhToTop.{u, v}.map (realizationProdIsoCGWH X Y).hom ≫
        CGWH.prodComparisonToTop
          (SSet.toCGWH.{u, v}.obj X) (SSet.toCGWH.{u, v}.obj Y) =
      (SSet.realizationToTopIso.{u, v}).hom.app (X ⨯ Y) ≫
        Limits.prodComparison SSet.toTop X Y ≫
        Limits.prod.map
          ((SSet.realizationToTopIso.{u, v}).inv.app X)
          ((SSet.realizationToTopIso.{u, v}).inv.app Y) ≫
        (TopCat.prodIsoProd
          (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj X))
          (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj Y))).hom := by
  rw [realizationProdIsoCGWH_hom]
  exact prodComparison_forget X Y

end SSet
