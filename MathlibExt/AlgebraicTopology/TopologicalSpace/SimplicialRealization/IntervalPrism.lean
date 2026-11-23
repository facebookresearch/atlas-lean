/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.AlgebraicTopology.SimplicialSet.ProdStdSimplexOneCompat
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationStdSimplex
public import Mathlib.Topology.Category.TopCat.Monoidal

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Homeomorph.Lemmas
import MathlibExt.Analysis.Convex.StdSimplex
import MathlibExt.Topology.Convenient.ProperQuotientProduct
import MathlibExt.Topology.Convenient.StdSimplexProductCellGluing

/-!
# All-universe interval-prism gluing

This file defines the canonical interval cells in the realization of
`Δ[n] ⊗ Δ[1]`, descends compatible maps across their finite quotient cover,
and proves the characteristic and endpoint equations.  All affine,
common-face, quotient, extensionality, and reindex machinery is private.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial Topology MonoidalCategory
open Set Finset

open scoped Simplicial

universe u

namespace TopCat.IntervalPrismConjugation

private noncomputable def ssetProductBridge (n : ℕ) :
    ((Limits.prod.functor.obj (Δ[n] : SSet.{u})).obj (Δ[1] : SSet.{u})) ≅
      ((Δ[n] : SSet.{u}) ⨯ (Δ[1] : SSet.{u})) :=
  Iso.refl _

private noncomputable def topProductBridge (n : ℕ) :
    ((Limits.prod.functor.obj
      (SimplexCategory.toTop.{u}.obj ⦋n⦌)).obj TopCat.I.{u}) ≅
      (SimplexCategory.toTop.obj ⦋n⦌ ⨯ TopCat.I) :=
  Iso.refl _

private noncomputable def tensorProdIso (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ⊗ TopCat.I.{u} ≅
      SimplexCategory.toTop.obj ⦋n⦌ ⨯ TopCat.I :=
  (CartesianMonoidalCategory.tensorLeftIsoProd (C := TopCat.{u})
    (SimplexCategory.toTop.obj ⦋n⦌)).app TopCat.I ≪≫
      topProductBridge n

private noncomputable def canonicalCell (n : ℕ) (i : Fin (n + 1)) :
    SimplexCategory.toTop.{u}.obj ⦋n + 1⦌ ⟶
      SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I.{u} :=
  SSet.toTopSimplex.inv.app ⦋n + 1⦌ ≫
    SSet.toTop.map (SSet.prodStdSimplex₁.ι i) ≫
    SSet.toTop.map
      ((CartesianMonoidalCategory.tensorLeftIsoProd (Δ[n] : SSet.{u})).hom.app
        (Δ[1] : SSet.{u})) ≫
    SSet.toTop.map (ssetProductBridge n).hom ≫
    Limits.prodComparison SSet.toTop (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
    Limits.prod.map (SSet.toTopSimplex.hom.app ⦋n⦌)
      SSet.stdSimplex.toTopObjIsoI.hom ≫
    (tensorProdIso.{u} n).inv

private noncomputable def affineCell (n : ℕ) (i : Fin (n + 1)) :
    SimplexCategory.toTop.{u}.obj ⦋n + 1⦌ ⟶
      SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I.{u} :=
  TopCat.ofHom
    { toFun := fun s =>
        (ULift.up (Convexity.StdSimplex.map
            (SimplexCategory.σ i) s.down),
          TopCat.stdSimplexHomeomorphI
            (Convexity.StdSimplex.map
              (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s.down))
      continuous_toFun := by fun_prop }

private theorem tensorProdIso_hom_fst (n : ℕ) :
    (tensorProdIso.{u} n).hom ≫ Limits.prod.fst =
      CartesianMonoidalCategory.fst
        (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I)
    (Limits.limit.isLimit _) ⟨.left⟩

private theorem tensorProdIso_hom_snd (n : ℕ) :
    (tensorProdIso.{u} n).hom ≫ Limits.prod.snd =
      CartesianMonoidalCategory.snd
        (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I)
    (Limits.limit.isLimit _) ⟨.right⟩

private theorem tensorProdIso_inv_fst (n : ℕ) :
    (tensorProdIso.{u} n).inv ≫
        CartesianMonoidalCategory.fst
          (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I =
      Limits.prod.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I)
    (Limits.limit.isLimit _) ⟨.left⟩

private theorem tensorProdIso_inv_snd (n : ℕ) :
    (tensorProdIso.{u} n).inv ≫
        CartesianMonoidalCategory.snd
          (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I =
      Limits.prod.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I)
    (Limits.limit.isLimit _) ⟨.right⟩

private theorem ssetTensorProdIso_hom_fst (n : ℕ) :
    (CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      Limits.prod.fst =
        CartesianMonoidalCategory.fst (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}))
    (Limits.limit.isLimit _) ⟨.left⟩

private theorem ssetTensorProdIso_hom_snd (n : ℕ) :
    (CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      Limits.prod.snd =
        CartesianMonoidalCategory.snd (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}))
    (Limits.limit.isLimit _) ⟨.right⟩

private theorem ssetTensorBridge_hom_fst (n : ℕ) :
    (CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      (ssetProductBridge n).hom ≫ Limits.prod.fst =
        CartesianMonoidalCategory.fst (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) := by
  change
    ((CartesianMonoidalCategory.tensorLeftIsoProd
      (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫ 𝟙 _) ≫
        Limits.prod.fst = _
  rw [Category.comp_id]
  exact ssetTensorProdIso_hom_fst.{u} n

private theorem ssetTensorBridge_hom_snd (n : ℕ) :
    (CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      (ssetProductBridge n).hom ≫ Limits.prod.snd =
        CartesianMonoidalCategory.snd (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) := by
  change
    ((CartesianMonoidalCategory.tensorLeftIsoProd
      (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫ 𝟙 _) ≫
        Limits.prod.snd = _
  rw [Category.comp_id]
  exact ssetTensorProdIso_hom_snd.{u} n

private theorem ssetCell_fst (n : ℕ) (i : Fin (n + 1)) :
    SSet.prodStdSimplex₁.ι i ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      (ssetProductBridge n).hom ≫ Limits.prod.fst =
        SSet.stdSimplex.map (SimplexCategory.σ i) := by
  rw [ssetTensorBridge_hom_fst]
  exact SSet.prodStdSimplex₁.ι_fst i

private theorem ssetCell_snd (n : ℕ) (i : Fin (n + 1)) :
    SSet.prodStdSimplex₁.ι i ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      (ssetProductBridge n).hom ≫ Limits.prod.snd =
        SSet.yonedaEquiv.symm
          (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) := by
  rw [ssetTensorBridge_hom_snd]
  exact SSet.prodStdSimplex₁.ι_snd i

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalCell_fst (n : ℕ) (i : Fin (n + 1)) :
    canonicalCell.{u} n i ≫
        CartesianMonoidalCategory.fst
          (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I =
      SimplexCategory.toTop.map (SimplexCategory.σ i) := by
  unfold canonicalCell
  simp only [Category.assoc, tensorProdIso_inv_fst, Limits.prod.map_fst]
  rw [Limits.prodComparison_fst_assoc]
  have hMapped := congrArg SSet.toTop.{u}.map (ssetCell_fst.{u} n i)
  simp only [Functor.map_comp] at hMapped
  have hMappedAssoc := congrArg
    (· ≫ SSet.toTopSimplex.hom.app ⦋n⦌) hMapped
  calc
    _ = SSet.toTopSimplex.inv.app ⦋n + 1⦌ ≫
        ((SSet.toTop.map (SSet.prodStdSimplex₁.ι i) ≫
          SSet.toTop.map
            ((CartesianMonoidalCategory.tensorLeftIsoProd
              (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u})) ≫
          SSet.toTop.map (ssetProductBridge n).hom ≫
          SSet.toTop.map Limits.prod.fst) ≫
            SSet.toTopSimplex.hom.app ⦋n⦌) := by
              simp only [Category.assoc]
    _ = SSet.toTopSimplex.inv.app ⦋n + 1⦌ ≫
        (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.σ i)) ≫
          SSet.toTopSimplex.hom.app ⦋n⦌) := by rw [hMappedAssoc]
    _ = SimplexCategory.toTop.map (SimplexCategory.σ i) := by
      have hnat :
          SimplexCategory.toTop.{u}.map (SimplexCategory.σ i) ≫
              SSet.toTopSimplex.inv.app ⦋n⦌ =
            SSet.toTopSimplex.inv.app ⦋n + 1⦌ ≫
              SSet.toTop.map
                (SSet.stdSimplex.map (SimplexCategory.σ i)) :=
        SSet.toTopSimplex.inv.naturality (SimplexCategory.σ i)
      have hnatAssoc := congrArg
        (· ≫ SSet.toTopSimplex.hom.app ⦋n⦌) hnat
      rw [← Category.assoc]
      rw [← hnatAssoc]
      simp

private theorem affineCell_fst (n : ℕ) (i : Fin (n + 1)) :
    affineCell.{u} n i ≫
        CartesianMonoidalCategory.fst
          (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I =
      SimplexCategory.toTop.map (SimplexCategory.σ i) := by
  apply TopCat.ext
  intro s
  rfl

private noncomputable def affineIntervalMap (n : ℕ) (i : Fin (n + 1)) :
    SimplexCategory.toTop.{u}.obj ⦋n + 1⦌ ⟶ TopCat.I.{u} :=
  TopCat.ofHom
    { toFun := fun s => TopCat.stdSimplexHomeomorphI
        (Convexity.StdSimplex.map
          (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s.down)
      continuous_toFun := by fun_prop }

private theorem affineCell_snd (n : ℕ) (i : Fin (n + 1)) :
    affineCell.{u} n i ≫
        CartesianMonoidalCategory.snd
          (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I =
      affineIntervalMap n i := by
  apply TopCat.ext
  intro s
  rfl

private theorem realizedIntervalMap_eq_affine (n : ℕ) (i : Fin (n + 1)) :
    SSet.toTopSimplex.inv.app ⦋n + 1⦌ ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm
          (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc)) ≫
        SSet.stdSimplex.toTopObjIsoI.hom =
      affineIntervalMap n i := by
  let h : (⦋n + 1⦌ : SimplexCategory) ⟶ ⦋1⦌ :=
    SSet.stdSimplex.objEquiv
      (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc)
  have hYoneda : SSet.yonedaEquiv.symm
      (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) =
      SSet.stdSimplex.map h := by
    apply SSet.yonedaEquiv.injective
    simp [SSet.yonedaEquiv_map, h]
  rw [hYoneda]
  apply TopCat.ext
  intro s
  change TopCat.stdSimplexHomeomorphI
      (SimplexCategory.toTopHomeo ⦋1⦌
        (SSet.toTop.map (SSet.stdSimplex.map h)
          (SSet.toTopSimplex.inv.app ⦋n + 1⦌ s))) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  have hs : SimplexCategory.toTopHomeo ⦋n + 1⦌
      (SSet.toTopSimplex.inv.app ⦋n + 1⦌ s) = s.down := by
    change ULift.down
      ((SSet.toTopSimplex.app ⦋n + 1⦌).hom
        ((SSet.toTopSimplex.app ⦋n + 1⦌).inv s)) = s.down
    exact congrArg ULift.down
      (TopCat.inv_hom_id_apply (SSet.toTopSimplex.app ⦋n + 1⦌) s)
  rw [hs]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalCell_snd (n : ℕ) (i : Fin (n + 1)) :
    canonicalCell.{u} n i ≫
        CartesianMonoidalCategory.snd
          (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I =
      affineIntervalMap n i := by
  unfold canonicalCell
  simp only [Category.assoc, tensorProdIso_inv_snd, Limits.prod.map_snd]
  rw [Limits.prodComparison_snd_assoc]
  have hMapped := congrArg SSet.toTop.{u}.map (ssetCell_snd.{u} n i)
  simp only [Functor.map_comp] at hMapped
  have hMappedAssoc := congrArg
    (· ≫ SSet.stdSimplex.toTopObjIsoI.hom) hMapped
  calc
    _ = SSet.toTopSimplex.inv.app ⦋n + 1⦌ ≫
        ((SSet.toTop.map (SSet.prodStdSimplex₁.ι i) ≫
          SSet.toTop.map
            ((CartesianMonoidalCategory.tensorLeftIsoProd
              (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u})) ≫
          SSet.toTop.map (ssetProductBridge n).hom ≫
          SSet.toTop.map Limits.prod.snd) ≫
            SSet.stdSimplex.toTopObjIsoI.hom) := by
              simp only [Category.assoc]
    _ = SSet.toTopSimplex.inv.app ⦋n + 1⦌ ≫
        (SSet.toTop.map (SSet.yonedaEquiv.symm
          (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc)) ≫
            SSet.stdSimplex.toTopObjIsoI.hom) := by rw [hMappedAssoc]
    _ = affineIntervalMap n i := realizedIntervalMap_eq_affine n i

private theorem canonicalCell_eq_affineCell (n : ℕ) (i : Fin (n + 1)) :
    canonicalCell.{u} n i = affineCell.{u} n i := by
  apply (cancel_mono (tensorProdIso.{u} n).hom).mp
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, tensorProdIso_hom_fst]
    rw [canonicalCell_fst, affineCell_fst]
  · simp only [Category.assoc, tensorProdIso_hom_snd]
    rw [canonicalCell_snd, affineCell_snd]



end TopCat.IntervalPrismConjugation
namespace TopCat.IntervalPrismAgreeBothVanish

private noncomputable def shuffleOfMaxDim {n m : ℕ}
    (y : ((Δ[n] : SSet.{u}) ⊗ (Δ[m] : SSet.{u})) _⦋n + m⦌)
    (hy : y ∈ (((Δ[n] : SSet.{u}) ⊗ (Δ[m] : SSet.{u})).nonDegenerate (n + m))) :
    ProdSimplexShuffle n m := by
  have hstrict : StrictMono (SSet.prodStdSimplex.objEquiv y) :=
    (SSet.prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv y).mp hy
  have hmax : SSet.prodStdSimplex.orderHomOfSimplex y rfl = OrderHom.id :=
    (SSet.prodStdSimplex.nonDegenerate_max_dim_iff y rfl).mp hy
  have hsum : ∀ k : Fin (n + m + 1),
      (SSet.prodStdSimplex.objEquiv y k).1.val +
        (SSet.prodStdSimplex.objEquiv y k).2.val = k.val := by
    intro k
    have hval : (SSet.prodStdSimplex.orderHomOfSimplex y rfl k).val = k.val := by
      rw [hmax]
      rfl
    have hCoe : SSet.prodStdSimplex.orderHomOfSimplex y rfl k =
        ⟨(y.1 k : ℕ) + y.2 k, by lia⟩ := by
      simp [SSet.prodStdSimplex.orderHomOfSimplex_coe]
    have hFst : (SSet.prodStdSimplex.objEquiv y k).1 = y.1 k := rfl
    have hSnd : (SSet.prodStdSimplex.objEquiv y k).2 = y.2 k := rfl
    rw [hFst, hSnd]
    rw [hCoe] at hval
    simpa using hval
  refine
    { projA := fun k => (SSet.prodStdSimplex.objEquiv y k).1
      projB := fun k => (SSet.prodStdSimplex.objEquiv y k).2
      monoA := fun _ _ h => (Prod.le_def.mp (hstrict.monotone h)).1
      monoB := fun _ _ h => (Prod.le_def.mp (hstrict.monotone h)).2
      firstA := ?_
      lastA := ?_
      firstB := ?_
      lastB := ?_
      step := ?_ }
  · apply Fin.ext
    have h0 := hsum 0
    simp only [Fin.val_zero] at h0 ⊢
    omega
  · apply Fin.ext
    have hL := hsum (Fin.last (n + m))
    have ha := (SSet.prodStdSimplex.objEquiv y (Fin.last (n + m))).1.isLt
    have hb := (SSet.prodStdSimplex.objEquiv y (Fin.last (n + m))).2.isLt
    simp only [Fin.val_last] at hL ⊢
    omega
  · apply Fin.ext
    have h0 := hsum 0
    simp only [Fin.val_zero] at h0 ⊢
    omega
  · apply Fin.ext
    have hL := hsum (Fin.last (n + m))
    have ha := (SSet.prodStdSimplex.objEquiv y (Fin.last (n + m))).1.isLt
    have hb := (SSet.prodStdSimplex.objEquiv y (Fin.last (n + m))).2.isLt
    simp only [Fin.val_last] at hL ⊢
    omega
  · intro q
    have hleA : (SSet.prodStdSimplex.objEquiv y q.castSucc).1.val ≤
        (SSet.prodStdSimplex.objEquiv y q.succ).1.val :=
      Fin.le_def.mp (Prod.le_def.mp (hstrict.monotone q.castSucc_le_succ)).1
    have hleB : (SSet.prodStdSimplex.objEquiv y q.castSucc).2.val ≤
        (SSet.prodStdSimplex.objEquiv y q.succ).2.val :=
      Fin.le_def.mp (Prod.le_def.mp (hstrict.monotone q.castSucc_le_succ)).2
    have hs1 := hsum q.castSucc
    have hs2 := hsum q.succ
    change (_ = _ + 1 ∧ _ = _) ∨ (_ = _ ∧ _ = _ + 1)
    simp only [Fin.val_succ, Fin.val_castSucc] at hs1 hs2
    omega

private noncomputable def intervalShuffle (n : ℕ) (i : Fin (n + 1)) :
    ProdSimplexShuffle n 1 :=
  shuffleOfMaxDim (SSet.prodStdSimplex₁.nonDegenerateEquiv.{u} i).val
    (SSet.prodStdSimplex₁.nonDegenerateEquiv i).prop

@[simp]
private theorem intervalShuffle_projA (n : ℕ) (i : Fin (n + 1))
    (r : Fin (n + 2)) :
    (intervalShuffle n i).projA r = SimplexCategory.σ i r :=
  rfl

@[simp]
private theorem intervalShuffle_projB (n : ℕ) (i : Fin (n + 1))
    (r : Fin (n + 2)) :
    (intervalShuffle n i).projB r =
      SSet.stdSimplex.objMk₁.{u} i.succ.castSucc r :=
  rfl

private theorem stallA {n : ℕ} {S T : ProdSimplexShuffle n 1}
    (s t : Convexity.StdSimplex ℝ (Fin (n + 2))) (r : Fin (n + 2))
    (h : shuffleCell S s = shuffleCell T t)
    (hlt : (S.projA r).val < (T.projA r).val) :
    s.weights r = 0 := by
  have hsumS := shuffleLevelSum_public S r
  have hsumT := shuffleLevelSum_public T r
  have hBlt : (T.projB r).val < (S.projB r).val := by omega
  have hTmem : ((shuffleCell S s).1, (shuffleCell S s).2) ∈
      Set.range (shuffleCell T) := ⟨t, h.symm.trans rfl⟩
  have hoverlap := shuffleCell_mem_range_imp_cumAB T hTmem r
  rw [shuffleCumBefore_eq_preimage S s _,
    shuffleSndCumThrough_eq_preimage S s _] at hoverlap
  have hsum_le :
      ∑ x ∈ Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projA x).val < (T.projA r).val),
        s.weights x ≤
      ∑ x ∈ Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projB x).val ≤ (T.projB r).val),
        s.weights x := hoverlap
  have hRsub :
      Finset.univ.filter
          (fun x : Fin (n + 2) => (S.projB x).val ≤ (T.projB r).val) ⊆
        Finset.univ.filter
          (fun x : Fin (n + 2) => (S.projA x).val < (T.projA r).val) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases hxr : x.val < r.val
    · have hle : (S.projA x).val ≤ (S.projA r).val :=
        Fin.le_def.mp (S.monoA (Fin.le_def.mpr hxr.le))
      omega
    · by_cases heq : x.val = r.val
      · obtain rfl : x = r := Fin.ext heq
        exact hlt
      · have hrx : r.val < x.val := by omega
        have hle : (S.projB r).val ≤ (S.projB x).val :=
          Fin.le_def.mp (S.monoB (Fin.le_def.mpr hrx.le))
        omega
  have hrL : r ∈ Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projA x).val < (T.projA r).val) := by
    simpa using hlt
  have hrNotR : r ∉ Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projB x).val ≤ (T.projB r).val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact hBlt
  have hrMem : r ∈ (Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projA x).val < (T.projA r).val) \
      Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projB x).val ≤ (T.projB r).val)) :=
    Finset.mem_sdiff.mpr ⟨hrL, hrNotR⟩
  have hsplit := Finset.sum_sdiff hRsub (f := fun x => s.weights x)
  have hnonneg : 0 ≤ ∑ x ∈ (Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projA x).val < (T.projA r).val) \
      Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projB x).val ≤ (T.projB r).val)),
      s.weights x :=
    Finset.sum_nonneg fun x _ => s.weights_nonneg x
  have hsingle : s.weights r ≤ ∑ x ∈ (Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projA x).val < (T.projA r).val) \
      Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projB x).val ≤ (T.projB r).val)),
      s.weights x :=
    Finset.single_le_sum (fun x _ => s.weights_nonneg x) hrMem
  have hrNonneg : 0 ≤ s.weights r := s.weights_nonneg r
  linarith

private theorem stallB {n : ℕ} {S T : ProdSimplexShuffle n 1}
    (s t : Convexity.StdSimplex ℝ (Fin (n + 2))) (r : Fin (n + 2))
    (h : shuffleCell S s = shuffleCell T t)
    (hlt : (T.projA r).val < (S.projA r).val) :
    t.weights r = 0 :=
  stallA t s r h.symm hlt

private theorem stallProjB {n : ℕ} {S T : ProdSimplexShuffle n 1}
    (s t : Convexity.StdSimplex ℝ (Fin (n + 2))) (r : Fin (n + 2))
    (h : shuffleCell S s = shuffleCell T t)
    (hlt : (S.projB r).val < (T.projB r).val) :
    s.weights r = 0 := by
  have hsumS := shuffleLevelSum_public S r
  have hsumT := shuffleLevelSum_public T r
  have hAlt : (T.projA r).val < (S.projA r).val := by omega
  have hTmem : ((shuffleCell S s).1, (shuffleCell S s).2) ∈
      Set.range (shuffleCell T) := ⟨t, h.symm.trans rfl⟩
  have hoverlap := shuffleCell_mem_range_imp_cumBA T hTmem r
  rw [shuffleSndCumBefore_eq_preimage S s _,
    shuffleCumThrough_eq_preimage S s _] at hoverlap
  have hsum_le :
      ∑ x ∈ Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projB x).val < (T.projB r).val),
        s.weights x ≤
      ∑ x ∈ Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projA x).val ≤ (T.projA r).val),
        s.weights x := hoverlap
  have hRsub :
      Finset.univ.filter
          (fun x : Fin (n + 2) => (S.projA x).val ≤ (T.projA r).val) ⊆
        Finset.univ.filter
          (fun x : Fin (n + 2) => (S.projB x).val < (T.projB r).val) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases hxr : x.val < r.val
    · have hle : (S.projB x).val ≤ (S.projB r).val :=
        Fin.le_def.mp (S.monoB (Fin.le_def.mpr hxr.le))
      omega
    · by_cases heq : x.val = r.val
      · obtain rfl : x = r := Fin.ext heq
        exact hlt
      · have hrx : r.val < x.val := by omega
        have hle : (S.projA r).val ≤ (S.projA x).val :=
          Fin.le_def.mp (S.monoA (Fin.le_def.mpr hrx.le))
        omega
  have hrL : r ∈ Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projB x).val < (T.projB r).val) := by
    simpa using hlt
  have hrNotR : r ∉ Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projA x).val ≤ (T.projA r).val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact hAlt
  have hrMem : r ∈ (Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projB x).val < (T.projB r).val) \
      Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projA x).val ≤ (T.projA r).val)) :=
    Finset.mem_sdiff.mpr ⟨hrL, hrNotR⟩
  have hsplit := Finset.sum_sdiff hRsub (f := fun x => s.weights x)
  have hnonneg : 0 ≤ ∑ x ∈ (Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projB x).val < (T.projB r).val) \
      Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projA x).val ≤ (T.projA r).val)),
      s.weights x :=
    Finset.sum_nonneg fun x _ => s.weights_nonneg x
  have hsingle : s.weights r ≤ ∑ x ∈ (Finset.univ.filter
      (fun x : Fin (n + 2) => (S.projB x).val < (T.projB r).val) \
      Finset.univ.filter
        (fun x : Fin (n + 2) => (S.projA x).val ≤ (T.projA r).val)),
      s.weights x :=
    Finset.single_le_sum (fun x _ => s.weights_nonneg x) hrMem
  have hrNonneg : 0 ≤ s.weights r := s.weights_nonneg r
  linarith

private theorem bothVanish {n : ℕ} {S T : ProdSimplexShuffle n 1}
    (s t : Convexity.StdSimplex ℝ (Fin (n + 2))) (r : Fin (n + 2))
    (h : shuffleCell S s = shuffleCell T t)
    (hne : (S.projA r).val ≠ (T.projA r).val) :
    s.weights r = 0 ∧ t.weights r = 0 := by
  have hsumS := shuffleLevelSum_public S r
  have hsumT := shuffleLevelSum_public T r
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨stallA s t r h hlt, ?_⟩
    have hB : (T.projB r).val < (S.projB r).val := by omega
    exact stallProjB t s r h.symm hB
  · refine ⟨?_, stallB s t r h hgt⟩
    have hB : (S.projB r).val < (T.projB r).val := by omega
    exact stallProjB s t r h hB

private theorem intervalAgreeBothVanish (n : ℕ) (i j : Fin (n + 1))
    (s t : Convexity.StdSimplex ℝ (Fin (n + 2))) (r : Fin (n + 2))
    (h :
      (Convexity.StdSimplex.map (SimplexCategory.σ i) s,
        Convexity.StdSimplex.map
          (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s) =
      (Convexity.StdSimplex.map (SimplexCategory.σ j) t,
        Convexity.StdSimplex.map
          (SSet.stdSimplex.objMk₁.{u} j.succ.castSucc) t))
    (hne : SimplexCategory.σ i r ≠ SimplexCategory.σ j r) :
    s.weights r = 0 ∧ t.weights r = 0 := by
  let S := intervalShuffle.{u} n i
  let T := intervalShuffle.{u} n j
  have hSA : S.projA = SimplexCategory.σ i := by
    funext x
    rfl
  have hTA : T.projA = SimplexCategory.σ j := by
    funext x
    rfl
  have hSB : S.projB = SSet.stdSimplex.objMk₁.{u} i.succ.castSucc := by
    funext x
    rfl
  have hTB : T.projB = SSet.stdSimplex.objMk₁.{u} j.succ.castSucc := by
    funext x
    rfl
  have hCell : shuffleCell S s = shuffleCell T t := by
    simp only [shuffleCell]
    rw [hSA, hTA, hSB, hTB]
    exact h
  have hneVal : (S.projA r).val ≠ (T.projA r).val := by
    intro heq
    apply hne
    apply Fin.ext
    simpa [S, T] using heq
  exact bothVanish s t r hCell hneVal





end TopCat.IntervalPrismAgreeBothVanish

namespace TopCat.IntervalPrismCommonFace

open TopCat.IntervalPrismAgreeBothVanish


private structure CommonFaceWitness (n : ℕ) (i j : Fin (n + 1))
    (s t : Convexity.StdSimplex ℝ (Fin (n + 2))) where
  k : ℕ
  a : (⦋k⦌ : SimplexCategory) ⟶ ⦋n + 1⦌
  b : (⦋k⦌ : SimplexCategory) ⟶ ⦋n + 1⦌
  comm :
    (SSet.stdSimplex.map a ≫ SSet.prodStdSimplex₁.ι i :
      (Δ[k] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[1]) =
    SSet.stdSimplex.map b ≫ SSet.prodStdSimplex₁.ι j
  w : Convexity.StdSimplex ℝ (Fin (k + 1))
  left : Convexity.StdSimplex.map a w = s
  right : Convexity.StdSimplex.map b w = t

private def intervalHomB {n : ℕ} (i : Fin (n + 1)) :
    (⦋n + 1⦌ : SimplexCategory) ⟶ ⦋1⦌ :=
  SSet.stdSimplex.objEquiv
    (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc)

private theorem intervalCell_snd_as_map (n : ℕ) (i : Fin (n + 1)) :
    SSet.prodStdSimplex₁.ι i ≫
        CartesianMonoidalCategory.snd (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) =
      SSet.stdSimplex.map (intervalHomB.{u} i) := by
  rw [SSet.prodStdSimplex₁.ι_snd]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_map]
  rfl

private theorem intervalCommonFaceWitness (n : ℕ) (i j : Fin (n + 1))
    (s t : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (h :
      (Convexity.StdSimplex.map (SimplexCategory.σ i) s,
        Convexity.StdSimplex.map
          (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s) =
      (Convexity.StdSimplex.map (SimplexCategory.σ j) t,
        Convexity.StdSimplex.map
          (SSet.stdSimplex.objMk₁.{u} j.succ.castSucc) t)) :
    Nonempty (CommonFaceWitness.{u} n i j s t) := by
  let S := intervalShuffle.{u} n i
  let T := intervalShuffle.{u} n j
  have hSA : S.projA = SimplexCategory.σ i := by
    funext x
    rfl
  have hTA : T.projA = SimplexCategory.σ j := by
    funext x
    rfl
  have hSB : S.projB = SSet.stdSimplex.objMk₁.{u} i.succ.castSucc := by
    funext x
    rfl
  have hTB : T.projB = SSet.stdSimplex.objMk₁.{u} j.succ.castSucc := by
    funext x
    rfl
  have hCell : shuffleCell S s = shuffleCell T t := by
    simp only [shuffleCell]
    rw [hSA, hTA, hSB, hTB]
    exact h
  let E : Finset (Fin (n + 2)) :=
    Finset.univ.filter (fun r => S.projA r = T.projA r)
  have hvan : ∀ r : Fin (n + 2),
      s.weights r ≠ 0 → S.projA r = T.projA r := by
    intro r hr
    by_contra hne
    have hneSigma : SimplexCategory.σ i r ≠ SimplexCategory.σ j r := by
      intro heq
      apply hne
      simpa only [hSA, hTA] using heq
    exact hr (intervalAgreeBothVanish.{u} n i j s t r h hneSigma).1
  have hends : (0 : Fin (n + 2)) ∈ E ∧ Fin.last (n + 1) ∈ E := by
    constructor
    · simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.ext (by rw [shufA_zero, shufA_zero])
    · simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.ext (by rw [shufA_last, shufA_last])
  have hcard : E.card ≠ 0 := Finset.card_ne_zero.mpr ⟨0, hends.1⟩
  obtain ⟨k, hk⟩ : ∃ k, E.card = k + 1 := by
    cases hE : E.card with
    | zero => exact absurd hE hcard
    | succ k => exact ⟨k, rfl⟩
  let e : Fin (k + 1) ↪o Fin (n + 2) := E.orderEmbOfFin hk
  let a : (⦋k⦌ : SimplexCategory) ⟶ ⦋n + 1⦌ :=
    SimplexCategory.mkHom e.toOrderHom
  let b : (⦋k⦌ : SimplexCategory) ⟶ ⦋n + 1⦌ :=
    SimplexCategory.mkHom e.toOrderHom
  have hmemA : ∀ q : Fin (k + 1), S.projA (e q) = T.projA (e q) := by
    intro q
    have hq := Finset.orderEmbOfFin_mem E hk q
    simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hq
  have hmemB : ∀ q : Fin (k + 1), S.projB (e q) = T.projB (e q) := by
    intro q
    have hA := congrArg Fin.val (hmemA q)
    have hsumS := shuffleLevelSum_public S (e q)
    have hsumT := shuffleLevelSum_public T (e q)
    apply Fin.ext
    omega
  have keyA : a ≫ SimplexCategory.σ i =
      b ≫ SimplexCategory.σ j := by
    apply SimplexCategory.Hom.ext
    ext q
    simp only [a, b, SimplexCategory.comp_toOrderHom]
    exact congrArg Fin.val (hmemA q)
  have keyB : a ≫ intervalHomB.{u} i =
      b ≫ intervalHomB.{u} j := by
    apply SimplexCategory.Hom.ext
    ext q
    simp only [a, b, SimplexCategory.comp_toOrderHom]
    change (S.projB (e q)).val = (T.projB (e q)).val
    exact congrArg Fin.val (hmemB q)
  have hcomm :
      (SSet.stdSimplex.map a ≫ SSet.prodStdSimplex₁.ι i :
        (Δ[k] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[1]) =
      SSet.stdSimplex.map b ≫ SSet.prodStdSimplex₁.ι j := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, SSet.prodStdSimplex₁.ι_fst]
      change SSet.stdSimplex.map a ≫
          SSet.stdSimplex.map (SimplexCategory.σ i) =
        SSet.stdSimplex.map b ≫
          SSet.stdSimplex.map (SimplexCategory.σ j)
      rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp, keyA]
    · simp only [Category.assoc, intervalCell_snd_as_map,
        ← SSet.stdSimplex.map_comp]
      rw [keyB]
  have hrange : Set.range ⇑e = ↑E := by
    change Set.range ⇑(E.orderEmbOfFin hk) = ↑E
    rw [Finset.range_orderEmbOfFin]
  have hsRange : s ∈ Set.range (Convexity.StdSimplex.map ⇑e) := by
    rw [Convexity.StdSimplex.mem_range_map_iff]
    intro r hr
    rw [hrange] at hr
    have hrNot : r ∉ E := fun hm => hr (Finset.mem_coe.mpr hm)
    have hne : S.projA r ≠ T.projA r :=
      fun heq => hrNot (Finset.mem_filter.mpr ⟨Finset.mem_univ r, heq⟩)
    by_contra hnz
    have hnz' : s.weights r ≠ 0 := by simpa using hnz
    exact hne (hvan r hnz')
  obtain ⟨w, hw⟩ := hsRange
  have hleft : Convexity.StdSimplex.map a w = s := by
    change Convexity.StdSimplex.map ⇑e w = s
    exact hw
  have hcommon : shuffleCell S (Convexity.StdSimplex.map ⇑e w) =
      shuffleCell T (Convexity.StdSimplex.map ⇑e w) := by
    apply Prod.ext
    · simp only [shuffleCell_fst, ← Convexity.StdSimplex.map_comp]
      congr 1
      funext q
      exact hmemA q
    · simp only [shuffleCell_snd, ← Convexity.StdSimplex.map_comp]
      congr 1
      funext q
      exact hmemB q
  have hT : shuffleCell T (Convexity.StdSimplex.map ⇑e w) =
      shuffleCell T t :=
    hcommon.symm.trans ((congrArg (shuffleCell S) hleft).trans hCell)
  have hright0 : Convexity.StdSimplex.map ⇑e w = t :=
    shuffleCell_injective T hT
  have hright : Convexity.StdSimplex.map b w = t := by
    change Convexity.StdSimplex.map ⇑e w = t
    exact hright0
  exact ⟨⟨k, a, b, hcomm, w, hleft, hright⟩⟩

private def CommonFaceStatement : Prop :=
  ∀ (n : ℕ) (i j : Fin (n + 1))
    (s t : Convexity.StdSimplex ℝ (Fin (n + 2))),
    (Convexity.StdSimplex.map (SimplexCategory.σ i) s,
      Convexity.StdSimplex.map
        (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s) =
    (Convexity.StdSimplex.map (SimplexCategory.σ j) t,
      Convexity.StdSimplex.map
        (SSet.stdSimplex.objMk₁.{u} j.succ.castSucc) t) →
    Nonempty (CommonFaceWitness.{u} n i j s t)

private theorem commonFaceStatement : CommonFaceStatement.{u} :=
  intervalCommonFaceWitness




end TopCat.IntervalPrismCommonFace
namespace TopCat.IntervalPrismCommonFace

open TopCat.IntervalPrismAgreeBothVanish

private noncomputable def descentShuffleHomA {n m : ℕ}
    (S : ProdSimplexShuffle n m) :
    (SimplexCategory.mk (n + m)) ⟶ SimplexCategory.mk n :=
  SimplexCategory.Hom.mk ⟨S.projA, S.monoA⟩

private noncomputable def descentShuffleHomB {n m : ℕ}
    (S : ProdSimplexShuffle n m) :
    (SimplexCategory.mk (n + m)) ⟶ SimplexCategory.mk m :=
  SimplexCategory.Hom.mk ⟨S.projB, S.monoB⟩

private theorem descentShuffle_ext {n m : ℕ}
    {S T : ProdSimplexShuffle n m}
    (hA : S.projA = T.projA) (hB : S.projB = T.projB) : S = T := by
  cases S
  cases T
  simp_all

private theorem exists_eq_intervalShuffle (n : ℕ)
    (S : ProdSimplexShuffle n 1) :
    ∃ i : Fin (n + 1), S = intervalShuffle.{u} n i := by
  let y : (((Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj
      (op (SimplexCategory.mk (n + 1)))) :=
    (SSet.stdSimplex.objEquiv.symm (descentShuffleHomA S),
      SSet.stdSimplex.objEquiv.symm (descentShuffleHomB S))
  have hyStrict : StrictMono (SSet.prodStdSimplex.objEquiv y) := by
    intro a b hab
    have hleA : S.projA a ≤ S.projA b := S.monoA hab.le
    have hleB : S.projB a ≤ S.projB b := S.monoB hab.le
    apply lt_of_le_of_ne (Prod.le_def.mpr ⟨hleA, hleB⟩)
    intro heq
    have hA := congrArg (fun p => p.1.val) heq
    have hB := congrArg (fun p => p.2.val) heq
    have hsumA := shuffleLevelSum_public S a
    have hsumB := shuffleLevelSum_public S b
    have habv : a.val < b.val := Fin.lt_def.mp hab
    change (S.projA a).val = (S.projA b).val at hA
    change (S.projB a).val = (S.projB b).val at hB
    omega
  have hy : y ∈
      (((Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).nonDegenerate (n + 1)) :=
    (SSet.prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv y).mpr hyStrict
  let z : {x // x ∈
      (((Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).nonDegenerate (n + 1))} :=
    ⟨y, hy⟩
  let i : Fin (n + 1) :=
    (SSet.prodStdSimplex₁.nonDegenerateEquiv.{u}).symm z
  refine ⟨i, ?_⟩
  have hi : SSet.prodStdSimplex₁.nonDegenerateEquiv.{u} i = z :=
    (SSet.prodStdSimplex₁.nonDegenerateEquiv.{u}).apply_symm_apply z
  apply descentShuffle_ext
  · funext k
    change S.projA k =
      (SSet.prodStdSimplex.objEquiv
        (SSet.prodStdSimplex₁.nonDegenerateEquiv.{u} i).val k).1
    rw [congrArg Subtype.val hi]
    rfl
  · funext k
    change S.projB k =
      (SSet.prodStdSimplex.objEquiv
        (SSet.prodStdSimplex₁.nonDegenerateEquiv.{u} i).val k).2
    rw [congrArg Subtype.val hi]
    rfl

private abbrev prismD (n : ℕ) : TopCat.{u} :=
  SimplexCategory.toTop.{u}.obj (SimplexCategory.mk n)

private noncomputable def affinePrismCell (n : ℕ) (i : Fin (n + 1)) :
    prismD.{u} (n + 1) ⟶ prismD n ⊗ TopCat.I.{u} :=
  TopCat.ofHom
    { toFun := fun s =>
        (ULift.up (Convexity.StdSimplex.map
            (SimplexCategory.σ i) s.down),
          TopCat.stdSimplexHomeomorphI
            (Convexity.StdSimplex.map
              (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s.down))
      continuous_toFun := by fun_prop }

/-- The canonical interval-prism cell obtained by realizing the corresponding
simplex-product inclusion. -/
noncomputable def _root_.TopCat.IntervalPrism.cell
    (n : ℕ) (i : Fin (n + 1)) :
    SimplexCategory.toTop.{u}.obj ⦋n + 1⦌ ⟶
      SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I.{u} :=
  SSet.toTopSimplex.inv.app ⦋n + 1⦌ ≫
    SSet.toTop.map (SSet.prodStdSimplex₁.ι i) ≫
    SSet.toTop.map
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[n] : SSet.{u})).hom.app (Δ[1] : SSet.{u})) ≫
    SSet.toTop.map (𝟙 _) ≫
    Limits.prodComparison SSet.toTop (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
    Limits.prod.map (SSet.toTopSimplex.hom.app ⦋n⦌)
      SSet.stdSimplex.toTopObjIsoI.hom ≫
    (((CartesianMonoidalCategory.tensorLeftIsoProd (C := TopCat.{u})
      (SimplexCategory.toTop.obj ⦋n⦌)).app TopCat.I) ≪≫ Iso.refl _).inv

private theorem cell_eq_affinePrismCell (n : ℕ) (i : Fin (n + 1)) :
    TopCat.IntervalPrism.cell.{u} n i = affinePrismCell.{u} n i := by
  calc
    TopCat.IntervalPrism.cell.{u} n i =
        TopCat.IntervalPrismConjugation.canonicalCell.{u} n i := rfl
    _ = TopCat.IntervalPrismConjugation.affineCell.{u} n i :=
      TopCat.IntervalPrismConjugation.canonicalCell_eq_affineCell n i
    _ = affinePrismCell.{u} n i := rfl

private noncomputable def intervalCover (n : ℕ) :
    (Σ _ : Fin (n + 1), prismD.{u} (n + 1)) →
      (prismD.{u} n : Type u) × (TopCat.I.{u} : Type u) :=
  fun p => affinePrismCell.{u} n p.1 p.2

private theorem continuous_intervalCover (n : ℕ) :
    Continuous (intervalCover.{u} n) := by
  rw [continuous_sigma_iff]
  intro i
  exact (affinePrismCell.{u} n i).hom.continuous

private theorem surjective_intervalCover (n : ℕ) :
    Function.Surjective (intervalCover.{u} n) := by
  intro z
  let x : Convexity.StdSimplex ℝ (Fin (n + 1)) := z.1.down
  let y : Convexity.StdSimplex ℝ (Fin 2) :=
    TopCat.stdSimplexHomeomorphI.{u}.symm z.2
  obtain ⟨⟨S, s⟩, hs⟩ :=
    surjective_shuffleGluingCoverMap n 1 (x, y)
  obtain ⟨i, rfl⟩ := exists_eq_intervalShuffle n S
  refine ⟨⟨i, ULift.up s⟩, ?_⟩
  apply Prod.ext
  · change ULift.up (Convexity.StdSimplex.map
        (SimplexCategory.σ i) s) = z.1
    apply ULift.down_injective
    change Convexity.StdSimplex.map (SimplexCategory.σ i) s = z.1.down
    have hfst := congrArg Prod.fst hs
    have hprojA : (intervalShuffle.{u} n i).projA =
        SimplexCategory.σ i := by
      funext r
      rfl
    change Convexity.StdSimplex.map
      (intervalShuffle.{u} n i).projA s = x at hfst
    rw [hprojA] at hfst
    simpa [x] using hfst
  · change TopCat.stdSimplexHomeomorphI.{u}
        (Convexity.StdSimplex.map
          (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s) = z.2
    have hsnd := congrArg Prod.snd hs
    have hprojB : (intervalShuffle.{u} n i).projB =
        SSet.stdSimplex.objMk₁.{u} i.succ.castSucc := by
      funext r
      rfl
    change Convexity.StdSimplex.map
      (intervalShuffle.{u} n i).projB s = y at hsnd
    rw [hprojB] at hsnd
    calc
      TopCat.stdSimplexHomeomorphI.{u}
          (Convexity.StdSimplex.map
            (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s) =
        TopCat.stdSimplexHomeomorphI.{u} y :=
          congrArg (fun q => TopCat.stdSimplexHomeomorphI.{u} q) hsnd
      _ = z.2 := by
        dsimp only [y]
        exact TopCat.stdSimplexHomeomorphI.{u}.apply_symm_apply z.2

private noncomputable instance compactPrismD (n : ℕ) :
    CompactSpace (prismD.{u} n : Type u) := by
  change CompactSpace (ULift (Convexity.StdSimplex ℝ (Fin (n + 1))))
  infer_instance

private noncomputable instance t2PrismD (n : ℕ) :
    T2Space (prismD.{u} n : Type u) := by
  let _ : T2Space (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).t2Space
  change T2Space (ULift (Convexity.StdSimplex ℝ (Fin (n + 1))))
  infer_instance

private noncomputable instance t2PrismI :
    T2Space (TopCat.I.{u} : Type u) := by
  let _ : T2Space unitInterval := inferInstance
  change T2Space (ULift unitInterval)
  infer_instance

private theorem intervalCover_prod_quotient
    {A : Type u} [TopologicalSpace A] (n : ℕ) :
    IsQuotientMap (Prod.map (id : A → A) (intervalCover.{u} n)) := by
  apply IsQuotientMap.prodMap_right_of_compact_to_t2
    (continuous_intervalCover n) (surjective_intervalCover n)

private noncomputable def sliceSimplex
    {A Z : TopCat.{u}} {n : ℕ}
    (f : A ⊗ prismD.{u} (n + 1) ⟶ Z) (a : A) :
    (TopCat.toSSet.obj Z).obj (op (SimplexCategory.mk (n + 1))) :=
  (Z.toSSetObjEquiv _).symm
    { toFun := fun s => f (a, ULift.up s)
      continuous_toFun := f.hom.continuous.comp
        (continuous_const.prodMk continuous_uliftUp) }

private noncomputable def sliceSSet
    {A Z : TopCat.{u}} {n : ℕ}
    (f : A ⊗ prismD.{u} (n + 1) ⟶ Z) (a : A) :
    (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) : SSet.{u}) ⟶
      TopCat.toSSet.obj Z :=
  SSet.yonedaEquiv.symm (sliceSimplex f a)

private theorem sliceSSet_adjacent
    {A Z : TopCat.{u}} {n : ℕ}
    (phi : ∀ _ : Fin (n + 1), A ⊗ prismD.{u} (n + 1) ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ)
    (a : A) (i : Fin n) :
    SSet.stdSimplex.δ i.succ.castSucc ≫ sliceSSet (phi i.castSucc) a =
      SSet.stdSimplex.δ i.succ.castSucc ≫ sliceSSet (phi i.succ) a := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp,
    SSet.stdSimplex.yonedaEquiv_δ_comp]
  apply (Z.toSSetObjEquiv _).injective
  ext w
  rw [TopCat.toSSetObjEquiv_δ_apply,
    TopCat.toSSetObjEquiv_δ_apply]
  simp only [sliceSSet, sliceSimplex, Equiv.apply_symm_apply]
  have hp := ConcreteCategory.congr_hom (hphi i) (a, ULift.up w)
  change phi i.castSucc
      (a, ULift.up (Convexity.StdSimplex.map
        i.castSucc.succ.succAbove w)) =
    phi i.succ
      (a, ULift.up (Convexity.StdSimplex.map
        i.castSucc.succ.succAbove w)) at hp
  rw [← Fin.succ_castSucc]
  exact hp

private theorem exists_sSet_desc
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1), A ⊗ prismD.{u} (n + 1) ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ)
    (a : A) :
    ∃ psi : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{u}) ⊗
        (Δ[1] : SSet.{u}) ⟶ TopCat.toSSet.obj Z,
      ∀ i : Fin (n + 1),
        SSet.prodStdSimplex₁.ι i ≫ psi = sliceSSet (phi i) a := by
  apply SSet.prodStdSimplex₁.exists_desc
  exact sliceSSet_adjacent phi hphi a

private theorem phi_eq_of_commonFace
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1), A ⊗ prismD.{u} (n + 1) ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ)
    (c : A) {i j : Fin (n + 1)}
    {s t : Convexity.StdSimplex ℝ (Fin (n + 2))}
    (F : CommonFaceWitness.{u} n i j s t) :
    phi i (c, ULift.up s) = phi j (c, ULift.up t) := by
  obtain ⟨psi, hpsi⟩ := exists_sSet_desc n phi hphi c
  have hmaps : SSet.stdSimplex.map F.a ≫ sliceSSet (phi i) c =
      SSet.stdSimplex.map F.b ≫ sliceSSet (phi j) c := by
    calc
      SSet.stdSimplex.map F.a ≫ sliceSSet (phi i) c =
          SSet.stdSimplex.map F.a ≫
            (SSet.prodStdSimplex₁.ι i ≫ psi) := by rw [hpsi i]
      _ = (SSet.stdSimplex.map F.a ≫
          SSet.prodStdSimplex₁.ι i) ≫ psi := by rw [Category.assoc]
      _ = (SSet.stdSimplex.map F.b ≫
          SSet.prodStdSimplex₁.ι j) ≫ psi := by rw [F.comm]
      _ = SSet.stdSimplex.map F.b ≫
          (SSet.prodStdSimplex₁.ι j ≫ psi) := by rw [Category.assoc]
      _ = SSet.stdSimplex.map F.b ≫ sliceSSet (phi j) c := by rw [hpsi j]
  have hsimp := congrArg SSet.yonedaEquiv hmaps
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at hsimp
  rw [SSet.yonedaEquiv_map, SSet.yonedaEquiv_map] at hsimp
  simp only [sliceSSet] at hsimp
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm,
    SSet.yonedaEquiv_symm_app_objEquiv_symm] at hsimp
  have hpoint := congrArg
    (fun q => (Z.toSSetObjEquiv (op (SimplexCategory.mk F.k))) q F.w) hsimp
  rw [TopCat.toSSetObjEquiv_naturality_apply,
    TopCat.toSSetObjEquiv_naturality_apply] at hpoint
  simp only [sliceSimplex, Equiv.apply_symm_apply] at hpoint
  simpa [F.left, F.right] using hpoint

private noncomputable def pieceMap
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1), A ⊗ prismD.{u} (n + 1) ⟶ Z) :
    C(A × (Σ _ : Fin (n + 1), prismD.{u} (n + 1)), Z) where
  toFun p := phi p.2.1 (p.1, p.2.2)
  continuous_toFun := by
    let e : A × (Σ _ : Fin (n + 1), prismD.{u} (n + 1)) ≃ₜ
        Σ _ : Fin (n + 1), prismD.{u} (n + 1) × A :=
      (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
    have hg : Continuous (fun p :
        Σ _ : Fin (n + 1), prismD.{u} (n + 1) × A =>
          phi p.1 (p.2.2, p.2.1)) := by
      rw [continuous_sigma_iff]
      intro i
      exact (phi i).hom.continuous.comp (continuous_snd.prodMk continuous_fst)
    exact hg.comp e.continuous

private noncomputable def coefficientCover (A : TopCat.{u}) (n : ℕ) :
    C(A × (Σ _ : Fin (n + 1), prismD.{u} (n + 1)),
      A × (prismD.{u} n × TopCat.I.{u})) where
  toFun := Prod.map id (intervalCover.{u} n)
  continuous_toFun := continuous_id.prodMap (continuous_intervalCover n)

private theorem coefficientCover_quotient (A : TopCat.{u}) (n : ℕ) :
    IsQuotientMap (coefficientCover A n) :=
  intervalCover_prod_quotient n

private theorem pieceMap_factors
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1), A ⊗ prismD.{u} (n + 1) ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ) :
    Function.FactorsThrough (pieceMap n phi) (coefficientCover A n) := by
  rintro ⟨c, i, s⟩ ⟨d, j, t⟩ heq
  change (c, affinePrismCell.{u} n i s) =
      (d, affinePrismCell.{u} n j t) at heq
  have hcd : c = d := congrArg Prod.fst heq
  subst d
  have hcell : affinePrismCell.{u} n i s =
      affinePrismCell.{u} n j t := congrArg Prod.snd heq
  have haff :
      (Convexity.StdSimplex.map (SimplexCategory.σ i) s.down,
        Convexity.StdSimplex.map
          (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) s.down) =
      (Convexity.StdSimplex.map (SimplexCategory.σ j) t.down,
        Convexity.StdSimplex.map
          (SSet.stdSimplex.objMk₁.{u} j.succ.castSucc) t.down) := by
    apply Prod.ext
    · apply ULift.up_injective
      exact congrArg Prod.fst hcell
    · apply TopCat.stdSimplexHomeomorphI.{u}.injective
      exact congrArg Prod.snd hcell
  obtain ⟨F⟩ := intervalCommonFaceWitness.{u} n i j s.down t.down haff
  change phi i (c, s) = phi j (c, t)
  exact phi_eq_of_commonFace n phi hphi c F

private noncomputable def descAux
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1), A ⊗ prismD.{u} (n + 1) ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ) :
    A ⊗ (prismD.{u} n ⊗ TopCat.I.{u}) ⟶ Z :=
  TopCat.ofHom ((coefficientCover_quotient A n).lift
    (pieceMap n phi) (pieceMap_factors n phi hphi))

private theorem descAux_cell
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1), A ⊗ prismD.{u} (n + 1) ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ)
    (i : Fin (n + 1)) :
    (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} n i) ≫
        descAux n phi hphi = phi i := by
  rw [cell_eq_affinePrismCell]
  ext x
  have hcomp := (coefficientCover_quotient A n).lift_comp
    (pieceMap n phi) (pieceMap_factors n phi hphi)
  have hp := ContinuousMap.congr_fun hcomp (x.1, ⟨i, x.2⟩)
  exact hp

/-- Descend a compatible family of interval-prism cell maps. -/
noncomputable def _root_.TopCat.IntervalPrism.desc
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1),
      A ⊗ SimplexCategory.toTop.{u}.obj ⦋n + 1⦌ ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ) :
    A ⊗ (SimplexCategory.toTop.{u}.obj ⦋n⦌ ⊗ TopCat.I.{u}) ⟶ Z :=
  Classical.choose (show ∃ d :
      A ⊗ (SimplexCategory.toTop.{u}.obj ⦋n⦌ ⊗ TopCat.I.{u}) ⟶ Z,
      ∀ i : Fin (n + 1),
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} n i) ≫ d = phi i from by
    exact ⟨descAux n phi hphi, descAux_cell n phi hphi⟩)

/-- The descended map restricts to the prescribed map on every prism cell. -/
theorem _root_.TopCat.IntervalPrism.cell_desc
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1),
      A ⊗ SimplexCategory.toTop.{u}.obj ⦋n + 1⦌ ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ)
    (i : Fin (n + 1)) :
    (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} n i) ≫
        TopCat.IntervalPrism.desc n phi hphi = phi i := by
  exact Classical.choose_spec (show ∃ d :
      A ⊗ (SimplexCategory.toTop.{u}.obj ⦋n⦌ ⊗ TopCat.I.{u}) ⟶ Z,
      ∀ i : Fin (n + 1),
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} n i) ≫ d = phi i from by
    exact ⟨descAux n phi hphi, descAux_cell n phi hphi⟩) i





end TopCat.IntervalPrismCommonFace
namespace TopCat.IntervalPrismCommonFace

open TopCat.IntervalPrismAgreeBothVanish

private theorem affine_cell_fst (n : ℕ) (i : Fin (n + 1)) :
    TopCat.IntervalPrism.cell.{u} n i ≫
        CartesianMonoidalCategory.fst (prismD.{u} n) TopCat.I =
      SimplexCategory.toTop.map (SimplexCategory.σ i) := by
  rw [cell_eq_affinePrismCell]
  apply TopCat.ext
  intro s
  rfl

/-- The actual prism cell projects to the degeneracy of its simplex.
This USED public characteristic reuses the unchanged private geometric
proof and has a literal public simplex object, never private prismD. -/
theorem _root_.TopCat.IntervalPrism.cell_fst (n : ℕ) (i : Fin (n + 1)) :
    TopCat.IntervalPrism.cell.{u} n i ≫
        CartesianMonoidalCategory.fst (SimplexCategory.toTop.obj ⦋n⦌)
          TopCat.I.{u} =
      SimplexCategory.toTop.map (SimplexCategory.σ i) :=
  affine_cell_fst n i

private theorem affine_cell_last_snd (n : ℕ) :
    SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ (Fin.last (n + 1))) ≫
        TopCat.IntervalPrism.cell.{u} n (Fin.last n) ≫
        CartesianMonoidalCategory.snd (prismD.{u} n) TopCat.I =
      TopCat.const 0 := by
  rw [cell_eq_affinePrismCell]
  apply TopCat.ext
  intro s
  change TopCat.stdSimplexHomeomorphI.{u}
      (Convexity.StdSimplex.map
        (SSet.stdSimplex.objMk₁.{u} (Fin.last n).succ.castSucc)
        (Convexity.StdSimplex.map
          (SimplexCategory.δ (Fin.last (n + 1))) s.down)) = 0
  rw [← Convexity.StdSimplex.map_comp]
  have hconst :
      (SSet.stdSimplex.objMk₁.{u} (Fin.last n).succ.castSucc :
          Fin (n + 2) → Fin 2) ∘
          (SimplexCategory.δ (Fin.last (n + 1)) :
            Fin (n + 1) → Fin (n + 2)) =
        fun _ => (0 : Fin 2) := by
    funext q
    apply Fin.ext
    have hne :
        (SimplexCategory.δ (Fin.last (n + 1)) :
          Fin (n + 1) → Fin (n + 2)) q ≠ Fin.last (n + 1) := by
      exact Fin.succAbove_ne _ _
    simp [SSet.stdSimplex.objMk₁_apply, hne]
  rw [hconst, Convexity.StdSimplex.map_const,
    TopCat.stdSimplexHomeomorphI_vertex_zero]

private theorem affine_cell_zero_snd (n : ℕ) :
    SimplexCategory.toTop.{u}.map (SimplexCategory.δ 0) ≫
        TopCat.IntervalPrism.cell.{u} n 0 ≫
        CartesianMonoidalCategory.snd (prismD.{u} n) TopCat.I =
      TopCat.const 1 := by
  rw [cell_eq_affinePrismCell]
  apply TopCat.ext
  intro s
  change TopCat.stdSimplexHomeomorphI.{u}
      (Convexity.StdSimplex.map
        (SSet.stdSimplex.objMk₁.{u} (0 : Fin (n + 1)).succ.castSucc)
        (Convexity.StdSimplex.map (SimplexCategory.δ 0) s.down)) = 1
  rw [← Convexity.StdSimplex.map_comp]
  have hconst :
      (SSet.stdSimplex.objMk₁.{u} (0 : Fin (n + 1)).succ.castSucc :
          Fin (n + 2) → Fin 2) ∘
          (SimplexCategory.δ (0 : Fin (n + 2)) :
            Fin (n + 1) → Fin (n + 2)) =
        fun _ => (1 : Fin 2) := by
    funext q
    apply Fin.ext
    have hne :
        (SimplexCategory.δ (0 : Fin (n + 2)) :
          Fin (n + 1) → Fin (n + 2)) q ≠ 0 := by
      simpa only [SimplexCategory.coe_δ] using
        (Fin.succAbove_ne (0 : Fin (n + 2)) q)
    simp [SSet.stdSimplex.objMk₁_apply, hne]
  rw [hconst, Convexity.StdSimplex.map_const,
    TopCat.stdSimplexHomeomorphI_vertex_one]

private theorem cell_delta_last (n : ℕ) :
    SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ (Fin.last (n + 1))) ≫
        TopCat.IntervalPrism.cell.{u} n (Fin.last n) =
      (TopCat.ι₀ : prismD.{u} n ⟶ prismD n ⊗ TopCat.I) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, affine_cell_fst,
      TopCat.ι₀_fst]
    rw [← SimplexCategory.toTop.map_comp]
    rw [show Fin.last (n + 1) = (Fin.last n).succ by rfl,
      SimplexCategory.δ_comp_σ_succ]
    exact (SimplexCategory.toTop.{u}).map_id _
  · simpa only [Category.assoc, TopCat.ι₀_snd] using
      affine_cell_last_snd.{u} n

private theorem cell_delta_zero (n : ℕ) :
    SimplexCategory.toTop.{u}.map (SimplexCategory.δ 0) ≫
        TopCat.IntervalPrism.cell.{u} n 0 =
      (TopCat.ι₁ : prismD.{u} n ⟶ prismD n ⊗ TopCat.I) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, affine_cell_fst,
      TopCat.ι₁_fst]
    rw [← SimplexCategory.toTop.map_comp]
    rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl,
      SimplexCategory.δ_comp_σ_self]
    exact (SimplexCategory.toTop.{u}).map_id _
  · simpa only [Category.assoc, TopCat.ι₁_snd] using
      affine_cell_zero_snd.{u} n

theorem _root_.TopCat.IntervalPrism.zero_desc
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1),
      A ⊗ SimplexCategory.toTop.{u}.obj ⦋n + 1⦌ ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ) :
    (𝟙 A ⊗ₘ (TopCat.ι₀ : SimplexCategory.toTop.{u}.obj ⦋n⦌ ⟶
      SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I)) ≫
        TopCat.IntervalPrism.desc n phi hphi =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ (Fin.last (n + 1)))) ≫
        phi (Fin.last n) := by
  rw [← cell_delta_last.{u} n]
  rw [MonoidalCategory.id_tensor_comp, Category.assoc,
    TopCat.IntervalPrism.cell_desc]

theorem _root_.TopCat.IntervalPrism.one_desc
    {A Z : TopCat.{u}} (n : ℕ)
    (phi : ∀ _ : Fin (n + 1),
      A ⊗ SimplexCategory.toTop.{u}.obj ⦋n + 1⦌ ⟶ Z)
    (hphi : ∀ i : Fin n,
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.castSucc =
        (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ i.castSucc.succ)) ≫ phi i.succ) :
    (𝟙 A ⊗ₘ (TopCat.ι₁ : SimplexCategory.toTop.{u}.obj ⦋n⦌ ⟶
      SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I)) ≫
        TopCat.IntervalPrism.desc n phi hphi =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ 0)) ≫ phi 0 := by
  rw [← cell_delta_zero.{u} n]
  rw [MonoidalCategory.id_tensor_comp, Category.assoc,
    TopCat.IntervalPrism.cell_desc]

/-- Internal extensionality for maps out of a prism with an arbitrary
coefficient space. -/
theorem _root_.TopCat.IntervalPrism.Internal.cell_hom_ext
    {A Z : TopCat.{u}} (n : ℕ)
    {f g : A ⊗ (SimplexCategory.toTop.{u}.obj ⦋n⦌ ⊗ TopCat.I.{u}) ⟶ Z}
    (h : ∀ i : Fin (n + 1),
      (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} n i) ≫ f =
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} n i) ≫ g) :
    f = g := by
  apply TopCat.ext
  intro x
  obtain ⟨y, rfl⟩ := (coefficientCover_quotient A n).surjective x
  rcases y with ⟨a, i, s⟩
  have hi := h i
  rw [cell_eq_affinePrismCell] at hi
  exact ConcreteCategory.congr_hom hi (a, s)




end TopCat.IntervalPrismCommonFace
namespace TopCat.IntervalPrismCellReindex

namespace SSet.prodStdSimplex₁

private theorem ι_σ_whiskerRight_of_le {p : ℕ}
    (i j : Fin (p + 1)) (hij : i ≤ j) :
    SSet.prodStdSimplex₁.ι (p := p + 1) j.succ ≫
        (SSet.stdSimplex.σ i ▷ (Δ[1] : SSet.{u})) =
      SSet.stdSimplex.σ i.castSucc ≫
        SSet.prodStdSimplex₁.ι (p := p) j := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      SSet.prodStdSimplex₁.ι_fst]
    change SSet.stdSimplex.map
        (SimplexCategory.σ j.succ ≫ SimplexCategory.σ i) =
      SSet.stdSimplex.map
        (SimplexCategory.σ i.castSucc ≫ SimplexCategory.σ j)
    rw [SimplexCategory.σ_comp_σ hij]
  · apply SSet.yonedaEquiv.injective
    simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      SSet.prodStdSimplex₁.ι_snd, SSet.stdSimplex.yonedaEquiv_σ_comp]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      SSet.stdSimplex.σ_objMk₁_of_lt _ _ (by simpa)]
    congr 1

private theorem ι_σ_whiskerRight_of_ge {p : ℕ}
    (i j : Fin (p + 1)) (hji : j ≤ i) :
    SSet.prodStdSimplex₁.ι (p := p + 1) j.castSucc ≫
        (SSet.stdSimplex.σ i ▷ (Δ[1] : SSet.{u})) =
      SSet.stdSimplex.σ i.succ ≫
        SSet.prodStdSimplex₁.ι (p := p) j := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      SSet.prodStdSimplex₁.ι_fst]
    change SSet.stdSimplex.map
        (SimplexCategory.σ j.castSucc ≫ SimplexCategory.σ i) =
      SSet.stdSimplex.map
        (SimplexCategory.σ i.succ ≫ SimplexCategory.σ j)
    rw [SimplexCategory.σ_comp_σ hji]
  · apply SSet.yonedaEquiv.injective
    simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      SSet.prodStdSimplex₁.ι_snd, SSet.stdSimplex.yonedaEquiv_σ_comp]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      SSet.stdSimplex.σ_objMk₁_of_le _ _ (by simpa)]
    congr 1

end SSet.prodStdSimplex₁

private noncomputable def ssetProductBridge (p : ℕ) :
    ((Limits.prod.functor.obj (Δ[p] : SSet.{u})).obj (Δ[1] : SSet.{u})) ≅
      ((Δ[p] : SSet.{u}) ⨯ (Δ[1] : SSet.{u})) :=
  Iso.refl _

private noncomputable def topProductBridge (p : ℕ) :
    ((Limits.prod.functor.obj
      (SimplexCategory.toTop.{u}.obj (SimplexCategory.mk p))).obj TopCat.I.{u}) ≅
      (SimplexCategory.toTop.obj (SimplexCategory.mk p) ⨯ TopCat.I) :=
  Iso.refl _

private noncomputable def tensorProdIso (p : ℕ) :
    SimplexCategory.toTop.{u}.obj (SimplexCategory.mk p) ⊗ TopCat.I.{u} ≅
      SimplexCategory.toTop.obj (SimplexCategory.mk p) ⨯ TopCat.I :=
  (CartesianMonoidalCategory.tensorLeftIsoProd (C := TopCat.{u})
    (SimplexCategory.toTop.obj (SimplexCategory.mk p))).app TopCat.I ≪≫
      topProductBridge p

private noncomputable def cell (p : ℕ) (j : Fin (p + 1)) :
    SimplexCategory.toTop.{u}.obj (SimplexCategory.mk (p + 1)) ⟶
      SimplexCategory.toTop.obj (SimplexCategory.mk p) ⊗ TopCat.I.{u} :=
  SSet.toTopSimplex.inv.app (SimplexCategory.mk (p + 1)) ≫
    SSet.toTop.map (SSet.prodStdSimplex₁.ι j) ≫
    SSet.toTop.map
      ((CartesianMonoidalCategory.tensorLeftIsoProd (Δ[p] : SSet.{u})).hom.app
        (Δ[1] : SSet.{u})) ≫
    SSet.toTop.map (ssetProductBridge p).hom ≫
    Limits.prodComparison SSet.toTop (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
    Limits.prod.map (SSet.toTopSimplex.hom.app (SimplexCategory.mk p))
      SSet.stdSimplex.toTopObjIsoI.hom ≫
    (tensorProdIso.{u} p).inv

private theorem tensorProdIso_inv_fst (p : ℕ) :
    (tensorProdIso.{u} p).inv ≫
        CartesianMonoidalCategory.fst
          (SimplexCategory.toTop.obj (SimplexCategory.mk p)) TopCat.I =
      Limits.prod.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (SimplexCategory.toTop.obj (SimplexCategory.mk p)) TopCat.I)
    (Limits.limit.isLimit _) ⟨.left⟩

private theorem tensorProdIso_inv_snd (p : ℕ) :
    (tensorProdIso.{u} p).inv ≫
        CartesianMonoidalCategory.snd
          (SimplexCategory.toTop.obj (SimplexCategory.mk p)) TopCat.I =
      Limits.prod.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (SimplexCategory.toTop.obj (SimplexCategory.mk p)) TopCat.I)
    (Limits.limit.isLimit _) ⟨.right⟩

private theorem ssetTensorBridge_hom_fst (p : ℕ) :
    (CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[p] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      (ssetProductBridge p).hom ≫ Limits.prod.fst =
        CartesianMonoidalCategory.fst (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}) := by
  change ((CartesianMonoidalCategory.tensorLeftIsoProd
      (Δ[p] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫ 𝟙 _) ≫
        Limits.prod.fst = _
  rw [Category.comp_id]
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}))
    (Limits.limit.isLimit _) ⟨.left⟩

private theorem ssetTensorBridge_hom_snd (p : ℕ) :
    (CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[p] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      (ssetProductBridge p).hom ≫ Limits.prod.snd =
        CartesianMonoidalCategory.snd (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}) := by
  change ((CartesianMonoidalCategory.tensorLeftIsoProd
      (Δ[p] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫ 𝟙 _) ≫
        Limits.prod.snd = _
  rw [Category.comp_id]
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct
      (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}))
    (Limits.limit.isLimit _) ⟨.right⟩

private theorem ssetCell_fst (p : ℕ) (j : Fin (p + 1)) :
    SSet.prodStdSimplex₁.ι j ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[p] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      (ssetProductBridge p).hom ≫ Limits.prod.fst =
        SSet.stdSimplex.map (SimplexCategory.σ j) := by
  rw [ssetTensorBridge_hom_fst]
  exact SSet.prodStdSimplex₁.ι_fst j

private theorem ssetCell_snd (p : ℕ) (j : Fin (p + 1)) :
    SSet.prodStdSimplex₁.ι j ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[p] : SSet.{u})).hom.app (Δ[1] : SSet.{u}) ≫
      (ssetProductBridge p).hom ≫ Limits.prod.snd =
        SSet.yonedaEquiv.symm
          (SSet.stdSimplex.objMk₁.{u} j.succ.castSucc) := by
  rw [ssetTensorBridge_hom_snd]
  exact SSet.prodStdSimplex₁.ι_snd j

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem cell_fst (p : ℕ) (j : Fin (p + 1)) :
    cell.{u} p j ≫
        CartesianMonoidalCategory.fst
          (SimplexCategory.toTop.obj (SimplexCategory.mk p)) TopCat.I =
      SimplexCategory.toTop.map (SimplexCategory.σ j) := by
  unfold cell
  simp only [Category.assoc, tensorProdIso_inv_fst, Limits.prod.map_fst]
  rw [Limits.prodComparison_fst_assoc]
  have hMapped := congrArg SSet.toTop.{u}.map (ssetCell_fst.{u} p j)
  simp only [Functor.map_comp] at hMapped
  calc
    _ = SSet.toTopSimplex.inv.app (SimplexCategory.mk (p + 1)) ≫
        (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.σ j)) ≫
          SSet.toTopSimplex.hom.app (SimplexCategory.mk p)) := by
      simpa only [Category.assoc] using congrArg
        (fun z => SSet.toTopSimplex.inv.app (SimplexCategory.mk (p + 1)) ≫
          z ≫ SSet.toTopSimplex.hom.app (SimplexCategory.mk p)) hMapped
    _ = SimplexCategory.toTop.map (SimplexCategory.σ j) := by
      have hnat :=
        SSet.toTopSimplex.{u}.inv.naturality (SimplexCategory.σ j)
      change SimplexCategory.toTop.map (SimplexCategory.σ j) ≫
          SSet.toTopSimplex.inv.app (SimplexCategory.mk p) =
        SSet.toTopSimplex.inv.app (SimplexCategory.mk (p + 1)) ≫
          SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.σ j)) at hnat
      rw [← Category.assoc, ← hnat]
      simp

private noncomputable def intervalSimplex (p : ℕ) (j : Fin (p + 1)) :
    (Δ[p + 1] : SSet.{u}) ⟶ Δ[1] :=
  SSet.yonedaEquiv.symm
    (SSet.stdSimplex.objMk₁.{u} j.succ.castSucc)

private noncomputable def intervalMap (p : ℕ) (j : Fin (p + 1)) :
    SimplexCategory.toTop.{u}.obj (SimplexCategory.mk (p + 1)) ⟶
      TopCat.I.{u} :=
  SSet.toTopSimplex.inv.app (SimplexCategory.mk (p + 1)) ≫
    SSet.toTop.map (intervalSimplex p j) ≫
    SSet.stdSimplex.toTopObjIsoI.hom

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem cell_snd (p : ℕ) (j : Fin (p + 1)) :
    cell.{u} p j ≫
        CartesianMonoidalCategory.snd
          (SimplexCategory.toTop.obj (SimplexCategory.mk p)) TopCat.I =
      intervalMap p j := by
  unfold cell
  simp only [Category.assoc, tensorProdIso_inv_snd, Limits.prod.map_snd]
  rw [Limits.prodComparison_snd_assoc]
  have hMapped := congrArg SSet.toTop.{u}.map (ssetCell_snd.{u} p j)
  simp only [Functor.map_comp] at hMapped
  unfold intervalMap
  unfold intervalSimplex
  simpa only [Category.assoc] using congrArg
    (fun z => SSet.toTopSimplex.inv.app (SimplexCategory.mk (p + 1)) ≫
      z ≫ SSet.stdSimplex.toTopObjIsoI.hom) hMapped

private theorem realizedIntervalMap_naturality
    {m n : SimplexCategory} (α : m ⟶ n)
    (a : SSet.stdSimplex.obj m ⟶ (Δ[1] : SSet.{u}))
    (b : SSet.stdSimplex.obj n ⟶ (Δ[1] : SSet.{u}))
    (h : a = SSet.stdSimplex.map α ≫ b) :
    SSet.toTopSimplex.inv.app m ≫ SSet.toTop.map a ≫
        SSet.stdSimplex.toTopObjIsoI.hom =
      SimplexCategory.toTop.map α ≫ SSet.toTopSimplex.inv.app n ≫
        SSet.toTop.map b ≫ SSet.stdSimplex.toTopObjIsoI.hom := by
  subst a
  have hnat := SSet.toTopSimplex.{u}.inv.naturality α
  change SimplexCategory.toTop.map α ≫ SSet.toTopSimplex.inv.app n =
    SSet.toTopSimplex.inv.app m ≫ SSet.toTop.map (SSet.stdSimplex.map α) at hnat
  calc
    _ = SSet.toTopSimplex.inv.app m ≫
        (SSet.toTop.map (SSet.stdSimplex.map α) ≫
          SSet.toTop.map b) ≫ SSet.stdSimplex.toTopObjIsoI.hom := by
      rw [Functor.map_comp]
    _ = (SimplexCategory.toTop.map α ≫
          SSet.toTopSimplex.inv.app n) ≫
        SSet.toTop.map b ≫ SSet.stdSimplex.toTopObjIsoI.hom := by
      rw [hnat]
      simp only [Category.assoc]
    _ = _ := by simp only [Category.assoc]

private theorem intervalMap_δ_of_le (p : ℕ) (i : Fin (p + 2))
    (j : Fin (p + 1)) (hij : i ≤ j.castSucc) :
    intervalMap.{u} p j =
      SimplexCategory.toTop.map (SimplexCategory.δ i.castSucc) ≫
        intervalMap (p + 1) j.succ := by
  have h := congrArg
    (fun z => z ≫ CartesianMonoidalCategory.snd
      (Δ[p + 1] : SSet.{u}) (Δ[1] : SSet.{u}))
    (SSet.prodStdSimplex₁.ι_δ_whiskerRight_of_le i j hij)
  simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
    SSet.prodStdSimplex₁.ι_snd] at h
  apply realizedIntervalMap_naturality
  exact h

private theorem intervalMap_δ_of_gt (p : ℕ) (i : Fin (p + 2))
    (j : Fin (p + 1)) (hji : j.castSucc < i) :
    intervalMap.{u} p j =
      SimplexCategory.toTop.map (SimplexCategory.δ i.succ) ≫
        intervalMap (p + 1) j.castSucc := by
  have h := congrArg
    (fun z => z ≫ CartesianMonoidalCategory.snd
      (Δ[p + 1] : SSet.{u}) (Δ[1] : SSet.{u}))
    (SSet.prodStdSimplex₁.ι_δ_whiskerRight_of_gt i j hji)
  simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
    SSet.prodStdSimplex₁.ι_snd] at h
  apply realizedIntervalMap_naturality
  exact h

private theorem intervalMap_σ_of_le (p : ℕ)
    (i j : Fin (p + 1)) (hij : i ≤ j) :
    intervalMap.{u} (p + 1) j.succ =
      SimplexCategory.toTop.map (SimplexCategory.σ i.castSucc) ≫
        intervalMap p j := by
  have h := congrArg
    (fun z => z ≫ CartesianMonoidalCategory.snd
      (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}))
    (SSet.prodStdSimplex₁.ι_σ_whiskerRight_of_le i j hij)
  simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
    SSet.prodStdSimplex₁.ι_snd] at h
  apply realizedIntervalMap_naturality
  exact h

private theorem intervalMap_σ_of_ge (p : ℕ)
    (i j : Fin (p + 1)) (hji : j ≤ i) :
    intervalMap.{u} (p + 1) j.castSucc =
      SimplexCategory.toTop.map (SimplexCategory.σ i.succ) ≫
        intervalMap p j := by
  have h := congrArg
    (fun z => z ≫ CartesianMonoidalCategory.snd
      (Δ[p] : SSet.{u}) (Δ[1] : SSet.{u}))
    (SSet.prodStdSimplex₁.ι_σ_whiskerRight_of_ge i j hji)
  simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
    SSet.prodStdSimplex₁.ι_snd] at h
  apply realizedIntervalMap_naturality
  exact h

-- The exact four equations frozen by the blocked design.
/-- Internal face-reindexing law for an interval cell on the lower side of
the breakpoint. -/
theorem _root_.TopCat.IntervalPrism.Internal.cell_δ_of_le
    (p : ℕ) (i : Fin (p + 2))
    (j : Fin (p + 1)) (hij : i ≤ j.castSucc) :
    TopCat.IntervalPrism.cell.{u} p j ≫
        (SimplexCategory.toTop.map (SimplexCategory.δ i) ▷ TopCat.I) =
      SimplexCategory.toTop.map (SimplexCategory.δ i.castSucc) ≫
        TopCat.IntervalPrism.cell (p + 1) j.succ := by
  change cell.{u} p j ≫
      (SimplexCategory.toTop.map (SimplexCategory.δ i) ▷ TopCat.I) =
    SimplexCategory.toTop.map (SimplexCategory.δ i.castSucc) ≫
      cell (p + 1) j.succ
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      cell_fst_assoc]
    rw [cell_fst, ← SimplexCategory.toTop.map_comp,
      ← SimplexCategory.δ_comp_σ_of_le hij,
      ← SimplexCategory.toTop.map_comp]
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      cell_snd]
    exact intervalMap_δ_of_le p i j hij

/-- Internal face-reindexing law for an interval cell on the upper side of
the breakpoint. -/
theorem _root_.TopCat.IntervalPrism.Internal.cell_δ_of_gt
    (p : ℕ) (i : Fin (p + 2))
    (j : Fin (p + 1)) (hji : j.castSucc < i) :
    TopCat.IntervalPrism.cell.{u} p j ≫
        (SimplexCategory.toTop.map (SimplexCategory.δ i) ▷ TopCat.I) =
      SimplexCategory.toTop.map (SimplexCategory.δ i.succ) ≫
        TopCat.IntervalPrism.cell (p + 1) j.castSucc := by
  change cell.{u} p j ≫
      (SimplexCategory.toTop.map (SimplexCategory.δ i) ▷ TopCat.I) =
    SimplexCategory.toTop.map (SimplexCategory.δ i.succ) ≫
      cell (p + 1) j.castSucc
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      cell_fst_assoc]
    rw [cell_fst, ← SimplexCategory.toTop.map_comp,
      ← SimplexCategory.δ_comp_σ_of_gt hji,
      ← SimplexCategory.toTop.map_comp]
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      cell_snd]
    exact intervalMap_δ_of_gt p i j hji

/-- Internal degeneracy-reindexing law for an interval cell on the lower
side of the breakpoint. -/
theorem _root_.TopCat.IntervalPrism.Internal.cell_σ_of_le
    (p : ℕ) (i j : Fin (p + 1)) (hij : i ≤ j) :
    TopCat.IntervalPrism.cell.{u} (p + 1) j.succ ≫
        (SimplexCategory.toTop.map (SimplexCategory.σ i) ▷ TopCat.I) =
      SimplexCategory.toTop.map (SimplexCategory.σ i.castSucc) ≫
        TopCat.IntervalPrism.cell p j := by
  change cell.{u} (p + 1) j.succ ≫
      (SimplexCategory.toTop.map (SimplexCategory.σ i) ▷ TopCat.I) =
    SimplexCategory.toTop.map (SimplexCategory.σ i.castSucc) ≫ cell p j
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      cell_fst_assoc]
    rw [cell_fst, ← SimplexCategory.toTop.map_comp,
      ← SimplexCategory.σ_comp_σ hij,
      ← SimplexCategory.toTop.map_comp]
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      cell_snd]
    exact intervalMap_σ_of_le p i j hij

/-- Internal degeneracy-reindexing law for an interval cell on the upper
side of the breakpoint. -/
theorem _root_.TopCat.IntervalPrism.Internal.cell_σ_of_ge
    (p : ℕ) (i j : Fin (p + 1)) (hji : j ≤ i) :
    TopCat.IntervalPrism.cell.{u} (p + 1) j.castSucc ≫
        (SimplexCategory.toTop.map (SimplexCategory.σ i) ▷ TopCat.I) =
      SimplexCategory.toTop.map (SimplexCategory.σ i.succ) ≫
        TopCat.IntervalPrism.cell p j := by
  change cell.{u} (p + 1) j.castSucc ≫
      (SimplexCategory.toTop.map (SimplexCategory.σ i) ▷ TopCat.I) =
    SimplexCategory.toTop.map (SimplexCategory.σ i.succ) ≫ cell p j
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      cell_fst_assoc]
    rw [cell_fst, ← SimplexCategory.toTop.map_comp,
      SimplexCategory.σ_comp_σ hji,
      ← SimplexCategory.toTop.map_comp]
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      cell_snd]
    exact intervalMap_σ_of_ge p i j hji


end TopCat.IntervalPrismCellReindex

end
