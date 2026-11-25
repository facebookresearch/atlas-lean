/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixConnesWorkingHeight
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixHeightCyclic
public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTailHomologyMapFunctor

/-!
# Naturality of stable matrix cyclic homology comparisons

The vanishing boundary from Chevalley–Eilenberg degree one to zero identifies positive-tail
homology with homology in the next degree. Over a commutative rational algebra, the stable
matrix trace map induces compatible maps to Connes and cyclic homology.

These comparisons are natural in algebra homomorphisms between independent coefficient carrier
universes and preserve the normalization and degree sign `(-1)^n`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The degree-one vanishing is retained by the canonical stable CE model. -/
theorem canonicalStableMatrixCEComplex_d_one_zero :
    (canonicalStableMatrixCEComplex k A).d 1 0 = 0 := by
  let e := canonicalStableMatrixCEIso k A
  let : IsIso (e.hom.f 1) :=
    ((HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) 1).mapIso e).isIso_hom
  apply (cancel_epi (e.hom.f 1)).1
  rw [Limits.comp_zero]
  exact (e.hom.comm 1 0).trans
    ((congrArg (fun f => f ≫ e.hom.f 0) (stableMatrixCEComplex_d_one_zero k A)).trans
      Limits.zero_comp)

/-- The positive-tail homology shift on CE of the canonical stable Lie algebra. -/
def canonicalStableMatrixPositiveTailHomologyIso (n : ℕ) :
    (ChainComplex.positiveTail (canonicalStableMatrixCEComplex k A)).homology n ≅
      (canonicalStableMatrixCEComplex k A).homology (n + 1) :=
  ChainComplex.positiveTailHomologyIso (canonicalStableMatrixCEComplex k A)
    (canonicalStableMatrixCEComplex_d_one_zero k A) n

/-- Additive lifting retains the degree-one zero differential. -/
theorem canonicalStableMatrixCEComplexAtHeight_d_one_zero :
    (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).d 1 0 = 0 :=
  ChainComplex.mapHomologicalComplex_d_one_zero
    (ModuleCat.uliftFunctor.{max u v z, max u v} k) (canonicalStableMatrixCEComplex k A)
      (canonicalStableMatrixCEComplex_d_one_zero k A)

/-- The shifted-homology comparison on the common-height canonical stable CE model. -/
def canonicalStableMatrixPositiveTailHomologyIsoAtHeight (n : ℕ) :
    (ChainComplex.positiveTail (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A)).homology n ≅
      (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).homology (n + 1) :=
  ChainComplex.positiveTailHomologyIso (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A)
    (canonicalStableMatrixCEComplexAtHeight_d_one_zero.{u,v,z} k A) n

variable [Algebra ℚ k]

/-- The cyclic trace map from stable matrix Lie homology in degree n + 1 to Connes homology in
degree n. -/
def canonicalStableMatrixCyclicConnesHomologyMap (n : ℕ) :
    (canonicalStableMatrixCEComplex k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
  (canonicalStableMatrixPositiveTailHomologyIso k A n).inv ≫
    HomologicalComplex.homologyMap (canonicalStableMatrixCyclicWeibelChainMap k A) n

/-- The cyclic trace map from lifted stable matrix Lie homology in degree n + 1 to lifted Connes
homology in degree n. -/
def canonicalStableMatrixCyclicConnesHomologyMapAtHeight (n : ℕ) :
    (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyAtHeight.{u,v,z} k A n :=
  (canonicalStableMatrixPositiveTailHomologyIsoAtHeight.{u,v,z} k A n).inv ≫
    HomologicalComplex.homologyMap (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,z} k A) n

/-- The canonical homology map followed by Connes' projection is this same shifted trace. -/
theorem canonicalStableMatrixCyclicHomologyMap_comp_connes (n : ℕ) :
    canonicalStableMatrixCyclicHomologyMap k A n ≫
        ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n =
      canonicalStableMatrixCyclicConnesHomologyMap k A n := by
  let e := canonicalStableMatrixCEIso k A
  let s := stableMatrixPositiveTailHomologyIso k A n
  let c := canonicalStableMatrixPositiveTailHomologyIso k A n
  let t := HomologicalComplex.homologyMap e.inv (n + 1)
  let ht := HomologicalComplex.homologyMap (ChainComplex.positiveTailMap e.inv) n
  let hs := HomologicalComplex.homologyMap (stableMatrixCyclicWeibelChainMap k A) n
  have h : ht ≫ s.hom = c.hom ≫ t :=
    ChainComplex.positiveTailHomologyIso_naturality e.inv
      (canonicalStableMatrixCEComplex_d_one_zero k A) (stableMatrixCEComplex_d_one_zero k A) n
  have hInv : t ≫ s.inv = c.inv ≫ ht := by
    apply (cancel_mono s.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hChain : HomologicalComplex.homologyMap (canonicalStableMatrixCyclicWeibelChainMap k A) n =
      ht ≫ hs := HomologicalComplex.homologyMap_comp _ _ n
  have hOriginal := stableMatrixCyclicHomologyMap_comp_connes k A n
  change (t ≫ stableMatrixCyclicHomologyMap k A n) ≫
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n =
      c.inv ≫ HomologicalComplex.homologyMap (canonicalStableMatrixCyclicWeibelChainMap k A) n
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => t ≫ f) hOriginal).trans
      ((Category.assoc t s.inv hs).symm.trans
        ((congrArg (fun f => f ≫ hs) hInv).trans
          ((Category.assoc c.inv ht hs).trans (congrArg (fun f => c.inv ≫ f) hChain.symm)))))

/-- The full-height shifted trace agrees with transport of the canonical trace homology map. -/
theorem canonicalStableMatrixCyclicConnesHomologyMapAtHeight_eq_lift (n : ℕ) :
    canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,v,z} k A n =
      (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
        (ComplexShape.down ℕ) (n + 1)).app (canonicalStableMatrixCEComplex k A)).hom ≫
        (ModuleCat.uliftFunctor.{max u v z, max u v} k).map
          (canonicalStableMatrixCyclicConnesHomologyMap k A n) ≫
          (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
            (ComplexShape.down ℕ) n).app
              (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).inv ≫
            HomologicalComplex.homologyMap
              (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom n := by
  let U := ModuleCat.uliftFunctor.{max u v z, max u v} k
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let K : ChainComplex (ModuleCat.{max u v} k) ℕ := canonicalStableMatrixCEComplex k A
  let Q : ChainComplex (ModuleCat.{max u v} k) ℕ := ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A
  let T : ChainComplex (ModuleCat.{max u v} k) ℕ := ChainComplex.positiveTail K
  let KU : ChainComplex (ModuleCat.{max u v z} k) ℕ := F.obj K
  let TU : ChainComplex (ModuleCat.{max u v z} k) ℕ := ChainComplex.positiveTail KU
  let FT : ChainComplex (ModuleCat.{max u v z} k) ℕ := F.obj T
  let FQ : ChainComplex (ModuleCat.{max u v z} k) ℕ := F.obj Q
  let QH : ChainComplex (ModuleCat.{max u v z} k) ℕ :=
    ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A
  let w : T ⟶ Q := canonicalStableMatrixCyclicWeibelChainMap k A
  let e : TU ≅ FT := (ChainComplex.positiveTailMapFunctorIso U).app K
  let qN : FQ ⟶ QH := (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom
  let s : U.obj (T.homology n) ≅ U.obj (K.homology (n + 1)) :=
    U.mapIso (canonicalStableMatrixPositiveTailHomologyIso k A n)
  let sH : TU.homology n ≅ KU.homology (n + 1) :=
    canonicalStableMatrixPositiveTailHomologyIsoAtHeight.{u,v,z} k A n
  let χK : KU.homology (n + 1) ≅ U.obj (K.homology (n + 1)) :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) (n + 1)).app K
  let χT : FT.homology n ≅ U.obj (T.homology n) :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app T
  let χQ : FQ.homology n ≅ U.obj (Q.homology n) :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app Q
  let he : TU.homology n ⟶ FT.homology n := HomologicalComplex.homologyMap e.hom n
  let hw : FT.homology n ⟶ FQ.homology n := HomologicalComplex.homologyMap (F.map w) n
  let hq : FQ.homology n ⟶ QH.homology n := HomologicalComplex.homologyMap qN n
  have hShift : he ≫ χT.hom ≫ s.hom = sH.hom ≫ χK.hom :=
    ChainComplex.positiveTailHomologyIso_map U K (canonicalStableMatrixCEComplex_d_one_zero k A) n
  have hShiftInv : sH.inv ≫ he ≫ χT.hom = χK.hom ≫ s.inv := by
    apply (Iso.eq_comp_inv s).2
    exact (Category.assoc sH.inv (he ≫ χT.hom) s.hom).trans
      ((congrArg (fun f => sH.inv ≫ f) ((Category.assoc he χT.hom s.hom).trans hShift)).trans
        ((Category.assoc sH.inv sH.hom χK.hom).symm.trans
          ((congrArg (fun f => f ≫ χK.hom) sH.inv_hom_id).trans (Category.id_comp χK.hom))))
  have hW : χT.hom ≫ U.map (HomologicalComplex.homologyMap w n) ≫ χQ.inv = hw := by
    have hNat := U.mapHomologicalComplexHomologyIso_hom_naturality (ComplexShape.down ℕ) n w
    exact (congrArg (fun f => f ≫ χQ.inv) hNat.symm).trans
      ((Category.assoc hw χQ.hom χQ.inv).trans
        ((congrArg (fun f => hw ≫ f) χQ.hom_inv_id).trans (Category.comp_id hw)))
  let H : ChainComplex (ModuleCat.{max u v z} k) ℕ ⥤ ModuleCat.{max u v z} k :=
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v z} k) (ComplexShape.down ℕ) n
  have hChain : HomologicalComplex.homologyMap
      (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,z} k A) n = he ≫ hw ≫ hq := by
    change H.map (e.hom ≫ F.map w ≫ qN) = he ≫ hw ≫ hq
    exact (H.map_comp e.hom (F.map w ≫ qN)).trans
      (congrArg (fun f => he ≫ f) (H.map_comp (F.map w) qN))
  have hExpand : sH.inv ≫ he ≫ hw ≫ hq =
      (sH.inv ≫ he ≫ χT.hom) ≫ U.map (HomologicalComplex.homologyMap w n) ≫ χQ.inv ≫ hq := by
    exact (congrArg (fun f : FT.homology n ⟶ FQ.homology n => sH.inv ≫ he ≫ f ≫ hq) hW.symm).trans
      (by simp only [Category.assoc])
  have hMap : U.map (canonicalStableMatrixCyclicConnesHomologyMap k A n) =
      s.inv ≫ U.map (HomologicalComplex.homologyMap w n) :=
    U.map_comp (canonicalStableMatrixPositiveTailHomologyIso k A n).inv (HomologicalComplex.homologyMap w n)
  change sH.inv ≫ HomologicalComplex.homologyMap
      (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,z} k A) n =
    χK.hom ≫ U.map (canonicalStableMatrixCyclicConnesHomologyMap k A n) ≫ χQ.inv ≫ hq
  exact (congrArg (fun f => sH.inv ≫ f) hChain).trans
    (hExpand.trans
      ((congrArg (fun f => f ≫ U.map (HomologicalComplex.homologyMap w n) ≫ χQ.inv ≫ hq) hShiftInv).trans
        ((show (χK.hom ≫ s.inv) ≫ U.map (HomologicalComplex.homologyMap w n) ≫ χQ.inv ≫ hq =
            χK.hom ≫ (s.inv ≫ U.map (HomologicalComplex.homologyMap w n)) ≫ χQ.inv ≫ hq by
          simp only [Category.assoc]).trans
          (congrArg (fun f => χK.hom ≫ f ≫ χQ.inv ≫ hq) hMap.symm))))

/-- The full-height HC map has the same shifted Connes factorization. -/
theorem canonicalStableMatrixCyclicHomologyMapAtHeight_comp_connes (n : ℕ) :
    canonicalStableMatrixCyclicHomologyMapAtHeight.{u,v,z} k A n ≫
        (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight.{u,v,z} k A n).hom =
      canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,v,z} k A n := by
  let U := ModuleCat.uliftFunctor.{max u v z, max u v} k
  let χ := (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) (n + 1)).app
    (canonicalStableMatrixCEComplex k A)
  let q := (((U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).inv ≫
      HomologicalComplex.homologyMap
        (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom n)
  have h := U.congr_map (canonicalStableMatrixCyclicHomologyMap_comp_connes k A n)
  rw [U.map_comp] at h
  rw [canonicalStableMatrixCyclicConnesHomologyMapAtHeight_eq_lift,
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight_hom]
  change (χ.hom ≫ U.map (canonicalStableMatrixCyclicHomologyMap k A n)) ≫
      (U.map (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n) ≫ q) =
    χ.hom ≫ U.map (canonicalStableMatrixCyclicConnesHomologyMap k A n) ≫ q
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => χ.hom ≫ f) (Category.assoc _ _ _).symm).trans
      (congrArg (fun f => χ.hom ≫ f ≫ q) h))

variable {B : Type w} [Ring B] [Algebra k B]

/-- The full-height shifted Connes homology map preserves coefficient maps. -/
@[reassoc]
theorem canonicalStableMatrixCyclicConnesHomologyMapAtHeight_naturality (f : A →ₐ[k] B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) (n + 1) ≫
      canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,w,max u v w z} k B n =
    canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,v,max u v w z} k A n ≫
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMapAtHeight.{u,v,w,z} k A
        f.toNonUnitalAlgHom n := by
  let c := canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f
  let sA := canonicalStableMatrixPositiveTailHomologyIsoAtHeight.{u,v,max u v w z} k A n
  let sB := canonicalStableMatrixPositiveTailHomologyIsoAtHeight.{u,w,max u v w z} k B n
  let h := HomologicalComplex.homologyMap c (n + 1)
  let ht := HomologicalComplex.homologyMap (ChainComplex.positiveTailMap c) n
  let wA := HomologicalComplex.homologyMap
    (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A) n
  let wB := HomologicalComplex.homologyMap
    (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B) n
  let q := ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMapAtHeight.{u,v,w,z} k A
    f.toNonUnitalAlgHom n
  have hs : ht ≫ sB.hom = sA.hom ≫ h :=
    ChainComplex.positiveTailHomologyIso_naturality c
      (canonicalStableMatrixCEComplexAtHeight_d_one_zero.{u,v,max u v w z} k A)
      (canonicalStableMatrixCEComplexAtHeight_d_one_zero.{u,w,max u v w z} k B) n
  have hsInv : h ≫ sB.inv = sA.inv ≫ ht := by
    apply (cancel_mono sB.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hs,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hw : ht ≫ wB = wA ≫ q := by
    have hh := congrArg (fun f => HomologicalComplex.homologyMap f n)
      (canonicalStableMatrixCyclicWeibelChainMapAtHeight_naturality.{u,v,w,z} k A f)
    simp only [HomologicalComplex.homologyMap_comp] at hh
    exact hh
  change h ≫ (sB.inv ≫ wB) = (sA.inv ≫ wA) ≫ q
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ wB) hsInv).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => sA.inv ≫ f) hw).trans (Category.assoc _ _ _).symm)))

/-- The canonical stable Lie CE-to-HC map is natural across independent coefficient universes. -/
@[reassoc]
theorem canonicalStableMatrixCyclicHomologyMapAtHeight_naturality (f : A →ₐ[k] B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) (n + 1) ≫
      canonicalStableMatrixCyclicHomologyMapAtHeight.{u,w,max u v w z} k B n =
    canonicalStableMatrixCyclicHomologyMapAtHeight.{u,v,max u v w z} k A n ≫
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomologyMapAtHeight.{u,v,w,z}
        f.toNonUnitalAlgHom n := by
  let eA := ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight.{u,v,max u v w z}
    k A n
  let eB := ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight.{u,w,max u v w z}
    k B n
  let h := HomologicalComplex.homologyMap
    (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) (n + 1)
  let cA := canonicalStableMatrixCyclicHomologyMapAtHeight.{u,v,max u v w z} k A n
  let cB := canonicalStableMatrixCyclicHomologyMapAtHeight.{u,w,max u v w z} k B n
  let m := ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomologyMapAtHeight.{u,v,w,z}
    f.toNonUnitalAlgHom n
  let q := ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMapAtHeight.{u,v,w,z} k A
    f.toNonUnitalAlgHom n
  have hA : cA ≫ eA.hom = canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,v,max u v w z}
      k A n := canonicalStableMatrixCyclicHomologyMapAtHeight_comp_connes.{u,v,max u v w z} k A n
  have hB : cB ≫ eB.hom = canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,w,max u v w z}
      k B n := canonicalStableMatrixCyclicHomologyMapAtHeight_comp_connes.{u,w,max u v w z} k B n
  have hM : m ≫ eB.hom = eA.hom ≫ q :=
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight_hom_naturality.{u,v,w,z}
      k A f.toNonUnitalAlgHom n
  apply (cancel_mono eB.hom).1
  exact (Category.assoc h cB eB.hom).trans
    ((congrArg (fun f => h ≫ f) hB).trans
      ((canonicalStableMatrixCyclicConnesHomologyMapAtHeight_naturality.{u,v,w,z} k A f n).trans
        ((congrArg (fun f => f ≫ q) hA.symm).trans
          ((Category.assoc cA eA.hom q).trans
            ((congrArg (fun f => cA ≫ f) hM.symm).trans (Category.assoc cA m eB.hom).symm)))))

end ChevalleyEilenberg
