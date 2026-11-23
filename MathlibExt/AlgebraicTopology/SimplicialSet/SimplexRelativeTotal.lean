/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanRelativeCoefficient
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotalNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionAugmentationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceAddCommGrpChains
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Original simplex-resolution totals and their relative augmentation

The actual shuffle map and carrier-chain Iso followed by the original
simplex-resolution augmentation define a map from the signed total to the
original chains. This map is a quasi-isomorphism and is natural for the
original map over the common base.

For a monomorphism over that base, the original relative total maps to the
original relative chain quotient by the computed cokernel map. The quotient
square is retained and the stock short-exact comparison proves that this
relative augmentation is a quasi-isomorphism. Ordinary homology isomorphism
of the original monomorphism therefore makes the actual relative total
acyclic. No cover-homology or relative-acyclicity witness is supplied.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology Opposite
open scoped Simplicial

universe w

public section

namespace SSet

local instance : HasCoproducts.{w} (ChainComplex AddCommGrpCat.{w} ℕ) := fun I =>
  let : Small.{w} (Discrete I) := small_self (Discrete I)
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  HomologicalComplex.instHasColimitsOfShape

variable (R : AddCommGrpCat.{w})

/-- The actual shuffle and original augmentation, with the original source as target. -/
def simplexTotalAugmentation {Z B : SSet.{w}} (p : Z ⟶ B) :
    bkAlternatingTotalComplex AddCommGrpCat.{w} R (simplexPullbackDiagram p) ⟶
      Z.chainComplex R :=
  (bkDiagonalTotalHomotopyEquiv AddCommGrpCat.{w} R (simplexPullbackDiagram p)).inv ≫
    (bkCarrierChainIso AddCommGrpCat.{w} R (simplexPullbackDiagram p)).inv ≫
      SSet.chainComplexMap (simplexResolutionAugmentation p) R

/-- The actual augmentation is a quasi-isomorphism, by the existing resolution theorem. -/
theorem simplexTotalAugmentation_quasiIso {Z B : SSet.{w}} (p : Z ⟶ B) :
    QuasiIso (simplexTotalAugmentation R p) := by
  let e := bkDiagonalTotalHomotopyEquiv AddCommGrpCat.{w} R
    (simplexPullbackDiagram p)
  let c : (simplexResolution p).chainComplex R ≅ _ :=
    bkCarrierChainIso AddCommGrpCat.{w} R (simplexPullbackDiagram p)
  have hWeak := simplexResolutionAugmentation_mem_realizationWeakEquivalences p
  let : QuasiIso (SSet.chainComplexMap (simplexResolutionAugmentation p) R) :=
    hWeak.quasiIso_chainComplexMap_addCommGrp R
  let : QuasiIso e.inv := e.quasiIso_inv
  let : QuasiIso c.inv := by infer_instance
  change QuasiIso (e.inv ≫ c.inv ≫
    SSet.chainComplexMap (simplexResolutionAugmentation p) R)
  let : QuasiIso (c.inv ≫ SSet.chainComplexMap (simplexResolutionAugmentation p) R) :=
    quasiIso_comp c.inv
      (SSet.chainComplexMap (simplexResolutionAugmentation p) R)
  exact quasiIso_comp e.inv
    (c.inv ≫ SSet.chainComplexMap (simplexResolutionAugmentation p) R)

/-- The complete total-to-original-chain square for a map over the same base. -/
theorem simplexTotalAugmentation_naturality {Z Z' B : SSet.{w}}
    {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') (hu : u ≫ q = p) :
    (bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map
        (simplexPullbackDiagramMap u hu) ≫ simplexTotalAugmentation R q =
      simplexTotalAugmentation R p ≫ SSet.chainComplexMap u R := by
  let α := simplexPullbackDiagramMap u hu
  let C := (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R
  let Kp : ChainComplex AddCommGrpCat.{w} ℕ := C.obj (simplexResolution p)
  let Kq : ChainComplex AddCommGrpCat.{w} ℕ := C.obj (simplexResolution q)
  let eP := bkDiagonalTotalHomotopyEquiv AddCommGrpCat.{w} R
    (simplexPullbackDiagram p)
  let eQ := bkDiagonalTotalHomotopyEquiv AddCommGrpCat.{w} R
    (simplexPullbackDiagram q)
  let cP : Kp ≅ _ := bkCarrierChainIso AddCommGrpCat.{w} R (simplexPullbackDiagram p)
  let cQ : Kq ≅ _ := bkCarrierChainIso AddCommGrpCat.{w} R (simplexPullbackDiagram q)
  let a := (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{w}).map
    ((coproductLinearizationFunctor AddCommGrpCat.{w} R).map (bkHocolimMap α))
  let m := (bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α
  let r : Kp ⟶ Kq := C.map (simplexResolutionMap u hu)
  let ap : Kp ⟶ C.obj Z := C.map (simplexResolutionAugmentation p)
  let aq : Kq ⟶ C.obj Z' := C.map (simplexResolutionAugmentation q)
  let g : C.obj Z ⟶ C.obj Z' := C.map u
  have hShuffle : m ≫ eQ.inv = eP.inv ≫ a :=
    bkDiagonalTotalHomotopyEquiv_inv_naturality AddCommGrpCat.{w} R α
  have hCarrier : a ≫ cQ.inv = cP.inv ≫ r := by
    apply (cancel_mono cQ.hom).mp
    have h : r ≫ cQ.hom = cP.hom ≫ a :=
      bkCarrierChainIso_naturality AddCommGrpCat.{w} R α
    exact (Category.assoc a cQ.inv cQ.hom).trans
      ((congrArg (fun k => a ≫ k) cQ.inv_hom_id).trans
        ((Category.comp_id a).trans
          (((congrArg (fun k => k ≫ a) cP.inv_hom_id).trans
            (Category.id_comp a)).symm.trans
            ((Category.assoc cP.inv cP.hom a).trans
              ((congrArg (fun k => cP.inv ≫ k) h.symm).trans
                (Category.assoc cP.inv r cQ.hom).symm)))))
  have hAug : r ≫ aq = ap ≫ g :=
    (C.map_comp _ _).symm.trans
      ((congrArg C.map (simplexResolutionAugmentation_naturality u hu)).trans
        (C.map_comp _ _))
  have hLift : (eP.inv ≫ a) ≫ cQ.inv = (eP.inv ≫ cP.inv) ≫ r :=
    (Category.assoc eP.inv a cQ.inv).trans
      ((congrArg (fun k => eP.inv ≫ k) hCarrier).trans
        (Category.assoc eP.inv cP.inv r).symm)
  change m ≫ (eQ.inv ≫ cQ.inv ≫ aq) = (eP.inv ≫ cP.inv ≫ ap) ≫ g
  exact (Category.assoc m eQ.inv (cQ.inv ≫ aq)).symm.trans
    ((Category.assoc (m ≫ eQ.inv) cQ.inv aq).symm.trans
      ((congrArg (fun k => (k ≫ cQ.inv) ≫ aq) hShuffle).trans
        ((congrArg (fun k => k ≫ aq) hLift).trans
          ((Category.assoc (eP.inv ≫ cP.inv) r aq).trans
            ((congrArg (fun k => (eP.inv ≫ cP.inv) ≫ k) hAug).trans
              ((Category.assoc (eP.inv ≫ cP.inv) ap g).symm.trans
                (congrArg (fun k => k ≫ g) (Category.assoc eP.inv cP.inv ap))))))))

theorem simplexPullbackDiagramMap_mono {Z Z' B : SSet.{w}}
    {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') [Mono u] (hu : u ≫ q = p)
    (s : SimplexIndex B) : Mono ((simplexPullbackDiagramMap u hu).app s) := by
  constructor
  intro T a b h
  let m := (simplexPullbackDiagramMap u hu).app s
  let fp := pullback.fst p s.hom
  let fq := pullback.fst q s.hom
  let sp := pullback.snd p s.hom
  let sq := pullback.snd q s.hom
  have hFirst : m ≫ fq = fp ≫ u := simplexPullbackDiagramMap_app_fst u hu s
  have hSecond : m ≫ sq = sp := simplexPullbackDiagramMap_app_snd u hu s
  apply pullback.hom_ext
  · apply (cancel_mono u).mp
    have hF : (a ≫ m) ≫ fq = (b ≫ m) ≫ fq :=
      congrArg (fun k => k ≫ fq) h
    have ha : (a ≫ m) ≫ fq = (a ≫ fp) ≫ u :=
      (Category.assoc a m fq).trans
        ((congrArg (fun k => a ≫ k) hFirst).trans (Category.assoc a fp u).symm)
    have hb : (b ≫ m) ≫ fq = (b ≫ fp) ≫ u :=
      (Category.assoc b m fq).trans
        ((congrArg (fun k => b ≫ k) hFirst).trans (Category.assoc b fp u).symm)
    exact ha.symm.trans (hF.trans hb)
  · have hS : (a ≫ m) ≫ sq = (b ≫ m) ≫ sq :=
      congrArg (fun k => k ≫ sq) h
    have ha : (a ≫ m) ≫ sq = a ≫ sp :=
      (Category.assoc a m sq).trans (congrArg (fun k => a ≫ k) hSecond)
    have hb : (b ≫ m) ≫ sq = b ≫ sp :=
      (Category.assoc b m sq).trans (congrArg (fun k => b ≫ k) hSecond)
    exact ha.symm.trans (hS.trans hb)

private theorem simplexTotalMap_mono {Z Z' B : SSet.{w}}
    {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') [Mono u] (hu : u ≫ q = p) :
    Mono ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map
      (simplexPullbackDiagramMap u hu)) := by
  let α := simplexPullbackDiagramMap u hu
  let C := (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R
  let γ := Functor.whiskerRight α C
  let : ∀ s, Mono (γ.app s) := fun s => by
    let : Mono (α.app s) := simplexPullbackDiagramMap_mono u hu s
    let P : SSetPair.{w} := SSetPair.of (α.app s)
    exact inferInstanceAs (Mono (SSet.chainComplexMap P.hom R))
  let : Mono γ := NatTrans.mono_of_mono_app γ
  let : Mono ((coefficientChainTotalFunctor (J := SimplexIndex B)).map γ) :=
    inferInstance
  let : Mono ((bkCoefficientChainTotalIso R (simplexPullbackDiagram p)).hom ≫
      (coefficientChainTotalFunctor (J := SimplexIndex B)).map γ) := inferInstance
  exact mono_of_mono_fac (bkCoefficientChainTotalIso_naturality R α)

/-- The relative coefficient total for the original map over the base. -/
abbrev simplexRelativeCoefficientTotal {Z Z' B : SSet.{w}}
    {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') (hu : u ≫ q = p) :
    ChainComplex AddCommGrpCat.{w} ℕ :=
  (coefficientChainTotalFunctor (J := SimplexIndex B)).obj
    (cokernel (Functor.whiskerRight (simplexPullbackDiagramMap u hu)
      ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R)))

/-- The computed relative augmentation returns the original relative chain quotient. -/
def simplexRelativeTotalAugmentation {Z Z' B : SSet.{w}}
    {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') (hu : u ≫ q = p) :
    simplexRelativeCoefficientTotal R u hu ⟶ cokernel (SSet.chainComplexMap u R) :=
  (bkRelativeCoefficientTotalIso R (simplexPullbackDiagramMap u hu)).inv ≫
    cokernel.map
      ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map
        (simplexPullbackDiagramMap u hu))
      (SSet.chainComplexMap u R) (simplexTotalAugmentation R p)
      (simplexTotalAugmentation R q) (simplexTotalAugmentation_naturality R u hu)

/-- The whole original relative quotient square for the augmentation. -/
theorem simplexRelativeTotalAugmentation_projection {Z Z' B : SSet.{w}}
    {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') (hu : u ≫ q = p) :
    (coefficientChainTotalFunctor (J := SimplexIndex B)).map
        (cokernel.π (Functor.whiskerRight (simplexPullbackDiagramMap u hu)
          ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R))) ≫
        simplexRelativeTotalAugmentation R u hu =
      (bkCoefficientChainTotalIso R (simplexPullbackDiagram q)).inv ≫
        simplexTotalAugmentation R q ≫ cokernel.π (SSet.chainComplexMap u R) := by
  let α := simplexPullbackDiagramMap u hu
  let e := bkRelativeCoefficientTotalIso R α
  let eQ := bkCoefficientChainTotalIso R (simplexPullbackDiagram q)
  let v := cokernel.map
    ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α)
    (SSet.chainComplexMap u R) (simplexTotalAugmentation R p)
    (simplexTotalAugmentation R q) (simplexTotalAugmentation_naturality R u hu)
  have hProjection := bkRelativeCoefficientTotalIso_projection R α
  have hv : cokernel.π ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α) ≫ v =
      simplexTotalAugmentation R q ≫ cokernel.π (SSet.chainComplexMap u R) :=
    cokernel.π_desc _ _ _
  let qF := (coefficientChainTotalFunctor (J := SimplexIndex B)).map
    (cokernel.π (Functor.whiskerRight α ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R)))
  let z := simplexTotalAugmentation R q ≫ cokernel.π (SSet.chainComplexMap u R)
  have hP : cokernel.π ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α) ≫
      e.hom = eQ.hom ≫ qF := hProjection
  have hCancel : e.hom ≫ (e.inv ≫ v) = v :=
    (Category.assoc e.hom e.inv v).symm.trans
      ((congrArg (fun k => k ≫ v) e.hom_inv_id).trans (Category.id_comp v))
  have hQ : eQ.hom ≫ (eQ.inv ≫ z) = z :=
    (Category.assoc eQ.hom eQ.inv z).symm.trans
      ((congrArg (fun k => k ≫ z) eQ.hom_inv_id).trans (Category.id_comp z))
  apply (cancel_epi eQ.hom).mp
  change eQ.hom ≫ (qF ≫ (e.inv ≫ v)) = eQ.hom ≫ (eQ.inv ≫ z)
  exact (Category.assoc eQ.hom qF (e.inv ≫ v)).symm.trans
    ((congrArg (fun k => k ≫ (e.inv ≫ v)) hP.symm).trans
      ((Category.assoc
          (cokernel.π ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α))
          e.hom (e.inv ≫ v)).trans
        ((congrArg (fun k =>
            cokernel.π ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α) ≫ k)
          hCancel).trans (hv.trans hQ.symm))))

/-- The relative augmentation is a quasi-isomorphism, by the actual cokernel short exact square. -/
theorem simplexRelativeTotalAugmentation_quasiIso {Z Z' B : SSet.{w}}
    {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') [Mono u] (hu : u ≫ q = p) :
    QuasiIso (simplexRelativeTotalAugmentation R u hu) := by
  let α := simplexPullbackDiagramMap u hu
  let a := (bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α
  let b := SSet.chainComplexMap u R
  let : Mono a := simplexTotalMap_mono R u hu
  let P : SSetPair.{w} := SSetPair.of u
  let : Mono b := inferInstanceAs (Mono (SSet.chainComplexMap P.hom R))
  let F := ShortComplex.cokernelSequenceFunctor (C := ChainComplex AddCommGrpCat.{w} ℕ)
  let s : Arrow.mk a ⟶ Arrow.mk b := Arrow.homMk (simplexTotalAugmentation R p)
    (simplexTotalAugmentation R q) (simplexTotalAugmentation_naturality R u hu).symm
  let φ : F.obj (Arrow.mk a) ⟶ F.obj (Arrow.mk b) := F.map s
  let : Mono (Arrow.mk a).hom := by
    change Mono a
    infer_instance
  let : Mono (Arrow.mk b).hom := by
    change Mono b
    infer_instance
  have hA : (F.obj (Arrow.mk a)).ShortExact :=
    ShortComplex.cokernelSequence_shortExact (Arrow.mk a)
  have hB : (F.obj (Arrow.mk b)).ShortExact :=
    ShortComplex.cokernelSequence_shortExact (Arrow.mk b)
  have hLeft : QuasiIso φ.τ₁ := simplexTotalAugmentation_quasiIso R p
  have hRight : QuasiIso φ.τ₂ := simplexTotalAugmentation_quasiIso R q
  have hCoker : QuasiIso φ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hA hB hLeft hRight
  change QuasiIso
    (cokernel.map a b (simplexTotalAugmentation R p)
      (simplexTotalAugmentation R q) (simplexTotalAugmentation_naturality R u hu)) at hCoker
  let : QuasiIso
      (cokernel.map a b (simplexTotalAugmentation R p)
        (simplexTotalAugmentation R q) (simplexTotalAugmentation_naturality R u hu)) := hCoker
  change QuasiIso ((bkRelativeCoefficientTotalIso R α).inv ≫ _)
  infer_instance

/-- Ordinary homology isomorphism makes the actual relative total acyclic. -/
theorem simplexRelativeCoefficientTotal_acyclic_of_homology_isIso {Z Z' B : SSet.{w}}
    {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') [Mono u] (hu : u ≫ q = p)
    (h : ∀ n : ℕ, IsIso (SSet.homologyMap u R n)) :
    (simplexRelativeCoefficientTotal R u hu).Acyclic := by
  let P : SSetPair.{w} := SSetPair.of u
  let : Mono (SSet.chainComplexMap u R) :=
    inferInstanceAs (Mono (SSet.chainComplexMap P.hom R))
  have hChain : QuasiIso (SSet.chainComplexMap u R) :=
    (_root_.quasiIso_iff _).mpr (fun n =>
      (_root_.quasiIsoAt_iff_isIso_homologyMap _ n).mpr (h n))
  have hOrdinary :=
    (HomologicalComplex.quasiIso_iff_acyclic_cokernel (SSet.chainComplexMap u R)).mp hChain
  let : QuasiIso (simplexRelativeTotalAugmentation R u hu) :=
    simplexRelativeTotalAugmentation_quasiIso R u hu
  intro n
  exact (_root_.exactAt_iff_of_quasiIsoAt (simplexRelativeTotalAugmentation R u hu) n).mpr
    (hOrdinary n)

end SSet
