/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellQuotientCellPresentation
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellSphericalGenerators
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularRelativeComparison
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularPathDeckNaturality
public import Mathlib.CategoryTheory.Conj
public import MathlibExt.AlgebraicTopology.PlusConstruction.RegularQuotientGroupRing
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.RealizationSingular
public import MathlibExt.AlgebraicTopology.SimplicialSet.ChangeOfCategory
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Hom
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CellFamilyFundamentalGroupoid
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverPullbackCopies
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverPullbackComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCellFamilyCopies
public import MathlibExt.AlgebraicTopology.SimplicialSet.PullbackPushout
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakEquivalenceChains
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import MathlibExt.Algebra.Homology.ExactFunctorConnecting
public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology.CWComplex
open scoped Simplicial

universe u v w

attribute [local instance] TopCat.toSSet_obj_kanComplex

namespace OriginalNativeRelativeBasis

private theorem singularChainMap_quasiIso {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.weakHomotopyEquivalences f) (R : AddCommGrpCat.{u}) :
    QuasiIso (((singularChainComplexFunctor AddCommGrpCat.{u}).obj R).map f) := by
  have hSing : SSet.realizationWeakEquivalences (TopCat.toSSet.map f) :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence (TopCat.toSSet.map f)).mp
      ((TopCat.mem_weakHomotopyEquivalences_iff f).mp hf)
  exact SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp hSing R

private theorem relativeSingularChainMap_quasiIso {A B : TopPair.{u}} (f : A ⟶ B)
    (hAmbient : TopCat.weakHomotopyEquivalences (TopPair.Hom.fst f))
    (hOld : TopCat.weakHomotopyEquivalences (TopPair.Hom.snd f)) (R : AddCommGrpCat.{u}) :
    QuasiIso ((relativeSingularChainFunctor AddCommGrpCat.{u} R).map f) := by
  let S := singularPairShortComplexFunctor AddCommGrpCat.{u} R
  let ψ : S.obj A ⟶ S.obj B := S.map f
  have hL : QuasiIso ψ.τ₁ := singularChainMap_quasiIso (TopPair.Hom.snd f) hOld R
  have hR : QuasiIso ψ.τ₂ := singularChainMap_quasiIso (TopPair.Hom.fst f) hAmbient R
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (singularPairShortComplex_shortExact AddCommGrpCat.{u} R A)
    (singularPairShortComplex_shortExact AddCommGrpCat.{u} R B) hL hR

private def nativeRelativeUnitArrow (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    Arrow.mk (SSet.chainComplexMap (LoopCellPulledSimplicialModel.nativePair X x P).hom R) ⟶
      Arrow.mk (((singularChainComplexFunctor AddCommGrpCat.{u}).obj R).map
        (LoopCellSphericalGenerators.liftedPair X x P).map) := by
  let E := LoopCellSphericalGenerators.nativePullback X x P
  let V := LoopCellSphericalGenerators.nativeCover X x P
  let i : E ⟶ V := LoopCellSphericalGenerators.nativePullbackToCover X x P
  let F : SSet.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
    (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  let a := sSetTopAdj.unit.app E
  let b := sSetTopAdj.unit.app V
  let j := TopCat.toSSet.map (SSet.toTop.map i)
  have hUnit : i ≫ b = a ≫ j := sSetTopAdj.unit.naturality i
  have hSquare : F.map a ≫ F.map j = F.map i ≫ F.map b :=
    (F.map_comp a j).symm.trans ((congrArg F.map hUnit.symm).trans (F.map_comp i b))
  exact Arrow.homMk (F.map a) (F.map b) hSquare

private theorem originalInclusion_mono (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : Mono (LoopCellAttachment.inclusion X x P) :=
  (TopCat.mono_iff_injective _).mpr (LoopCellAttachment.inclusion_isClosedEmbedding X x P).injective

private def stockRelativeCokerIso {C : Type v} [Category C] [Abelian C]
    [HasCoproducts.{u} C] (A : SSetPair.{u}) (R : C) :
    A.chainComplex R ≅ cokernel (SSet.chainComplexMap A.hom R) :=
  CokernelCofork.mapIsoOfIsColimit
    (cc := A.cokernelCoforkChainComplex R)
    (cc' := CokernelCofork.ofπ (cokernel.π (SSet.chainComplexMap A.hom R))
      (cokernel.condition (SSet.chainComplexMap A.hom R)))
    (A.isColimitCokernelCoforkChainComplex R)
    (cokernelIsCokernel (SSet.chainComplexMap A.hom R)) (Iso.refl _)

private theorem stockRelativeCokerIso_projection {C : Type v} [Category C] [Abelian C]
    [HasCoproducts.{u} C] (A : SSetPair.{u}) (R : C) :
    A.chainComplexπ R ≫ (stockRelativeCokerIso A R).hom =
      cokernel.π (SSet.chainComplexMap A.hom R) := by
  let cc := CokernelCofork.ofπ (cokernel.π (SSet.chainComplexMap A.hom R))
    (cokernel.condition (SSet.chainComplexMap A.hom R))
  change (A.cokernelCoforkChainComplex R).π ≫
    CokernelCofork.mapOfIsColimit (A.isColimitCokernelCoforkChainComplex R) cc
      (𝟙 (Arrow.mk (SSet.chainComplexMap A.hom R))) = cc.π
  exact (CokernelCofork.π_mapOfIsColimit
    (A.isColimitCokernelCoforkChainComplex R) cc
      (𝟙 (Arrow.mk (SSet.chainComplexMap A.hom R)))).trans (Category.id_comp cc.π)

private def forgetRelativeChainIso (A : SSetPair.{u}) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (A.chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))) ≅
        A.chainComplex (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let eM := stockRelativeCokerIso A R
  let eA := stockRelativeCokerIso A (singularIntegralCoefficients : AddCommGrpCat.{u})
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  exact F.mapIso eM ≪≫ (SSetPair.mapRelativeChainComplexFunctorIso U R).app A ≪≫ eA.symm

private theorem stockRelativeCokerIso_inverse_projection {C : Type v} [Category C] [Abelian C]
    [HasCoproducts.{u} C] (A : SSetPair.{u}) (R : C) :
    cokernel.π (SSet.chainComplexMap A.hom R) ≫ (stockRelativeCokerIso A R).inv =
      A.chainComplexπ R := by
  let e := stockRelativeCokerIso A R
  let q := A.chainComplexπ R
  let q' := cokernel.π (SSet.chainComplexMap A.hom R)
  have h : q ≫ e.hom = q' := stockRelativeCokerIso_projection A R
  exact (congrArg (fun t => t ≫ e.inv) h).symm.trans
    ((Category.assoc q e.hom e.inv).trans
      ((congrArg (fun t => q ≫ t) e.hom_inv_id).trans (Category.comp_id q)))

private theorem forgetRelativeChainIso_projection (A : SSetPair.{u}) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (A.chainComplexπ (ModuleCat.of ℤ (ULift.{u} ℤ))) ≫
      (forgetRelativeChainIso A).hom =
        (SSet.mapChainComplexFunctorIso
          (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
          (ModuleCat.of ℤ (ULift.{u} ℤ))).hom.app A.fst ≫
          A.chainComplexπ (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let eM := stockRelativeCokerIso A R
  let eA := stockRelativeCokerIso A (singularIntegralCoefficients : AddCommGrpCat.{u})
  let eR := (SSetPair.mapRelativeChainComplexFunctorIso U R).app A
  let eV := (SSet.mapChainComplexFunctorIso U R).app A.fst
  let qM := A.chainComplexπ R
  let qA := A.chainComplexπ (singularIntegralCoefficients : AddCommGrpCat.{u})
  let kM := cokernel.π (SSet.chainComplexMap A.hom R)
  let kA := cokernel.π (SSet.chainComplexMap A.hom
    (singularIntegralCoefficients : AddCommGrpCat.{u}))
  have h1 : F.map qM ≫ F.map eM.hom = F.map kM :=
    (F.map_comp qM eM.hom).symm.trans
      (congrArg F.map (stockRelativeCokerIso_projection A R))
  have h2 : F.map kM ≫ eR.hom = eV.hom ≫ kA :=
    (SSetPair.mapRelativeChainComplexFunctorIso_hom_app_comp_π U R A).symm
  have h3 : kA ≫ eA.inv = qA :=
    stockRelativeCokerIso_inverse_projection A _
  change F.map qM ≫ (F.map eM.hom ≫ eR.hom ≫ eA.inv) = eV.hom ≫ qA
  exact (Category.assoc (F.map qM) (F.map eM.hom) (eR.hom ≫ eA.inv)).symm.trans
    ((congrArg (fun t => t ≫ eR.hom ≫ eA.inv) h1).trans
      ((Category.assoc (F.map kM) eR.hom eA.inv).symm.trans
        ((congrArg (fun t => t ≫ eA.inv) h2).trans
          ((Category.assoc eV.hom kA eA.inv).trans
            (congrArg (fun t => eV.hom ≫ t) h3)))))

private theorem stockRelativeQuotient_transport_coefficients {C : Type v}
    [Category.{w} C] [Abelian C]
    [HasCoproducts.{u} C] (A B : SSetPair.{u}) (h : A = B) (R : C) :
    A.chainComplexπ R ≫ eqToHom (congrArg (fun A : SSetPair.{u} => A.chainComplex R) h) =
      eqToHom (congrArg (fun A : SSetPair.{u} => A.fst.chainComplex R) h) ≫ B.chainComplexπ R := by
  cases h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem stockRelativeQuotient_transport (A B : SSetPair.{u}) (h : A = B)
    (R : AddCommGrpCat.{u}) :
    A.chainComplexπ R ≫ eqToHom (congrArg (fun A : SSetPair.{u} => A.chainComplex R) h) =
      eqToHom (congrArg (fun A : SSetPair.{u} => A.fst.chainComplex R) h) ≫ B.chainComplexπ R :=
  stockRelativeQuotient_transport_coefficients A B h R

private theorem forgetRelativeChainIso_naturality {A B : SSetPair.{u}} (φ : A ⟶ B) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (SSetPair.chainComplexMap φ (ModuleCat.of ℤ (ULift.{u} ℤ))) ≫
        (forgetRelativeChainIso B).hom =
      (forgetRelativeChainIso A).hom ≫
        SSetPair.chainComplexMap φ (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let CA := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})
  let CM := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj R
  let eA := forgetRelativeChainIso A
  let eB := forgetRelativeChainIso B
  let vA := (SSet.mapChainComplexFunctorIso U R).app A.fst
  let vB := (SSet.mapChainComplexFunctorIso U R).app B.fst
  let qA := A.chainComplexπ R
  let qB := B.chainComplexπ R
  let qA' := A.chainComplexπ (singularIntegralCoefficients : AddCommGrpCat.{u})
  let qB' := B.chainComplexπ (singularIntegralCoefficients : AddCommGrpCat.{u})
  let m := SSetPair.chainComplexMap φ R
  let n := SSetPair.chainComplexMap φ (singularIntegralCoefficients : AddCommGrpCat.{u})
  let a := CM.map φ.hom.right
  let b := CA.map φ.hom.right
  have hA : F.map qA ≫ eA.hom = vA.hom ≫ qA' := forgetRelativeChainIso_projection A
  have hB : F.map qB ≫ eB.hom = vB.hom ≫ qB' := forgetRelativeChainIso_projection B
  have hInv : (F.map qA ≫ eA.hom) ≫ eA.inv = F.map qA :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => F.map qA ≫ f) eA.hom_inv_id).trans (Category.comp_id _))
  have hQ : F.map qA = (vA.hom ≫ qA') ≫ eA.inv :=
    hInv.symm.trans (congrArg (fun f => f ≫ eA.inv) hA)
  have hEpi : Epi ((vA.hom ≫ qA') ≫ eA.inv) := by infer_instance
  let : Epi (F.map qA) := hQ.symm ▸ hEpi
  have hM : F.map qA ≫ F.map m = F.map a ≫ F.map qB :=
    (F.map_comp qA m).symm.trans
      ((congrArg F.map
          (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality φ).symm).trans
        (F.map_comp a qB))
  have hN : b ≫ qB' = qA' ≫ n :=
    ((SSetPair.chainComplexFunctorπ AddCommGrpCat.{u}).app
      (singularIntegralCoefficients : AddCommGrpCat.{u})).naturality φ
  have hV : F.map a ≫ vB.hom = vA.hom ≫ b :=
    (SSet.mapChainComplexFunctorIso U R).hom.naturality φ.hom.right
  apply (cancel_epi (F.map qA)).mp
  have hL : F.map qA ≫ (F.map m ≫ eB.hom) = (vA.hom ≫ qA') ≫ n :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ eB.hom) hM).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => F.map a ≫ f) hB).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun f => f ≫ qB') hV).trans
                ((Category.assoc _ _ _).trans
                  ((congrArg (fun f => vA.hom ≫ f) hN).trans (Category.assoc _ _ _).symm)))))))
  have hR : F.map qA ≫ (eA.hom ≫ n) = (vA.hom ≫ qA') ≫ n :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ n) hA)
  exact hL.trans hR.symm

private abbrev pairedCoverAtVertex {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (y : Y _⦋0⦌) : SSetPair.{u} :=
  SSetPair.of (pullback.snd f (SSet.KanComplex.nativeCoverProjection Y y))

private def pairedDeckAtVertex {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) :
    pairedCoverAtVertex f y ⟶ pairedCoverAtVertex f y :=
  SSetPair.ofHom (SSet.KanComplex.nativeCoverDeckMap a)
    (SSet.KanComplex.nativeRegularPullbackDeckMap f y a)
      (SSet.KanComplex.nativeRegularPullbackDeckMap_snd f y a)

private theorem pairedDeck_point_transport {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    {y z : Y _⦋0⦌} (h : y = z) (a : End (SSet.FundamentalGroupoid.mk y)) :
    pairedDeckAtVertex f y a ≫ eqToHom (congrArg (pairedCoverAtVertex f) h) =
      eqToHom (congrArg (pairedCoverAtVertex f) h) ≫
        pairedDeckAtVertex f z ((eqToIso (congrArg SSet.FundamentalGroupoid.mk h)).conj a) := by
  cases h
  simp only [eqToHom_refl, eqToIso_refl, Iso.refl_conj, Category.comp_id, Category.id_comp]

end OriginalNativeRelativeBasis

public section

namespace AlgebraicTopology.LoopCellNativeRelativeBasis

attribute [local instance] OriginalNativeRelativeBasis.originalInclusion_mono

local instance originalLoopInclusionMono (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : Mono (LoopCellAttachment.inclusion X x P) :=
  OriginalNativeRelativeBasis.originalInclusion_mono X x P

/-- The actual relative-chain map from the pulled realization to the SAME original native cover. -/
abbrev nativeComparisonChainMap (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    (relativeSingularChainFunctor AddCommGrpCat.{u} R).obj
        (LoopCellQuotientCellPresentation.realizedPair X x P) ⟶
      (relativeSingularChainFunctor AddCommGrpCat.{u} R).obj
        (LoopCellSphericalGenerators.liftedPair X x P) :=
  (relativeSingularChainFunctor AddCommGrpCat.{u} R).map
    (LoopCellQuotientCellPresentation.realizedPairToCover X x P)

/-- Its quasi-isomorphism is derived from the actual weak ambient comparison and whole-old
identity. -/
theorem nativeComparisonChainMap_quasiIso (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    QuasiIso (nativeComparisonChainMap X x P R) := by
  let φ := LoopCellQuotientCellPresentation.realizedPairToCover X x P
  have hTop : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (LoopCellPulledSimplicialModel.toCover X x P)) :=
    LoopCellPulledSimplicialModel.toCover_weak X x P
  have hAmbient : TopCat.weakHomotopyEquivalences (TopPair.Hom.fst φ) :=
    Eq.mp (congrArg (fun f => TopCat.weakHomotopyEquivalences f)
      (LoopCellQuotientCellPresentation.realizedPairToCover_fst X x P)).symm hTop
  have hIdentity : TopCat.weakHomotopyEquivalences
      (𝟙 (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P))) :=
    TopCat.weakHomotopyEquivalences.id_mem _
  have hOld : TopCat.weakHomotopyEquivalences (TopPair.Hom.snd φ) :=
    Eq.mp (congrArg (fun f => TopCat.weakHomotopyEquivalences f)
      (LoopCellQuotientCellPresentation.realizedPairToCover_snd X x P)).symm hIdentity
  exact OriginalNativeRelativeBasis.relativeSingularChainMap_quasiIso φ hAmbient hOld R

/-- The actual relative homology comparison to the SAME native pair in every degree. -/
def nativeComparisonHomologyIso (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) (n : ℕ) :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).obj
        (LoopCellQuotientCellPresentation.realizedPair X x P) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).obj
        (LoopCellSphericalGenerators.liftedPair X x P) := by
  letI : QuasiIso (nativeComparisonChainMap X x P R) := nativeComparisonChainMap_quasiIso X x P R
  letI : IsIso ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map
      (LoopCellQuotientCellPresentation.realizedPairToCover X x P)) := by
    change IsIso (HomologicalComplex.homologyMap (nativeComparisonChainMap X x P R) n)
    exact (_root_.quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance
  exact asIso ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map
    (LoopCellQuotientCellPresentation.realizedPairToCover X x P))

/-- The whole actual quotient law is retained by this comparison. -/
theorem nativeComparisonHomologyIso_projection (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) (n : ℕ) :
    singularHomologyPairQuotientMap AddCommGrpCat.{u} R
        (LoopCellQuotientCellPresentation.realizedPair X x P) n ≫
      (nativeComparisonHomologyIso X x P R n).hom =
        ((singularHomologyFunctor AddCommGrpCat.{u} n).obj R).map
          (SSet.toTop.map (LoopCellPulledSimplicialModel.toCover X x P)) ≫
        singularHomologyPairQuotientMap AddCommGrpCat.{u} R
          (LoopCellSphericalGenerators.liftedPair X x P) n := by
  let φ := LoopCellQuotientCellPresentation.realizedPairToCover X x P
  have hHom : (nativeComparisonHomologyIso X x P R n).hom =
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map φ := by rfl
  have hNat := singularHomologyPairQuotientMap_naturality AddCommGrpCat.{u} R n φ
  exact (congrArg (fun f => singularHomologyPairQuotientMap AddCommGrpCat.{u} R
      (LoopCellQuotientCellPresentation.realizedPair X x P) n ≫ f) hHom).trans
    (hNat.trans (congrArg (fun f =>
      ((singularHomologyFunctor AddCommGrpCat.{u} n).obj R).map f ≫
        singularHomologyPairQuotientMap AddCommGrpCat.{u} R
          (LoopCellSphericalGenerators.liftedPair X x P) n)
      (LoopCellQuotientCellPresentation.realizedPairToCover_fst X x P)))

/-- The complete actual coefficient basis on the ORIGINAL realized native covering pair. -/
def nativeCoefficientBasisIso (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u}) :
    (∐ fun _ : LoopCellQuotientCellPresentation.labels X x P => R) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj
        (LoopCellSphericalGenerators.liftedPair X x P) :=
  LoopCellQuotientCellPresentation.relativeCoefficientBasisIso X x P R ≪≫
    nativeComparisonHomologyIso X x P R 2

/-- The actual relative realization-unit chain map, using the SAME native pair and quotient. -/
def nativeRelativeUnitChainMap (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    (LoopCellPulledSimplicialModel.nativePair X x P).chainComplex R ⟶
      (relativeSingularChainFunctor AddCommGrpCat.{u} R).obj
        (LoopCellSphericalGenerators.liftedPair X x P) := by
  let S := (singularPairShortComplexFunctor AddCommGrpCat.{u} R).obj
    (LoopCellSphericalGenerators.liftedPair X x P)
  exact CokernelCofork.mapOfIsColimit
    ((LoopCellPulledSimplicialModel.nativePair X x P).isColimitCokernelCoforkChainComplex R)
    (CokernelCofork.ofπ S.g S.zero)
    (OriginalNativeRelativeBasis.nativeRelativeUnitArrow X x P R)

/-- Its entire quotient square is the original realization unit on the native ambient space. -/
theorem nativeRelativeUnitChainMap_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    (LoopCellPulledSimplicialModel.nativePair X x P).chainComplexπ R ≫
      nativeRelativeUnitChainMap X x P R =
        SSet.chainComplexMap (sSetTopAdj.unit.app
            (LoopCellSphericalGenerators.nativeCover X x P)) R ≫
          relativeSingularChainQuotient AddCommGrpCat.{u} R
            (LoopCellSphericalGenerators.liftedPair X x P) := by
  let S := (singularPairShortComplexFunctor AddCommGrpCat.{u} R).obj
    (LoopCellSphericalGenerators.liftedPair X x P)
  exact CokernelCofork.π_mapOfIsColimit
    ((LoopCellPulledSimplicialModel.nativePair X x P).isColimitCokernelCoforkChainComplex R)
    (CokernelCofork.ofπ S.g S.zero)
    (OriginalNativeRelativeBasis.nativeRelativeUnitArrow X x P R)

/-- The actual relative unit is a quasi-isomorphism by both actual unit weak equivalences. -/
theorem nativeRelativeUnitChainMap_quasiIso (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    QuasiIso (nativeRelativeUnitChainMap X x P R) := by
  let A := LoopCellPulledSimplicialModel.nativePair X x P
  let S := (singularPairShortComplexFunctor AddCommGrpCat.{u} R).obj
    (LoopCellSphericalGenerators.liftedPair X x P)
  let a := SSet.chainComplexMap (sSetTopAdj.unit.app A.left) R
  let b := SSet.chainComplexMap (sSetTopAdj.unit.app A.right) R
  let φ := OriginalNativeRelativeBasis.nativeRelativeUnitArrow X x P R
  let ψ : A.chainComplexShortComplex R ⟶ S :=
    ShortComplex.homMk a b (nativeRelativeUnitChainMap X x P R) φ.w
      (nativeRelativeUnitChainMap_projection X x P R).symm
  have hLeft : QuasiIso ψ.τ₁ :=
    SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp
      (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences A.left) R
  have hRight : QuasiIso ψ.τ₂ :=
    SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp
      (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences A.right) R
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (A.shortExact_chainComplexShortComplex R)
    (singularPairShortComplex_shortExact AddCommGrpCat.{u} R
      (LoopCellSphericalGenerators.liftedPair X x P)) hLeft hRight

/-- Relative native simplicial homology identifies through its ACTUAL unit with the same realized
pair. -/
def nativeRelativeUnitHomologyIso (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) (n : ℕ) :
    (LoopCellPulledSimplicialModel.nativePair X x P).homology R n ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).obj
        (LoopCellSphericalGenerators.liftedPair X x P) := by
  let a := nativeRelativeUnitChainMap X x P R
  let m : (LoopCellPulledSimplicialModel.nativePair X x P).homology R n ⟶
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).obj
        (LoopCellSphericalGenerators.liftedPair X x P) := HomologicalComplex.homologyMap a n
  have hQ : QuasiIso a := nativeRelativeUnitChainMap_quasiIso X x P R
  have hIso : IsIso m := (_root_.quasiIsoAt_iff_isIso_homologyMap a n).mp (hQ.quasiIsoAt n)
  exact @asIso _ _ _ _ m hIso

private theorem nativeRelativeUnitHomologyIso_hom (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) (n : ℕ) :
    (nativeRelativeUnitHomologyIso X x P R n).hom =
      HomologicalComplex.homologyMap (nativeRelativeUnitChainMap X x P R) n := by rfl

/-- The whole absolute-to-relative homology quotient is calibrated by the SAME native unit. -/
theorem nativeRelativeUnitHomologyIso_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) (n : ℕ) :
    (LoopCellPulledSimplicialModel.nativePair X x P).homologyπ R n ≫
      (nativeRelativeUnitHomologyIso X x P R n).hom =
        SSet.homologyMap (sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P)) R n ≫
          singularHomologyPairQuotientMap AddCommGrpCat.{u} R
            (LoopCellSphericalGenerators.liftedPair X x P) n := by
  let H : ChainComplex AddCommGrpCat.{u} ℕ ⥤ AddCommGrpCat.{u} :=
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n
  let q := (LoopCellPulledSimplicialModel.nativePair X x P).chainComplexπ R
  let a := nativeRelativeUnitChainMap X x P R
  let b :=
      SSet.chainComplexMap (sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P)) R
  let q' := relativeSingularChainQuotient AddCommGrpCat.{u} R
      (LoopCellSphericalGenerators.liftedPair X x P)
  rw [nativeRelativeUnitHomologyIso_hom]
  change H.map q ≫ H.map a = H.map b ≫ H.map q'
  exact (H.map_comp q a).symm.trans
    ((congrArg H.map (nativeRelativeUnitChainMap_projection X x P R)).trans (H.map_comp b q'))

/-- The ENTIRE native simplicial relative coefficient basis uses the SAME original unit
comparison. -/
def nativeSimplicialCoefficientBasisIso (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u}) :
    (∐ fun _ : LoopCellQuotientCellPresentation.labels X x P => R) ≅
      (LoopCellPulledSimplicialModel.nativePair X x P).homology R 2 :=
  nativeCoefficientBasisIso X x P R ≪≫ (nativeRelativeUnitHomologyIso X x P R 2).symm

/-- Each complete native coefficient summand is its SAME actual whole labelled disk-pair class. -/
theorem nativeCoefficientBasisIso_ι (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u})
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) i ≫
        (nativeCoefficientBasisIso X x P R).hom =
      (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u} R 2).hom ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map
          (LoopCellQuotientCellPresentation.cellPairToCover X x P i) := by
  let H : TopPair.{u} ⥤ AddCommGrpCat.{u} := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  let c := LoopCellQuotientCellPresentation.cellPair X x P i
  let f := LoopCellQuotientCellPresentation.realizedPairToCover X x P
  let g := (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u} R 2).hom
  let b := LoopCellQuotientCellPresentation.relativeCoefficientBasisIso X x P R
  let j := Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) i
  have h : j ≫ b.hom = g ≫ H.map c :=
    LoopCellQuotientCellPresentation.relativeCoefficientBasisIso_ι X x P R i
  change j ≫ (b.hom ≫ H.map f) = g ≫ H.map
    (LoopCellQuotientCellPresentation.cellPairToCover X x P i)
  exact (Category.assoc j b.hom (H.map f)).symm.trans
    ((congrArg (fun t => t ≫ H.map f) h).trans
      ((Category.assoc g (H.map c) (H.map f)).trans
        ((congrArg (fun t => g ≫ t) (H.map_comp c f).symm).trans
          (congrArg (fun t => g ≫ H.map t)
            (LoopCellQuotientCellPresentation.cellPairToCover_eq X x P i).symm))))

/-- The actual native basis retains its exact noncommutative LEFT deck law at every coefficient. -/
theorem nativeCoefficientBasisIso_deck (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u})
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (q*r,p) ≫
        (nativeCoefficientBasisIso X x P R).hom =
      (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (r,p) ≫
        (nativeCoefficientBasisIso X x P R).hom) ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map
            (LoopCellQuotientCellPresentation.nativeDeckPair X x P q) := by
  let H : TopPair.{u} ⥤ AddCommGrpCat.{u} := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  let g := (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u} R 2).hom
  let c := LoopCellQuotientCellPresentation.cellPairToCover X x P (r,p)
  let d := LoopCellQuotientCellPresentation.nativeDeckPair X x P q
  have h : H.map (LoopCellQuotientCellPresentation.cellPairToCover X x P (q*r,p)) =
      H.map c ≫ H.map d :=
    (congrArg H.map (LoopCellQuotientCellPresentation.cellPairToCover_deck X x P q r p)).trans
      (H.map_comp c d)
  exact (nativeCoefficientBasisIso_ι X x P R (q*r,p)).trans
    ((congrArg (fun t => g ≫ t) h).trans
      ((Category.assoc g (H.map c) (H.map d)).symm.trans
        (congrArg (fun t => t ≫ H.map d) (nativeCoefficientBasisIso_ι X x P R (r,p)).symm)))

/-- The original integral native-cover relative homology group. -/
abbrev nativeHomologyTwo (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) : AddCommGrpCat.{u} :=
  (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj
    (LoopCellSphericalGenerators.liftedPair X x P)

/-- The actual deck endomorphism representation on native relative homology. -/
def nativeDeckRepresentation (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u}) :
    FundamentalGroup X x ⧸ P →* AddMonoid.End (nativeHomologyTwo X x P R) where
  toFun q := ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map
    (LoopCellQuotientCellPresentation.nativeDeckPair X x P q)).hom
  map_one' := by
    ext a
    let H := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
    exact ConcreteCategory.congr_hom
      ((congrArg H.map (LoopCellQuotientCellPresentation.nativeDeckPair_one X x P)).trans
        (H.map_id _)) a
  map_mul' q r := by
    ext a
    let H := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
    exact ConcreteCategory.congr_hom
      ((congrArg H.map (LoopCellQuotientCellPresentation.nativeDeckPair_mul X x P q r)).trans
        (H.map_comp (LoopCellQuotientCellPresentation.nativeDeckPair X x P r)
          (LoopCellQuotientCellPresentation.nativeDeckPair X x P q))) a

/-- The original quotient-group ring. No commutativity of its quotient group is assumed. -/
abbrev quotientGroupRing (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) := MonoidAlgebra ℤ (FundamentalGroup X x ⧸ P)

/-- Linearizing the ACTUAL deck representation gives the genuine quotient-ring action. -/
def nativeDeckRingHom (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u}) :
    quotientGroupRing X x P →+* AddMonoid.End (nativeHomologyTwo X x P R) :=
  MonoidAlgebra.liftNCRingHom
    (Int.castRingHom (AddMonoid.End (nativeHomologyTwo X x P R)))
    (nativeDeckRepresentation X x P R)
    (fun z q => Int.cast_commute z (nativeDeckRepresentation X x P R q))

/-- The computed quotient-ring module structure on the SAME native relative group. -/
def nativeDeckModule (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u}) :
    Module (quotientGroupRing X x P) (nativeHomologyTwo X x P R) :=
  Module.compHom (nativeHomologyTwo X x P R) (nativeDeckRingHom X x P R)

/-- Every ring basis element acts by the actual LEFT deck map with its original integral
coefficient. -/
theorem nativeDeckModule_single (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u})
    (q : FundamentalGroup X x ⧸ P) (z : ℤ) (a : nativeHomologyTwo X x P R) :
    letI := nativeDeckModule X x P R
    (MonoidAlgebra.single q z : quotientGroupRing X x P) • a =
      z • nativeDeckRepresentation X x P R q a := by
  let := nativeDeckModule X x P R
  have h : nativeDeckRingHom X x P R (MonoidAlgebra.single q z) =
      (z : AddMonoid.End (nativeHomologyTwo X x P R)) * nativeDeckRepresentation X x P R q :=
    MonoidAlgebra.liftNCRingHom_single
      (Int.castRingHom (AddMonoid.End (nativeHomologyTwo X x P R)))
      (nativeDeckRepresentation X x P R) _ q z
  change nativeDeckRingHom X x P R (MonoidAlgebra.single q z) a = _
  exact (congrArg (fun f : AddMonoid.End (nativeHomologyTwo X x P R) => f a) h).trans (by
    change (z : AddMonoid.End (nativeHomologyTwo X x P R))
      (nativeDeckRepresentation X x P R q a) = z • nativeDeckRepresentation X x P R q a
    rw [AddMonoid.End.intCast_def]
    rfl)

/-- The SAME original integral generator at the literal quotient/cell label. -/
def nativeGenerator (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
      (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
    (nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).hom)
      (ULift.up (1 : ℤ))

/-- These actual generators obey LEFT multiplication under the genuine deck action. -/
theorem nativeGenerator_deck (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    nativeDeckRepresentation X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) q
      (nativeGenerator X x P (r,p)) = nativeGenerator X x P (q*r,p) := by
  exact (ConcreteCategory.congr_hom
    (nativeCoefficientBasisIso_deck X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) q r p)
      (ULift.up (1 : ℤ))).symm

/-- The unit-column map from the actual free quotient-ring module on ALL members of P. -/
def nativeLambdaBasisMap (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    (P →₀ quotientGroupRing X x P) →ₗ[quotientGroupRing X x P]
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  exact Finsupp.linearCombination (quotientGroupRing X x P)
      (fun p : P => nativeGenerator X x P (1,p))

/-- The entire original coefficient/label formula for every column of this quotient-ring map. -/
theorem nativeLambdaBasisMap_single (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    nativeLambdaBasisMap X x P (Finsupp.single p (MonoidAlgebra.single q z)) =
      z • nativeGenerator X x P (q,p) := by
  let := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  have h := Finsupp.linearCombination_single
    (R := quotientGroupRing X x P) (v := fun p : P => nativeGenerator X x P (1,p))
      (MonoidAlgebra.single q z) p
  exact h.trans
    ((nativeDeckModule_single X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
      q z (nativeGenerator X x P (1,p))).trans
        (congrArg (fun a => z • a) (by
          simpa only [mul_one] using nativeGenerator_deck X x P q 1 p)))

/-- The actual integral free-group coordinate of the complete native basis. -/
def nativeIntegralFreeIso (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    AddCommGrpCat.of (FreeAbelianGroup (LoopCellQuotientCellPresentation.labels X x P)) ≅
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  (CategoryTheory.integralPathBasisIso (LoopCellQuotientCellPresentation.labels X x P)).symm ≪≫
    nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})

/-- Every free generator is its exact original native relative cell class. -/
theorem nativeIntegralFreeIso_of (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (nativeIntegralFreeIso X x P).hom (FreeAbelianGroup.of i) = nativeGenerator X x P i := by
  let I := LoopCellQuotientCellPresentation.labels X x P
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let e := CategoryTheory.integralPathBasisIso I
  let b := nativeCoefficientBasisIso X x P R
  let v := (Sigma.ι (fun _ : I => R) i) (ULift.up (1 : ℤ))
  have hι : Sigma.ι (fun _ : I => R) i ≫ e.hom =
      (CategoryTheory.integralPathBasisCofan I).inj i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct (fun _ : I => R))
      (CategoryTheory.integralPathBasisCofanIsColimit I) ⟨i⟩
  have hValue : e.hom v = FreeAbelianGroup.of i :=
    (ConcreteCategory.congr_hom hι (ULift.up (1 : ℤ))).trans
      ((CategoryTheory.integralPathBasisCofan_inj I i (ULift.up (1 : ℤ))).trans (one_zsmul _))
  have hInverse : e.inv (FreeAbelianGroup.of i) = v :=
    (congrArg e.inv hValue.symm).trans (ConcreteCategory.congr_hom e.hom_inv_id v)
  exact congrArg b.hom hInverse

/-- The complete underlying integer-coordinate equivalence is derived from the actual cell basis. -/
def nativeIntegralBasisAddEquiv (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (LoopCellQuotientCellPresentation.labels X x P →₀ ℤ) ≃+
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  (FreeAbelianGroup.equivFinsupp (LoopCellQuotientCellPresentation.labels X x P)).symm.trans
    (nativeIntegralFreeIso X x P).addCommGroupIsoToAddEquiv

/-- Every integer coordinate maps to its exact original quotient-labelled cell class. -/
theorem nativeIntegralBasisAddEquiv_single (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (i : LoopCellQuotientCellPresentation.labels X x P) (z : ℤ) :
    nativeIntegralBasisAddEquiv X x P (Finsupp.single i z) = z • nativeGenerator X x P i := by
  let e := nativeIntegralFreeIso X x P
  have h : (FreeAbelianGroup.equivFinsupp (LoopCellQuotientCellPresentation.labels X x P)).symm
      (Finsupp.single i z) = z • FreeAbelianGroup.of i :=
    Finsupp.toFreeAbelianGroup_single i z
  exact (congrArg e.hom h).trans
    ((e.hom.hom.map_zsmul z (FreeAbelianGroup.of i)).trans
      (congrArg (fun a => z • a) (nativeIntegralFreeIso_of X x P i)))

/-- Flatten the actual quotient-ring columns to the literal (q,p) integer coordinates. -/
def quotientRingCoordinates (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (P →₀ quotientGroupRing X x P) ≃+ (LoopCellQuotientCellPresentation.labels X x P →₀ ℤ) :=
  let e : quotientGroupRing X x P ≃+ (FundamentalGroup X x ⧸ P →₀ ℤ) :=
    MonoidAlgebra.coeffAddEquiv
  (Finsupp.mapRange.addEquiv e).trans
    (Finsupp.curryAddEquiv.symm.trans
      (Finsupp.domCongr (Equiv.prodComm P (FundamentalGroup X x ⧸ P))))

/-- Flattening retains the exact noncommutative quotient label and original P-column. -/
theorem quotientRingCoordinates_single (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x))
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    quotientRingCoordinates X x P (Finsupp.single p (MonoidAlgebra.single q z)) =
      Finsupp.single (q,p) z := by
  change Finsupp.equivMapDomain (Equiv.prodComm P (FundamentalGroup X x ⧸ P))
    ((Finsupp.mapRange
      (fun a : quotientGroupRing X x P => a.coeff) (MonoidAlgebra.coeff_zero)
      (Finsupp.single p (MonoidAlgebra.single q z))).uncurry) = Finsupp.single (q,p) z
  simp only [Finsupp.mapRange_single, MonoidAlgebra.coeff_single,
    Finsupp.uncurry_single, Finsupp.equivMapDomain_single, Equiv.prodComm_apply]
  rfl

/-- The actual quotient-ring column map is bijective on its entire original relative homology
target. -/
theorem nativeLambdaBasisMap_bijective (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    Function.Bijective (nativeLambdaBasisMap X x P) := by
  let := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let f := nativeLambdaBasisMap X x P
  let e := (quotientRingCoordinates X x P).trans (nativeIntegralBasisAddEquiv X x P)
  have h : f.toAddMonoidHom = e.toAddMonoidHom := by
    apply Finsupp.addHom_ext'
    intro p
    apply MonoidAlgebra.addMonoidHom_ext
    intro q z
    have hE : e (Finsupp.single p (MonoidAlgebra.single q z)) =
        z • nativeGenerator X x P (q,p) :=
      (congrArg (nativeIntegralBasisAddEquiv X x P)
        (quotientRingCoordinates_single X x P q p z)).trans
          (nativeIntegralBasisAddEquiv_single X x P (q,p) z)
    exact (nativeLambdaBasisMap_single X x P q p z).trans hE.symm
  have hFunction : (fun a => f a) = fun a => e a :=
    funext (fun a => congrArg (fun g => g a) h)
  exact Eq.mp (congrArg Function.Bijective hFunction.symm) e.bijective

/-- The ENTIRE actual native relative two-cell module is the free original quotient-group-ring
module on P. -/
def nativeLambdaBasisIso (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    (P →₀ quotientGroupRing X x P) ≃ₗ[quotientGroupRing X x P]
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  exact LinearEquiv.ofBijective (nativeLambdaBasisMap X x P) (nativeLambdaBasisMap_bijective X x P)

/-- The free quotient-ring basis retains every original labelled two-cell and every coefficient. -/
theorem nativeLambdaBasisIso_single (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    nativeLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z)) =
      z • nativeGenerator X x P (q,p) :=
  nativeLambdaBasisMap_single X x P q p z

/-- The genuine inverse recovers every original quotient/cell coordinate. -/
theorem nativeLambdaBasisIso_inverse_single (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    (nativeLambdaBasisIso X x P).symm (z • nativeGenerator X x P (q,p)) =
      Finsupp.single p (MonoidAlgebra.single q z) := by
  exact (congrArg (nativeLambdaBasisIso X x P).symm
      (nativeLambdaBasisIso_single X x P q p z).symm).trans
    ((nativeLambdaBasisIso X x P).symm_apply_apply _)

/-- Every coefficient of an actual integral basis column is its integer multiple of the SAME
generator. -/
theorem nativeGenerator_coefficient (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (i : LoopCellQuotientCellPresentation.labels X x P)
    (a : (singularIntegralCoefficients : AddCommGrpCat.{u})) :
    (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
      (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
        (nativeCoefficientBasisIso X x P
            (singularIntegralCoefficients : AddCommGrpCat.{u})).hom) a =
      a.down • nativeGenerator X x P i := by
  let f := Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
    (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
      (nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).hom
  have ha : a = a.down •
      (ULift.up (1 : ℤ) : (singularIntegralCoefficients : AddCommGrpCat.{u})) := by
    apply ULift.down_injective
    simp
  exact (congrArg f ha).trans (f.hom.map_zsmul a.down (ULift.up (1 : ℤ)))

/-- The SAME selected upstairs sphere has exactly the actual unit two-cell column. -/
theorem chosenSphere_unit_column (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map
            (LoopCellSphericalGenerators.liftedSphericalGenerator X x P p)) ≫
      LoopCellSphericalGenerators.relativeProjection X x P =
        Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
          (singularIntegralCoefficients : AddCommGrpCat.{u})) (1,p) ≫
            (nativeCoefficientBasisIso X x P
                (singularIntegralCoefficients : AddCommGrpCat.{u})).hom := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let H := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  let g := (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u} R 2).hom
  have hBasis : Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (1,p) ≫
      (nativeCoefficientBasisIso X x P R).hom =
        g ≫ H.map (LoopCellSphericalGenerators.liftedCharacteristicDiskPair X x P p) :=
    (nativeCoefficientBasisIso_ι X x P R (1,p)).trans
      (congrArg (fun f => g ≫ H.map f)
          (LoopCellQuotientCellPresentation.cellPairToCover_unit X x P p))
  ext a
  exact (LoopCellSphericalGenerators.liftedSphericalGenerator_value X x P p a).trans
    (ConcreteCategory.congr_hom hBasis a).symm

/-- The actual spherical attaching map for EVERY quotient label and original P-member. -/
def chosenSphericalCopy (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (classicalCellDiskPair.{u} 3).snd ⟶ (LoopCellSphericalGenerators.liftedPair X x P).fst :=
  LoopCellSphericalGenerators.liftedSphericalGenerator X x P i.2 ≫
    SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P i.1)

/-- The SAME chosen spherical family has the full identity column at EVERY coefficient and quotient
label. -/
theorem chosenSphericalCopy_column (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (chosenSphericalCopy X x P i)) ≫
      LoopCellSphericalGenerators.relativeProjection X x P =
        Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
          (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
            (nativeCoefficientBasisIso X x P
                (singularIntegralCoefficients : AddCommGrpCat.{u})).hom := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let A := LoopCellSphericalGenerators.liftedPair X x P
  let H := (singularHomologyFunctor AddCommGrpCat.{u} 2).obj R
  let Hrel := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  let g := classicalCellBoundaryHomologyTwoGenerator.{u}
  let S := LoopCellSphericalGenerators.liftedSphericalGenerator X x P i.2
  let d := LoopCellQuotientCellPresentation.nativeDeckPair X x P i.1
  let f := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P i.1)
  let q := LoopCellSphericalGenerators.relativeProjection X x P
  have hMap : H.map (chosenSphericalCopy X x P i) = H.map S ≫ H.map f := H.map_comp S f
  have hNat : H.map f ≫ q = q ≫ Hrel.map d :=
    (congrArg (fun t => H.map t ≫ q)
      (LoopCellQuotientCellPresentation.nativeDeckPair_fst X x P i.1).symm).trans
        (singularHomologyPairQuotientMap_naturality AddCommGrpCat.{u} R 2 d).symm
  have hWhole : g ≫ H.map (chosenSphericalCopy X x P i) ≫ q =
      (g ≫ H.map S ≫ q) ≫ Hrel.map d := by
    have hSq : (H.map S ≫ H.map f) ≫ q = (H.map S ≫ q) ≫ Hrel.map d :=
      (Category.assoc (H.map S) (H.map f) q).trans
        ((congrArg (fun t => H.map S ≫ t) hNat).trans
          (Category.assoc (H.map S) q (Hrel.map d)).symm)
    exact (congrArg (fun t => g ≫ t ≫ q) hMap).trans
      ((congrArg (fun t => g ≫ t) hSq).trans
        (Category.assoc g (H.map S ≫ q) (Hrel.map d)).symm)
  have hUnit := chosenSphere_unit_column X x P i.2
  have hDeck := nativeCoefficientBasisIso_deck X x P R i.1 1 i.2
  exact hWhole.trans
    ((congrArg (fun h => h ≫ Hrel.map d) hUnit).trans
      (by simpa only [mul_one] using hDeck.symm))

/-- In the ACTUAL free quotient-ring basis, every chosen spherical copy is its exact (q,p) basis
element. -/
theorem chosenSphericalCopy_basis_coordinate (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P)
    (a : (singularIntegralCoefficients : AddCommGrpCat.{u})) :
    (nativeLambdaBasisIso X x P).symm
      ((classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (chosenSphericalCopy X x P i)) ≫
          LoopCellSphericalGenerators.relativeProjection X x P) a) =
      Finsupp.single i.2 (MonoidAlgebra.single i.1 a.down) := by
  have hColumn := ConcreteCategory.congr_hom (chosenSphericalCopy_column X x P i) a
  have hValue := nativeGenerator_coefficient X x P i a
  exact (congrArg (nativeLambdaBasisIso X x P).symm (hColumn.trans hValue)).trans
    (nativeLambdaBasisIso_inverse_single X x P i.1 i.2 a.down)

/-- The computed target vertex is the literal singular vertex of the original included point. -/
theorem nativeTargetPoint_eq_original (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    LoopCellSphericalGenerators.nativeTargetPoint X x P =
      TopCat.toSSetObj₀Equiv.symm (LoopCellAttachment.inclusion X x P x) := by
  apply (TopCat.toSSetObjEquiv (LoopCellAttachment.space X x P) _).injective
  ext z
  rfl

/-- The original regular coefficient comparison uses the SAME literal paired arrow as the chosen
native pair. -/
theorem originalRegularPair_eq_native (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    TopCat.originalRegularPulledCoverPair (LoopCellAttachment.inclusion X x P)
        (LoopCellAttachment.inclusion X x P x) =
      LoopCellPulledSimplicialModel.nativePair X x P := by
  let f := TopCat.toSSet.map (LoopCellAttachment.inclusion X x P)
  let : Mono f := inferInstance
  let F : (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) _⦋0⦌ → SSetPair.{u} :=
    fun y => SSetPair.of (pullback.snd f
      (SSet.KanComplex.nativeCoverProjection
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) y))
  exact congrArg F (nativeTargetPoint_eq_original X x P).symm

/-- The actual original regular-relative H2 group, with its original map and quotient. -/
abbrev originalRegularHomologyTwo (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : ModuleCat.{u} ℤ :=
  (TopCat.originalRegularRelativeChainComplex (LoopCellAttachment.inclusion X x P)
    (LoopCellAttachment.inclusion X x P x)).homology 2

/-- The original relative regular chains, after forgetting integral scalars,
identify with the same native pair through the existing coefficient comparison. -/
def originalRegularNativeChainIso (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (TopCat.originalRegularRelativeChainComplex (LoopCellAttachment.inclusion X x P)
          (LoopCellAttachment.inclusion X x P x)) ≅
      (LoopCellPulledSimplicialModel.nativePair X x P).chainComplex
        (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let f := LoopCellAttachment.inclusion X x P
  let y := f x
  let A := TopCat.originalRegularPulledCoverPair f y
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let h : A = LoopCellPulledSimplicialModel.nativePair X x P := originalRegularPair_eq_native X x P
  exact F.mapIso (TopCat.originalRegularRelativeChainIso f y) ≪≫
    OriginalNativeRelativeBasis.forgetRelativeChainIso A ≪≫
      eqToIso (congrArg (fun A : SSetPair.{u} =>
        A.chainComplex (singularIntegralCoefficients : AddCommGrpCat.{u})) h)

/-- The corresponding absolute regular chains use the same cover, scalar
comparison and derived singular basepoint equality. -/
def originalRegularNativeAmbientChainIso (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)))) ≅
      (LoopCellSphericalGenerators.nativeCover X x P).chainComplex
        (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let f := LoopCellAttachment.inclusion X x P
  let y := f x
  let A := TopCat.originalRegularPulledCoverPair f y
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let h : A = LoopCellPulledSimplicialModel.nativePair X x P := originalRegularPair_eq_native X x P
  exact F.mapIso (TopCat.originalTopRegularCoverChainIso (LoopCellAttachment.space X x P) y) ≪≫
    (SSet.mapChainComplexFunctorIso U R).app A.fst ≪≫
      eqToIso (congrArg (fun A : SSetPair.{u} =>
        A.fst.chainComplex (singularIntegralCoefficients : AddCommGrpCat.{u})) h)

/-- The entire original regular quotient chain map is preserved; no relative
homology or cell-basis isomorphism is supplied as an input. -/
theorem originalRegularNativeChainIso_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (TopCat.originalRegularRelativeChainProjection (LoopCellAttachment.inclusion X x P)
          (LoopCellAttachment.inclusion X x P x)) ≫
      (originalRegularNativeChainIso X x P).hom =
        (originalRegularNativeAmbientChainIso X x P).hom ≫
          (LoopCellPulledSimplicialModel.nativePair X x P).chainComplexπ
            (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let f := LoopCellAttachment.inclusion X x P
  let y := f x
  let A := TopCat.originalRegularPulledCoverPair f y
  let B := LoopCellPulledSimplicialModel.nativePair X x P
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let q := TopCat.originalRegularRelativeChainProjection f y
  let eR := TopCat.originalRegularRelativeChainIso f y
  let eT := TopCat.originalTopRegularCoverChainIso (LoopCellAttachment.space X x P) y
  let eF := OriginalNativeRelativeBasis.forgetRelativeChainIso A
  let eV := (SSet.mapChainComplexFunctorIso U R).app A.fst
  let h : A = B := originalRegularPair_eq_native X x P
  let t := eqToIso (congrArg (fun A : SSetPair.{u} =>
    A.chainComplex (singularIntegralCoefficients : AddCommGrpCat.{u})) h)
  let s := eqToIso (congrArg (fun A : SSetPair.{u} =>
    A.fst.chainComplex (singularIntegralCoefficients : AddCommGrpCat.{u})) h)
  let qM := A.chainComplexπ R
  let qA := A.chainComplexπ (singularIntegralCoefficients : AddCommGrpCat.{u})
  let qB := B.chainComplexπ (singularIntegralCoefficients : AddCommGrpCat.{u})
  have h1 : F.map q ≫ F.map eR.hom = F.map eT.hom ≫ F.map qM :=
    (F.map_comp q eR.hom).symm.trans
      ((congrArg F.map (TopCat.originalRegularRelativeChainIso_projection f y)).trans
        (F.map_comp eT.hom qM))
  have h2 : F.map qM ≫ eF.hom = eV.hom ≫ qA :=
    OriginalNativeRelativeBasis.forgetRelativeChainIso_projection A
  have h3 : qA ≫ t.hom = s.hom ≫ qB :=
    OriginalNativeRelativeBasis.stockRelativeQuotient_transport A B h _
  change F.map q ≫ (F.map eR.hom ≫ eF.hom ≫ t.hom) =
    (F.map eT.hom ≫ eV.hom ≫ s.hom) ≫ qB
  have h12 : F.map q ≫ (F.map eR.hom ≫ eF.hom) =
      F.map eT.hom ≫ (eV.hom ≫ qA) :=
    (Category.assoc (F.map q) (F.map eR.hom) eF.hom).symm.trans
      ((congrArg (fun k => k ≫ eF.hom) h1).trans
        ((Category.assoc (F.map eT.hom) (F.map qM) eF.hom).trans
          (congrArg (fun k => F.map eT.hom ≫ k) h2)))
  exact (Category.assoc (F.map q) (F.map eR.hom ≫ eF.hom) t.hom).symm.trans
    ((congrArg (fun k => k ≫ t.hom) h12).trans
      ((Category.assoc (F.map eT.hom) (eV.hom ≫ qA) t.hom).trans
        ((congrArg (fun k => F.map eT.hom ≫ k)
          ((Category.assoc eV.hom qA t.hom).trans
            (congrArg (fun k => eV.hom ≫ k) h3))).trans
          (by
            change F.map eT.hom ≫ (eV.hom ≫ (s.hom ≫ qB)) =
              (F.map eT.hom ≫ (eV.hom ≫ s.hom)) ≫ qB
            exact (congrArg (fun k => F.map eT.hom ≫ k)
              (Category.assoc eV.hom s.hom qB).symm).trans
                (Category.assoc (F.map eT.hom) (eV.hom ≫ s.hom) qB).symm))))

/-- The exact original regular-relative H2 comparison to the SAME native relative covering group. -/
def originalRegularNativeHomologyIso (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj (originalRegularHomologyTwo X x P) ≅
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let C := TopCat.originalRegularRelativeChainComplex (LoopCellAttachment.inclusion X x P)
    (LoopCellAttachment.inclusion X x P x)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 2
  exact ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 2 U).app C).symm ≪≫
    H.mapIso (originalRegularNativeChainIso X x P) ≪≫
      nativeRelativeUnitHomologyIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) 2

/-- The absolute original regular homology is carried through the same cover
and its actual realization unit. -/
def originalRegularNativeAmbientHomologyIso (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj
        ((TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)))).homology 2) ≅
      ((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj
          (LoopCellSphericalGenerators.liftedPair X x P).fst := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let C := TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)))
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 2
  exact ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 2 U).app C).symm ≪≫
    H.mapIso (originalRegularNativeAmbientChainIso X x P) ≪≫
      SSet.realizationSingularHomologyIso (singularIntegralCoefficients : AddCommGrpCat.{u})
        (LoopCellSphericalGenerators.nativeCover X x P) 2

/-- The actual original homology quotient agrees with the native old-cover
quotient through the same absolute and relative comparison maps. -/
theorem originalRegularNativeHomologyIso_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
        (HomologicalComplex.homologyMap
          (TopCat.originalRegularRelativeChainProjection (LoopCellAttachment.inclusion X x P)
            (LoopCellAttachment.inclusion X x P x)) 2) ≫
      (originalRegularNativeHomologyIso X x P).hom =
        (originalRegularNativeAmbientHomologyIso X x P).hom ≫
          LoopCellSphericalGenerators.relativeProjection X x P := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 2
  let A := TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)))
  let C := TopCat.originalRegularRelativeChainComplex (LoopCellAttachment.inclusion X x P)
    (LoopCellAttachment.inclusion X x P x)
  let q := TopCat.originalRegularRelativeChainProjection (LoopCellAttachment.inclusion X x P)
    (LoopCellAttachment.inclusion X x P x)
  let c := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 2 U
  let eR := originalRegularNativeChainIso X x P
  let eV := originalRegularNativeAmbientChainIso X x P
  let uR := nativeRelativeUnitHomologyIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) 2
  let uV := SSet.realizationSingularHomologyIso (singularIntegralCoefficients : AddCommGrpCat.{u})
    (LoopCellSphericalGenerators.nativeCover X x P) 2
  let qS := (LoopCellPulledSimplicialModel.nativePair X x P).homologyπ
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 2
  let qT := LoopCellSphericalGenerators.relativeProjection X x P
  have h1 : U.map (HomologicalComplex.homologyMap q 2) ≫ c.inv.app C =
      c.inv.app A ≫ H.map (F.map q) := c.inv.naturality q
  have h2 : H.map (F.map q) ≫ H.map eR.hom = H.map eV.hom ≫ qS :=
    (H.map_comp (F.map q) eR.hom).symm.trans
      ((congrArg H.map (originalRegularNativeChainIso_projection X x P)).trans
        (H.map_comp eV.hom _))
  have h3 : qS ≫ uR.hom = uV.hom ≫ qT :=
    nativeRelativeUnitHomologyIso_projection X x P
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2
  change U.map (HomologicalComplex.homologyMap q 2) ≫
      (c.inv.app C ≫ H.map eR.hom ≫ uR.hom) =
    (c.inv.app A ≫ H.map eV.hom ≫ uV.hom) ≫ qT
  have h12 : U.map (HomologicalComplex.homologyMap q 2) ≫
      (c.inv.app C ≫ H.map eR.hom) = c.inv.app A ≫ (H.map eV.hom ≫ qS) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ H.map eR.hom) h1).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => c.inv.app A ≫ k) h2)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ uR.hom) h12).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => c.inv.app A ≫ k)
          ((Category.assoc _ _ _).trans (congrArg (fun k => H.map eV.hom ≫ k) h3))).trans
          ((congrArg (fun k => c.inv.app A ≫ k)
            (Category.assoc (H.map eV.hom) uV.hom qT).symm).trans
              (Category.assoc (c.inv.app A) (H.map eV.hom ≫ uV.hom) qT).symm))))

/-- The whole inverse quotient law uses those same two original comparison isomorphisms. -/
theorem originalRegularNativeHomologyIso_inverse_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    LoopCellSphericalGenerators.relativeProjection X x P ≫
        (originalRegularNativeHomologyIso X x P).inv =
      (originalRegularNativeAmbientHomologyIso X x P).inv ≫
        (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
          (HomologicalComplex.homologyMap
            (TopCat.originalRegularRelativeChainProjection (LoopCellAttachment.inclusion X x P)
              (LoopCellAttachment.inclusion X x P x)) 2) := by
  let eR := originalRegularNativeHomologyIso X x P
  let eV := originalRegularNativeAmbientHomologyIso X x P
  let qR := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
    (HomologicalComplex.homologyMap
      (TopCat.originalRegularRelativeChainProjection (LoopCellAttachment.inclusion X x P)
        (LoopCellAttachment.inclusion X x P x)) 2)
  let qV := LoopCellSphericalGenerators.relativeProjection X x P
  have h : qR ≫ eR.hom = eV.hom ≫ qV := originalRegularNativeHomologyIso_projection X x P
  have hPre : eV.inv ≫ (qR ≫ eR.hom) = qV :=
    (congrArg (fun k => eV.inv ≫ k) h).trans (eV.inv_hom_id_assoc qV)
  exact (congrArg (fun k => k ≫ eR.inv) hPre).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => eV.inv ≫ k)
        ((Category.assoc qR eR.hom eR.inv).trans
          ((congrArg (fun k => qR ≫ k) eR.hom_inv_id).trans (Category.comp_id qR)))).trans
        (by rfl)))

/-- The chosen translated sphere projects to the SAME original spherical attaching map. -/
theorem chosenSphericalCopy_down (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    chosenSphericalCopy X x P i ≫
        (SSet.toTop.map (LoopCellPulledSimplicialModel.projection X x P) ≫
          sSetTopAdj.counit.app (LoopCellAttachment.space X x P)) =
      LoopCellSphericalGenerators.sphericalGenerator X x P i.2 := by
  let F := SSet.toTop
  let S := LoopCellSphericalGenerators.liftedSphericalGenerator X x P i.2
  let d := LoopCellQuotientCellPresentation.nativeDeck X x P i.1
  let π := LoopCellPulledSimplicialModel.projection X x P
  let e := sSetTopAdj.counit.app (LoopCellAttachment.space X x P)
  have h : F.map d ≫ F.map π = F.map π :=
    (F.map_comp d π).symm.trans (congrArg F.map
        (LoopCellQuotientCellPresentation.nativeDeck_projection X x P i.1))
  exact (Category.assoc S (F.map d) (F.map π ≫ e)).trans
    ((congrArg (fun f => S ≫ f) (Category.assoc (F.map d) (F.map π) e).symm).trans
      ((congrArg (fun f => S ≫ (f ≫ e)) h).trans
        (LoopCellSphericalGenerators.liftedSphericalGenerator_down X x P i.2)))

/-- The ACTUAL upstairs three-cell attachment, using every quotient-labelled SAME chosen sphere. -/
abbrev upstairsThreeSpace (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : TopCat.{u} :=
  CellFamilyAttachment.space (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (chosenSphericalCopy X x P)

/-- Its actual relative pair is the original native covering space inclusion in that three-cell
attachment. -/
abbrev upstairsThreePair (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : TopPair.{u} :=
  CellCollarDeformation.attachmentPair (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (chosenSphericalCopy X x P)

/-- The ACTUAL original three-cell attachment on the unchanged original two-cell space. -/
abbrev originalThreeSpace (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : TopCat.{u} :=
  CellFamilyAttachment.space (LoopCellAttachment.space X x P) 2
    (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- The actual projection of both entire spaces and all whole three-disks to the original
attachment. -/
def upstairsThreeDown (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    upstairsThreeSpace X x P ⟶ originalThreeSpace X x P := by
  let Y := LoopCellAttachment.space X x P
  let s := LoopCellSphericalGenerators.sphericalGenerator X x P
  let π := SSet.toTop.map (LoopCellPulledSimplicialModel.projection X x P) ≫ sSetTopAdj.counit.app Y
  let j := CellFamilyAttachment.inclusion Y 2 s
  let c : LoopCellQuotientCellPresentation.labels X x P →
      ((classicalCellDiskPair.{u} 3).fst ⟶ originalThreeSpace X x P) :=
    fun i => CellFamilyAttachment.cell Y 2 s i.2
  exact CellFamilyAttachment.desc (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (chosenSphericalCopy X x P) (π ≫ j) c (fun i =>
      (CellFamilyAttachment.boundary_gluing Y 2 s i.2).symm.trans
        ((congrArg (fun f => f ≫ j) (chosenSphericalCopy_down X x P i).symm).trans
          (Category.assoc (chosenSphericalCopy X x P i) π j)))

/-- The actual three-space projection retains the whole original old-space leg. -/
theorem upstairsThreeDown_old (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    CellFamilyAttachment.inclusion (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (chosenSphericalCopy X x P) ≫ upstairsThreeDown X x P =
      (SSet.toTop.map (LoopCellPulledSimplicialModel.projection X x P) ≫
        sSetTopAdj.counit.app (LoopCellAttachment.space X x P)) ≫
          CellFamilyAttachment.inclusion (LoopCellAttachment.space X x P) 2
            (LoopCellSphericalGenerators.sphericalGenerator X x P) := by
  let Y := LoopCellAttachment.space X x P
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let s := LoopCellSphericalGenerators.sphericalGenerator X x P
  let a := chosenSphericalCopy X x P
  let π := SSet.toTop.map (LoopCellPulledSimplicialModel.projection X x P) ≫ sSetTopAdj.counit.app Y
  let j := CellFamilyAttachment.inclusion Y 2 s
  let c := fun i : LoopCellQuotientCellPresentation.labels X x P =>
      CellFamilyAttachment.cell Y 2 s i.2
  let w := fun i : LoopCellQuotientCellPresentation.labels X x P =>
    (CellFamilyAttachment.boundary_gluing Y 2 s i.2).symm.trans
      ((congrArg (fun f => f ≫ j) (chosenSphericalCopy_down X x P i).symm).trans
        (Category.assoc (a i) π j))
  change CellFamilyAttachment.inclusion V 2 a ≫ CellFamilyAttachment.desc V 2 a (π ≫ j) c w = π ≫ j
  exact CellFamilyAttachment.inclusion_desc V 2 a (π ≫ j) c w

/-- Every entire original upstairs three-disk projects to its SAME original
characteristic disk, independently of the quotient label. -/
theorem upstairsThreeDown_cell (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    CellFamilyAttachment.cell (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (chosenSphericalCopy X x P) i ≫ upstairsThreeDown X x P =
      CellFamilyAttachment.cell (LoopCellAttachment.space X x P) 2
        (LoopCellSphericalGenerators.sphericalGenerator X x P) i.2 := by
  let Y := LoopCellAttachment.space X x P
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let s := LoopCellSphericalGenerators.sphericalGenerator X x P
  let a := chosenSphericalCopy X x P
  let π := SSet.toTop.map (LoopCellPulledSimplicialModel.projection X x P) ≫ sSetTopAdj.counit.app Y
  let j := CellFamilyAttachment.inclusion Y 2 s
  let c := fun i : LoopCellQuotientCellPresentation.labels X x P =>
      CellFamilyAttachment.cell Y 2 s i.2
  let w := fun i : LoopCellQuotientCellPresentation.labels X x P =>
    (CellFamilyAttachment.boundary_gluing Y 2 s i.2).symm.trans
      ((congrArg (fun f => f ≫ j) (chosenSphericalCopy_down X x P i).symm).trans
        (Category.assoc (a i) π j))
  change CellFamilyAttachment.cell V 2 a i ≫ CellFamilyAttachment.desc V 2 a (π ≫ j) c w = c i
  exact CellFamilyAttachment.cell_desc V 2 a (π ≫ j) c w i

/-- The literal three-cell diagonal in the original natural grading. -/
abbrev upstairsThreeCoefficientIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (∐ fun _ : LoopCellQuotientCellPresentation.labels X x P =>
      (singularIntegralCoefficients : AddCommGrpCat.{u})) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).obj (upstairsThreePair X x P) :=
  CellFamilyAttachment.attachmentRelativeDiagonalIso
    (LoopCellSphericalGenerators.liftedPair X x P).fst 2 (chosenSphericalCopy X x P)
      (singularIntegralCoefficients : AddCommGrpCat.{u})

/-- The ACTUAL three-to-two boundary: the three-cell pair LES followed by the unchanged native
old-cover quotient. -/
def actualThreeToTwoBoundary (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (∐ fun _ : LoopCellQuotientCellPresentation.labels X x P =>
      (singularIntegralCoefficients : AddCommGrpCat.{u})) ⟶
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  (upstairsThreeCoefficientIso X x P).hom ≫
    ((relativeSingularHomologyNatToIntIso AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).app (upstairsThreePair X x P)).inv ≫
    (singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 3 (upstairsThreePair X x P) ≫
    ((singularHomologyNatToIntIso AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app
        (LoopCellSphericalGenerators.liftedPair X x P).fst).hom ≫
    LoopCellSphericalGenerators.relativeProjection X x P

/-- The actual LES boundary has the same entire labelled column as the fixed three-disk boundary. -/
theorem actualThreeToTwoBoundary_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
      (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫ actualThreeToTwoBoundary X x P =
        classicalCellBoundaryHomologyTwoGenerator.{u} ≫
          (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
            (singularIntegralCoefficients : AddCommGrpCat.{u})).map (chosenSphericalCopy X x P i)) ≫
          LoopCellSphericalGenerators.relativeProjection X x P := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let A := upstairsThreePair X x P
  let D := classicalCellDiskPair.{u} 3
  let E := singularHomologyIntData AddCommGrpCat.{u} R
  let H := (singularHomologyFunctor AddCommGrpCat.{u} 2).obj R
  let Hrel := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 3
  let c := CellFamilyAttachment.cellPairMap (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (chosenSphericalCopy X x P) i
  let q := LoopCellSphericalGenerators.relativeProjection X x P
  let g := (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u} R 3).hom
  let a := relativeSingularHomologyNatToIntIso AddCommGrpCat.{u} R 3
  let b := singularHomologyNatToIntIso AddCommGrpCat.{u} R 2
  let aA : Hrel.obj A ⟶ (E.Hₚ 3).obj A := a.inv.app A
  let aD : Hrel.obj D ⟶ (E.Hₚ 3).obj D := a.inv.app D
  let dA : (E.Hₚ 3).obj A ⟶ (E.H 2).obj A.snd := E.boundary 3 A
  let dD : (E.Hₚ 3).obj D ⟶ (E.H 2).obj D.snd := E.boundary 3 D
  let bA : (E.H 2).obj A.snd ⟶ H.obj A.snd := b.hom.app A.snd
  let bD : (E.H 2).obj D.snd ⟶ H.obj D.snd := b.hom.app D.snd
  let s : D.snd ⟶ A.snd := chosenSphericalCopy X x P i
  let qA : H.obj A.snd ⟶ nativeHomologyTwo X x P R := q
  have hCell : Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) i ≫
      (upstairsThreeCoefficientIso X x P).hom = g ≫ Hrel.map c :=
    CellFamilyAttachment.attachmentRelativeCellHom_eq_diskPair
      (LoopCellSphericalGenerators.liftedPair X x P).fst 2 (chosenSphericalCopy X x P) R i
  have hRel : Hrel.map c ≫ a.inv.app A = a.inv.app D ≫ (E.Hₚ 3).map c :=
    a.inv.naturality c
  have hBoundary : (E.Hₚ 3).map c ≫ E.boundary 3 A =
      E.boundary 3 D ≫ (E.H 2).map (chosenSphericalCopy X x P i) :=
    (TopPair.HomologyTheoryData.boundary_naturality E 3 c).trans
      (congrArg (fun f => E.boundary 3 D ≫ (E.H 2).map f)
        (CellFamilyAttachment.cellPairMap_snd
          (LoopCellSphericalGenerators.liftedPair X x P).fst 2 (chosenSphericalCopy X x P) i))
  have hAbs : (E.H 2).map (chosenSphericalCopy X x P i) ≫ b.hom.app A.snd =
      b.hom.app D.snd ≫ H.map (chosenSphericalCopy X x P i) :=
    b.hom.naturality (chosenSphericalCopy X x P i)
  have hGenerator : classicalCellBoundaryHomologyTwoGenerator.{u} =
      g ≫ a.inv.app D ≫ E.boundary 3 D ≫ b.hom.app D.snd :=
    classicalCellBoundaryHomologyTwoGenerator_eq_original_boundary
  change (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) i ≫
    (upstairsThreeCoefficientIso X x P).hom) ≫ aA ≫ dA ≫ bA ≫ qA =
      classicalCellBoundaryHomologyTwoGenerator.{u} ≫ H.map s ≫ qA
  have hRel' : Hrel.map c ≫ aA = aD ≫ (E.Hₚ 3).map c := hRel
  have hBoundary' : (E.Hₚ 3).map c ≫ dA = dD ≫ (E.H 2).map s := hBoundary
  have hAbs' : (E.H 2).map s ≫ bA = bD ≫ H.map s := hAbs
  have hGen' : classicalCellBoundaryHomologyTwoGenerator.{u} = g ≫ aD ≫ dD ≫ bD := hGenerator
  calc
    _ = (g ≫ Hrel.map c) ≫ aA ≫ dA ≫ bA ≫ qA :=
      congrArg (fun k : R ⟶ Hrel.obj A => k ≫ aA ≫ dA ≫ bA ≫ qA) hCell
    _ = (g ≫ aD ≫ (E.Hₚ 3).map c) ≫ dA ≫ bA ≫ qA := by
      simpa only [Category.assoc] using
        congrArg (fun k => g ≫ k ≫ dA ≫ bA ≫ qA) hRel'
    _ = (g ≫ aD ≫ dD ≫ (E.H 2).map s) ≫ bA ≫ qA := by
      simpa only [Category.assoc] using
        congrArg (fun k => g ≫ aD ≫ k ≫ bA ≫ qA) hBoundary'
    _ = (g ≫ aD ≫ dD ≫ bD) ≫ H.map s ≫ qA := by
      simpa only [Category.assoc] using
        congrArg (fun k => g ≫ aD ≫ dD ≫ k ≫ qA) hAbs'
    _ = classicalCellBoundaryHomologyTwoGenerator.{u} ≫ H.map s ≫ qA :=
      congrArg (fun k : R ⟶ H.obj D.snd => k ≫ H.map s ≫ qA) hGen'.symm

/-- The ENTIRE actual chosen three-to-two LES boundary is the identity in the same original labelled
basis. -/
theorem actualThreeToTwoBoundary_eq_basis (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    actualThreeToTwoBoundary X x P =
      (nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).hom := by
  apply Sigma.hom_ext
  intro i
  exact (actualThreeToTwoBoundary_ι X x P i).trans (chosenSphericalCopy_column X x P i)

/-- The actual chosen sphere copies have the full LEFT label composition law. -/
theorem chosenSphericalCopy_deck (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    chosenSphericalCopy X x P (q*r,p) = chosenSphericalCopy X x P (r,p) ≫
      SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q) := by
  let F := SSet.toTop
  let S := LoopCellSphericalGenerators.liftedSphericalGenerator X x P p
  let dr := LoopCellQuotientCellPresentation.nativeDeck X x P r
  let dq := LoopCellQuotientCellPresentation.nativeDeck X x P q
  exact (congrArg (fun f => S ≫ F.map f)
      (LoopCellQuotientCellPresentation.nativeDeck_mul X x P q r)).trans
    ((congrArg (fun f => S ≫ f) (F.map_comp dr dq)).trans
      ((Category.assoc S (F.map dr) (F.map dq)).symm))

/-- Extend the original native deck map across the actual three-cell family
by its LEFT permutation of all quotient-labelled disks. -/
def upstairsThreeDeck (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) : upstairsThreeSpace X x P ⟶ upstairsThreeSpace X x P := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let j := CellFamilyAttachment.inclusion V 2 a
  let d := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)
  let c := fun i : LoopCellQuotientCellPresentation.labels X x P =>
    CellFamilyAttachment.cell V 2 a (q*i.1,i.2)
  exact CellFamilyAttachment.desc V 2 a (d ≫ j) c (fun i =>
    (CellFamilyAttachment.boundary_gluing V 2 a (q*i.1,i.2)).symm.trans
      ((congrArg (fun f => f ≫ j) (chosenSphericalCopy_deck X x P q i.1 i.2)).trans
        (Category.assoc (a i) d j)))

/-- This extension keeps the same native map on the entire old covering space. -/
theorem upstairsThreeDeck_old (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) :
    CellFamilyAttachment.inclusion (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (chosenSphericalCopy X x P) ≫ upstairsThreeDeck X x P q =
      SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q) ≫
        CellFamilyAttachment.inclusion (LoopCellSphericalGenerators.liftedPair X x P).fst 2
          (chosenSphericalCopy X x P) := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let j := CellFamilyAttachment.inclusion V 2 a
  let d := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)
  let c := fun i : LoopCellQuotientCellPresentation.labels X x P =>
    CellFamilyAttachment.cell V 2 a (q*i.1,i.2)
  let w := fun i : LoopCellQuotientCellPresentation.labels X x P =>
    (CellFamilyAttachment.boundary_gluing V 2 a (q*i.1,i.2)).symm.trans
      ((congrArg (fun f => f ≫ j) (chosenSphericalCopy_deck X x P q i.1 i.2)).trans
        (Category.assoc (a i) d j))
  change j ≫ CellFamilyAttachment.desc V 2 a (d ≫ j) c w = d ≫ j
  exact CellFamilyAttachment.inclusion_desc V 2 a (d ≫ j) c w

/-- Each WHOLE original three-disk is sent to the disk with the LEFT-multiplied label. -/
theorem upstairsThreeDeck_cell (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) (i : LoopCellQuotientCellPresentation.labels X x P) :
    CellFamilyAttachment.cell (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (chosenSphericalCopy X x P) i ≫ upstairsThreeDeck X x P q =
      CellFamilyAttachment.cell (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (chosenSphericalCopy X x P) (q*i.1,i.2) := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let j := CellFamilyAttachment.inclusion V 2 a
  let d := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)
  let c := fun k : LoopCellQuotientCellPresentation.labels X x P =>
    CellFamilyAttachment.cell V 2 a (q*k.1,k.2)
  let w := fun k : LoopCellQuotientCellPresentation.labels X x P =>
    (CellFamilyAttachment.boundary_gluing V 2 a (q*k.1,k.2)).symm.trans
      ((congrArg (fun f => f ≫ j) (chosenSphericalCopy_deck X x P q k.1 k.2)).trans
        (Category.assoc (a k) d j))
  change CellFamilyAttachment.cell V 2 a i ≫ CellFamilyAttachment.desc V 2 a (d ≫ j) c w = c i
  exact CellFamilyAttachment.cell_desc V 2 a (d ≫ j) c w i

/-- The actual extension of the unit is the whole identity map. -/
theorem upstairsThreeDeck_one (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    upstairsThreeDeck X x P 1 = 𝟙 (upstairsThreeSpace X x P) := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  apply CellFamilyAttachment.hom_ext V 2 a
  · exact (upstairsThreeDeck_old X x P 1).trans
      ((congrArg (fun f => SSet.toTop.map f ≫ CellFamilyAttachment.inclusion V 2 a)
        (LoopCellQuotientCellPresentation.nativeDeck_one X x P)).trans
          ((congrArg (fun f => f ≫ CellFamilyAttachment.inclusion V 2 a)
            (SSet.toTop.map_id _)).trans
              ((Category.id_comp _).trans (Category.comp_id _).symm)))
  · intro i
    rcases i with ⟨r,p⟩
    exact (upstairsThreeDeck_cell X x P 1 (r,p)).trans
      ((congrArg (fun k => CellFamilyAttachment.cell V 2 a (k,p)) (one_mul r)).trans
        (Category.comp_id _).symm)

/-- The original noncommutative LEFT group law holds on the entire attached space. -/
theorem upstairsThreeDeck_mul (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q r : FundamentalGroup X x ⧸ P) :
    upstairsThreeDeck X x P (q*r) = upstairsThreeDeck X x P r ≫ upstairsThreeDeck X x P q := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let j := CellFamilyAttachment.inclusion V 2 a
  let dr := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P r)
  let dq := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)
  have hD : SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P (q*r)) = dr ≫ dq :=
    (congrArg SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck_mul X x P q r)).trans
      (SSet.toTop.map_comp _ _)
  apply CellFamilyAttachment.hom_ext V 2 a
  · have hL : j ≫ upstairsThreeDeck X x P (q*r) = dr ≫ (dq ≫ j) :=
      (upstairsThreeDeck_old X x P (q*r)).trans
        ((congrArg (fun f => f ≫ j) hD).trans (Category.assoc dr dq j))
    have hR : j ≫ (upstairsThreeDeck X x P r ≫ upstairsThreeDeck X x P q) = dr ≫ (dq ≫ j) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ upstairsThreeDeck X x P q) (upstairsThreeDeck_old X x P r)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun f => dr ≫ f) (upstairsThreeDeck_old X x P q))))
    exact hL.trans hR.symm
  · intro i
    have hR : CellFamilyAttachment.cell V 2 a i ≫
        (upstairsThreeDeck X x P r ≫ upstairsThreeDeck X x P q) =
      CellFamilyAttachment.cell V 2 a (q*(r*i.1),i.2) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ upstairsThreeDeck X x P q)
            (upstairsThreeDeck_cell X x P r i)).trans
          (upstairsThreeDeck_cell X x P q (r*i.1,i.2)))
    exact (upstairsThreeDeck_cell X x P (q*r) i).trans
      ((congrArg (fun k => CellFamilyAttachment.cell V 2 a (k,i.2))
        (mul_assoc q r i.1)).trans hR.symm)

/-- The actual extension is a map of the original upstairs three-cell pair. -/
def upstairsThreeDeckPair (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) : upstairsThreePair X x P ⟶ upstairsThreePair X x P :=
  TopPair.ofHom (upstairsThreeDeck X x P q)
    (SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q))
    (upstairsThreeDeck_old X x P q).symm

/-- The three-cell pair's whole group action has its actual unit. -/
theorem upstairsThreeDeckPair_one (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    upstairsThreeDeckPair X x P 1 = 𝟙 (upstairsThreePair X x P) := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact (congrArg SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck_one X x P)).trans
      (SSet.toTop.map_id _)
  · exact upstairsThreeDeck_one X x P

/-- Its pair action has the same noncommutative LEFT multiplication order. -/
theorem upstairsThreeDeckPair_mul (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q r : FundamentalGroup X x ⧸ P) :
    upstairsThreeDeckPair X x P (q*r) = upstairsThreeDeckPair X x P r ≫
        upstairsThreeDeckPair X x P q := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact
      (congrArg SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck_mul X x P q r)).trans
      (SSet.toTop.map_comp _ _)
  · exact upstairsThreeDeck_mul X x P q r

/-- Every whole attached three-disk pair transforms by the same LEFT label multiplication. -/
theorem upstairsThreeCellPair_deck (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    CellFamilyAttachment.cellPairMap (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (chosenSphericalCopy X x P) (q*r,p) =
      CellFamilyAttachment.cellPairMap (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (chosenSphericalCopy X x P) (r,p) ≫ upstairsThreeDeckPair X x P q := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let cq := CellFamilyAttachment.cellPairMap V 2 a (q*r,p)
  let cr := CellFamilyAttachment.cellPairMap V 2 a (r,p)
  let d := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)
  apply MorphismProperty.Arrow.Hom.ext
  · have hq : TopPair.Hom.snd cq = a (q*r,p) :=
      CellFamilyAttachment.cellPairMap_snd V 2 a (q*r,p)
    have hr : TopPair.Hom.snd cr = a (r,p) :=
      CellFamilyAttachment.cellPairMap_snd V 2 a (r,p)
    exact hq.trans ((chosenSphericalCopy_deck X x P q r p).trans
      (congrArg (fun f => f ≫ d) hr.symm))
  · have hq : TopPair.Hom.fst cq = CellFamilyAttachment.cell V 2 a (q*r,p) :=
      CellFamilyAttachment.cellPairMap_fst V 2 a (q*r,p)
    have hr : TopPair.Hom.fst cr = CellFamilyAttachment.cell V 2 a (r,p) :=
      CellFamilyAttachment.cellPairMap_fst V 2 a (r,p)
    exact hq.trans ((upstairsThreeDeck_cell X x P q (r,p)).symm.trans
      (congrArg (fun f => f ≫ upstairsThreeDeck X x P q) hr.symm))

/-- The entire three-cell homology basis retains the actual geometric deck action. -/
theorem upstairsThreeCoefficientIso_deck (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) (q*r,p) ≫
      (upstairsThreeCoefficientIso X x P).hom =
        (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
          (singularIntegralCoefficients : AddCommGrpCat.{u})) (r,p) ≫
            (upstairsThreeCoefficientIso X x P).hom) ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{u}
            (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).map
                (upstairsThreeDeckPair X x P q) := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let H := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 3
  let g := (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u} R 3).hom
  let c := CellFamilyAttachment.cellPairMap V 2 a (r,p)
  let d := upstairsThreeDeckPair X x P q
  have hq : Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (q*r,p) ≫
      (upstairsThreeCoefficientIso X x P).hom = g ≫
          H.map (CellFamilyAttachment.cellPairMap V 2 a (q*r,p)) :=
    CellFamilyAttachment.attachmentRelativeCellHom_eq_diskPair V 2 a R (q*r,p)
  have hr : Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (r,p) ≫
      (upstairsThreeCoefficientIso X x P).hom = g ≫ H.map c :=
    CellFamilyAttachment.attachmentRelativeCellHom_eq_diskPair V 2 a R (r,p)
  have hMap : H.map (CellFamilyAttachment.cellPairMap V 2 a (q*r,p)) = H.map c ≫ H.map d :=
    (congrArg H.map (upstairsThreeCellPair_deck X x P q r p)).trans (H.map_comp c d)
  exact hq.trans ((congrArg (fun f => g ≫ f) hMap).trans
    ((Category.assoc g (H.map c) (H.map d)).symm.trans
      (congrArg (fun f => f ≫ H.map d) hr.symm)))

/-- The actual relative H3 group of the upstairs three-cell attachment. -/
abbrev upstairsThreeHomology (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : AddCommGrpCat.{u} :=
  (relativeSingularHomologyFunctor AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).obj (upstairsThreePair X x P)

/-- The actual geometric action on the three-cell relative homology group. -/
def upstairsThreeDeckRepresentation (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    FundamentalGroup X x ⧸ P →* AddMonoid.End (upstairsThreeHomology X x P) where
  toFun q := ((relativeSingularHomologyFunctor AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).map (upstairsThreeDeckPair X x P q)).hom
  map_one' := by
    ext a
    let H := relativeSingularHomologyFunctor AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 3
    exact ConcreteCategory.congr_hom
      ((congrArg H.map (upstairsThreeDeckPair_one X x P)).trans (H.map_id _)) a
  map_mul' q r := by
    ext a
    let H := relativeSingularHomologyFunctor AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 3
    exact ConcreteCategory.congr_hom
      ((congrArg H.map (upstairsThreeDeckPair_mul X x P q r)).trans (H.map_comp _ _)) a

/-- Linearize that SAME geometric action over the original quotient-group ring. -/
def upstairsThreeDeckRingHom (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    quotientGroupRing X x P →+* AddMonoid.End (upstairsThreeHomology X x P) :=
  MonoidAlgebra.liftNCRingHom (Int.castRingHom (AddMonoid.End (upstairsThreeHomology X x P)))
    (upstairsThreeDeckRepresentation X x P)
    (fun z q => Int.cast_commute z (upstairsThreeDeckRepresentation X x P q))

/-- The quotient-ring module on the actual relative three-cell homology. -/
def upstairsThreeDeckModule (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    Module (quotientGroupRing X x P) (upstairsThreeHomology X x P) :=
  Module.compHom (upstairsThreeHomology X x P) (upstairsThreeDeckRingHom X x P)

/-- Every ring coordinate has its original integer coefficient and geometric deck action. -/
theorem upstairsThreeDeckModule_single (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) (z : ℤ) (a : upstairsThreeHomology X x P) :
    letI := upstairsThreeDeckModule X x P
    (MonoidAlgebra.single q z : quotientGroupRing X x P) • a =
      z • upstairsThreeDeckRepresentation X x P q a := by
  let := upstairsThreeDeckModule X x P
  have h : upstairsThreeDeckRingHom X x P (MonoidAlgebra.single q z) =
      (z : AddMonoid.End (upstairsThreeHomology X x P)) * upstairsThreeDeckRepresentation X x P q :=
    MonoidAlgebra.liftNCRingHom_single
      (Int.castRingHom (AddMonoid.End (upstairsThreeHomology X x P)))
      (upstairsThreeDeckRepresentation X x P) _ q z
  change upstairsThreeDeckRingHom X x P (MonoidAlgebra.single q z) a = _
  exact (congrArg (fun f : AddMonoid.End (upstairsThreeHomology X x P) => f a) h).trans (by
    change (z : AddMonoid.End (upstairsThreeHomology X x P))
      (upstairsThreeDeckRepresentation X x P q a) = _
    rw [AddMonoid.End.intCast_def]
    rfl)

/-- The actual relative boundary before introducing any free-cell coordinates. -/
def actualThreeRelativeBoundary (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    upstairsThreeHomology X x P ⟶
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  ((relativeSingularHomologyNatToIntIso AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).app (upstairsThreePair X x P)).inv ≫
    (singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 3 (upstairsThreePair X x P) ≫
    ((singularHomologyNatToIntIso AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app
        (LoopCellSphericalGenerators.liftedPair X x P).fst).hom ≫
    LoopCellSphericalGenerators.relativeProjection X x P

/-- The coefficient-domain boundary is the same original relative boundary after its actual
three-cell coordinate map. -/
theorem actualThreeToTwoBoundary_eq (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    actualThreeToTwoBoundary X x P =
      (upstairsThreeCoefficientIso X x P).hom ≫ actualThreeRelativeBoundary X x P := by
  rfl

/-- The same actual boundary gives the complete two-cell basis on all three-cell columns. -/
theorem actualThreeRelativeBoundary_basis (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (upstairsThreeCoefficientIso X x P).hom ≫ actualThreeRelativeBoundary X x P =
      (nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).hom := by
  exact actualThreeToTwoBoundary_eq_basis X x P

/-- The actual boundary is equivariant for the SAME geometric actions on both original pairs. -/
theorem actualThreeRelativeBoundary_deck (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).map (upstairsThreeDeckPair X x P q) ≫
      actualThreeRelativeBoundary X x P =
        actualThreeRelativeBoundary X x P ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{u}
            (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
              (LoopCellQuotientCellPresentation.nativeDeckPair X x P q) := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let e3 := upstairsThreeCoefficientIso X x P
  let e2 := nativeCoefficientBasisIso X x P R
  let b := actualThreeRelativeBoundary X x P
  let d3 := (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 3).map
      (upstairsThreeDeckPair X x P q)
  let d2 := (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map
    (LoopCellQuotientCellPresentation.nativeDeckPair X x P q)
  have hB : e3.hom ≫ b = e2.hom := actualThreeRelativeBoundary_basis X x P
  apply (cancel_epi e3.hom).mp
  apply Sigma.hom_ext
  intro i
  rcases i with ⟨r,p⟩
  let j := Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (r,p)
  let k := Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (q*r,p)
  have h3 : k ≫ e3.hom = (j ≫ e3.hom) ≫ d3 := upstairsThreeCoefficientIso_deck X x P q r p
  have h2 : k ≫ e2.hom = (j ≫ e2.hom) ≫ d2 := nativeCoefficientBasisIso_deck X x P R q r p
  have hL : j ≫ (e3.hom ≫ (d3 ≫ b)) = k ≫ e2.hom :=
    (Category.assoc j e3.hom (d3 ≫ b)).symm.trans
      ((Category.assoc (j ≫ e3.hom) d3 b).symm.trans
        ((congrArg (fun f => f ≫ b) h3.symm).trans
          ((Category.assoc k e3.hom b).trans (congrArg (fun f => k ≫ f) hB))))
  have hR : j ≫ (e3.hom ≫ (b ≫ d2)) = k ≫ e2.hom :=
    (congrArg (fun f => j ≫ f) (Category.assoc e3.hom b d2).symm).trans
      ((congrArg (fun f => j ≫ (f ≫ d2)) hB).trans
        ((Category.assoc j e2.hom d2).symm.trans h2.symm))
  exact hL.trans hR.symm

/-- The actual boundary is a morphism of the full original noncommutative quotient-ring modules. -/
def actualThreeToTwoLambdaMap (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    letI := upstairsThreeDeckModule X x P
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    upstairsThreeHomology X x P →ₗ[quotientGroupRing X x P]
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  letI := upstairsThreeDeckModule X x P
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let b := actualThreeRelativeBoundary X x P
  refine
    { toFun := b
      map_add' := b.hom.map_add
      map_smul' := ?_ }
  intro r a
  let f : quotientGroupRing X x P →+
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
    { toFun := fun s => b (s • a)
      map_zero' := by rw [zero_smul, map_zero]
      map_add' := by intro s t; rw [add_smul, map_add] }
  let g : quotientGroupRing X x P →+
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
    { toFun := fun s => s • b a
      map_zero' := zero_smul _ _
      map_add' := fun s t => add_smul s t (b a) }
  have h : f = g := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro q z
    have hDeck : b (upstairsThreeDeckRepresentation X x P q a) =
        nativeDeckRepresentation X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) q (b a) :=
      ConcreteCategory.congr_hom (actualThreeRelativeBoundary_deck X x P q) a
    exact (congrArg b (upstairsThreeDeckModule_single X x P q z a)).trans
      ((b.hom.map_zsmul z _).trans
        ((congrArg (fun c => z • c) hDeck).trans
          (nativeDeckModule_single X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) q z
              (b a)).symm))
  exact congrArg (fun h => h r) h

/-- The actual three-cell boundary is an isomorphism, as certified by its
complete original coefficient columns rather than their augmentation. -/
def actualThreeRelativeBoundaryIso (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    upstairsThreeHomology X x P ≅
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  (upstairsThreeCoefficientIso X x P).symm ≪≫
    nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})

/-- Its forward map is the SAME actual LES boundary and native relative quotient. -/
theorem actualThreeRelativeBoundaryIso_hom (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (actualThreeRelativeBoundaryIso X x P).hom = actualThreeRelativeBoundary X x P := by
  let e3 := upstairsThreeCoefficientIso X x P
  let e2 := nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  apply (cancel_epi e3.hom).mp
  exact (e3.hom_inv_id_assoc e2.hom).trans (actualThreeRelativeBoundary_basis X x P).symm

/-- The SAME actual boundary, now with its strict quotient-ring linear inverse. -/
def actualThreeToTwoLambdaEquiv (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    letI := upstairsThreeDeckModule X x P
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    upstairsThreeHomology X x P ≃ₗ[quotientGroupRing X x P]
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  letI := upstairsThreeDeckModule X x P
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let f := actualThreeToTwoLambdaMap X x P
  let e := actualThreeRelativeBoundaryIso X x P
  let a := e.addCommGroupIsoToAddEquiv
  have h : (fun z => f z) = fun z => e.hom z :=
    funext (fun z => (ConcreteCategory.congr_hom (actualThreeRelativeBoundaryIso_hom X x P) z).symm)
  have hb : Function.Bijective (fun z => f z) := h.symm ▸ a.bijective
  exact LinearEquiv.ofBijective f hb

private theorem actualThreeToTwoLambdaEquiv_apply (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (a : upstairsThreeHomology X x P) :
    actualThreeToTwoLambdaEquiv X x P a = actualThreeRelativeBoundary X x P a := by
  rfl

/-- The complete quotient-ring basis of the actual three-cell relative group. -/
def upstairsThreeLambdaBasisIso (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    letI := upstairsThreeDeckModule X x P
    (P →₀ quotientGroupRing X x P) ≃ₗ[quotientGroupRing X x P] upstairsThreeHomology X x P := by
  letI := upstairsThreeDeckModule X x P
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  exact (nativeLambdaBasisIso X x P).trans (actualThreeToTwoLambdaEquiv X x P).symm

/-- The ENTIRE actual three-to-two matrix in those quotient-ring coordinates. -/
def actualThreeToTwoLambdaMatrix (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (P →₀ quotientGroupRing X x P) →ₗ[quotientGroupRing X x P] (P →₀ quotientGroupRing X x P) := by
  letI := upstairsThreeDeckModule X x P
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  exact (nativeLambdaBasisIso X x P).symm.toLinearMap.comp
    ((actualThreeToTwoLambdaMap X x P).comp (upstairsThreeLambdaBasisIso X x P).toLinearMap)

/-- The whole actual matrix is identity over the NONCOMMUTATIVE quotient-group ring. -/
theorem actualThreeToTwoLambdaMatrix_eq_id (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    actualThreeToTwoLambdaMatrix X x P = LinearMap.id := by
  let := upstairsThreeDeckModule X x P
  let := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  apply LinearMap.ext
  intro a
  let e := nativeLambdaBasisIso X x P
  let b := actualThreeToTwoLambdaEquiv X x P
  change e.symm (b (b.symm (e a))) = a
  exact (congrArg e.symm (b.apply_symm_apply (e a))).trans (e.symm_apply_apply a)

private theorem upstairsThreeLambdaBasisIso_apply_cached (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (a : P →₀ quotientGroupRing X x P) :
    letI := upstairsThreeDeckModule X x P
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    upstairsThreeLambdaBasisIso X x P a =
      (actualThreeToTwoLambdaEquiv X x P).symm (nativeLambdaBasisIso X x P a) := by rfl

private theorem actualThreeToTwoLambdaEquiv_add_eq_cached (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    letI := upstairsThreeDeckModule X x P
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    (actualThreeToTwoLambdaEquiv X x P).toAddEquiv =
      (actualThreeRelativeBoundaryIso X x P).addCommGroupIsoToAddEquiv := by
  let := upstairsThreeDeckModule X x P
  let := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  have hCat := actualThreeRelativeBoundaryIso_hom X x P
  exact AddEquiv.ext (fun t => (actualThreeToTwoLambdaEquiv_apply X x P t).trans
    (ConcreteCategory.congr_hom hCat t).symm)

private theorem upstairsThreeCoefficientIso_boundary_cached (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
      (upstairsThreeCoefficientIso X x P).hom) ≫ (actualThreeRelativeBoundaryIso X x P).hom =
        Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
          (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
            (nativeCoefficientBasisIso X x P
                (singularIntegralCoefficients : AddCommGrpCat.{u})).hom := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let j := Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) i
  let e3 := upstairsThreeCoefficientIso X x P
  have hCat := actualThreeRelativeBoundaryIso_hom X x P
  exact (congrArg (fun f => (j ≫ e3.hom) ≫ f) hCat).trans
    ((Category.assoc j e3.hom (actualThreeRelativeBoundary X x P)).trans
      (congrArg (fun f => j ≫ f) (actualThreeRelativeBoundary_basis X x P)))

private theorem upstairsThreeCoefficientIso_inverse_boundary_cached (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
      (nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).hom) ≫
        (actualThreeRelativeBoundaryIso X x P).inv =
          Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
            (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
              (upstairsThreeCoefficientIso X x P).hom := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let j := Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) i
  let e2 := nativeCoefficientBasisIso X x P R
  let e3 := upstairsThreeCoefficientIso X x P
  let B : upstairsThreeHomology X x P ≅ nativeHomologyTwo X x P R :=
      actualThreeRelativeBoundaryIso X x P
  have hColumn : (j ≫ e3.hom) ≫ B.hom = j ≫ e2.hom :=
    upstairsThreeCoefficientIso_boundary_cached X x P i
  exact (congrArg (fun f : R ⟶ nativeHomologyTwo X x P R => f ≫ B.inv) hColumn).symm.trans
    ((Category.assoc (j ≫ e3.hom) B.hom B.inv).trans
      ((congrArg (fun f => (j ≫ e3.hom) ≫ f) B.hom_inv_id).trans (Category.comp_id _)))

private theorem nativeGenerator_coefficient_hom_cached (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (i : LoopCellQuotientCellPresentation.labels X x P) (z : ℤ) :
    (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
      (nativeCoefficientBasisIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u})).hom).hom
        (ULift.up z) = z • nativeGenerator X x P i := by
  exact nativeGenerator_coefficient X x P i (ULift.up z)

private theorem actualThreeBoundaryIso_inverse_column_cached (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    (actualThreeRelativeBoundaryIso X x P).inv (z • nativeGenerator X x P (q,p)) =
      (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) (q,p) ≫
          (upstairsThreeCoefficientIso X x P).hom) (ULift.up z) := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let Cells : AddCommGrpCat.{u} := ∐ fun _ : LoopCellQuotientCellPresentation.labels X x P => R
  let j : R ⟶ Cells := Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (q,p)
  let e2 : Cells ≅ nativeHomologyTwo X x P R := nativeCoefficientBasisIso X x P R
  let e3 : Cells ≅ upstairsThreeHomology X x P := upstairsThreeCoefficientIso X x P
  let B : upstairsThreeHomology X x P ≅ nativeHomologyTwo X x P R :=
      actualThreeRelativeBoundaryIso X x P
  have hInverse : (j ≫ e2.hom) ≫ B.inv = j ≫ e3.hom :=
    upstairsThreeCoefficientIso_inverse_boundary_cached X x P (q,p)
  have hValue : B.inv.hom ((j ≫ e2.hom).hom (ULift.up z)) = (j ≫ e3.hom).hom (ULift.up z) :=
    congrArg (fun f : R ⟶ upstairsThreeHomology X x P => f.hom (ULift.up z)) hInverse
  have hCoefficient : (j ≫ e2.hom).hom (ULift.up z) = z • nativeGenerator X x P (q,p) :=
    nativeGenerator_coefficient_hom_cached X x P (q,p) z
  exact (congrArg (fun t : nativeHomologyTwo X x P R => B.inv.hom t) hCoefficient).symm.trans hValue

private theorem upstairsThreeLambdaBasisIso_apply_category_cached (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (a : P →₀ quotientGroupRing X x P) :
    letI := upstairsThreeDeckModule X x P
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    upstairsThreeLambdaBasisIso X x P a =
      (actualThreeRelativeBoundaryIso X x P).inv (nativeLambdaBasisIso X x P a) := by
  let := upstairsThreeDeckModule X x P
  let := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  have hAdd := actualThreeToTwoLambdaEquiv_add_eq_cached X x P
  exact (upstairsThreeLambdaBasisIso_apply_cached X x P a).trans
    (congrArg (fun e : upstairsThreeHomology X x P ≃+
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) =>
        e.symm (nativeLambdaBasisIso X x P a)) hAdd)

private theorem upstairsThreeLambdaBasisIso_single_cached (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    letI := upstairsThreeDeckModule X x P
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    upstairsThreeLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z)) =
      (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) (q,p) ≫
          (upstairsThreeCoefficientIso X x P).hom) (ULift.up z) := by
  let := upstairsThreeDeckModule X x P
  let := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let a : P →₀ quotientGroupRing X x P := Finsupp.single p (MonoidAlgebra.single q z)
  exact (upstairsThreeLambdaBasisIso_apply_category_cached X x P a).trans
    ((congrArg (actualThreeRelativeBoundaryIso X x P).inv
      (nativeLambdaBasisIso_single X x P q p z)).trans
        (actualThreeBoundaryIso_inverse_column_cached X x P q p z))

/-- Every three-cell quotient-ring basis column is the actual labelled
closed-disk relative class, with its entire integer coefficient. -/
theorem upstairsThreeLambdaBasisIso_single (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    upstairsThreeLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z)) =
      (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) (q,p) ≫
          (upstairsThreeCoefficientIso X x P).hom) (ULift.up z) := by
  exact upstairsThreeLambdaBasisIso_single_cached X x P q p z

/-- The inverse recovers every actual three-disk coefficient and quotient label. -/
theorem upstairsThreeLambdaBasisIso_inverse_single (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    (upstairsThreeLambdaBasisIso X x P).symm
      ((Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) (q,p) ≫
          (upstairsThreeCoefficientIso X x P).hom) (ULift.up z)) =
      Finsupp.single p (MonoidAlgebra.single q z) := by
  exact (congrArg (upstairsThreeLambdaBasisIso X x P).symm
    (upstairsThreeLambdaBasisIso_single X x P q p z).symm).trans
      ((upstairsThreeLambdaBasisIso X x P).symm_apply_apply _)

/-- The literal quotient label in the original regular singular basepoint,
using the computed native connector and the proved point equality. -/
def originalQuotientDeckIndex (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    FundamentalGroup X x ⧸ P ≃*
      End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm
        (LoopCellAttachment.inclusion X x P x))) :=
  (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm.trans
    ((eqToIso (congrArg SSet.FundamentalGroupoid.mk (nativeTargetPoint_eq_original X x P))).conj)

/-- The actual pair action with its native point and SAME old pullback map. -/
def nativeDeckSimplicialPair (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    LoopCellPulledSimplicialModel.nativePair X x P ⟶
        LoopCellPulledSimplicialModel.nativePair X x P :=
  SSetPair.ofHom (LoopCellQuotientCellPresentation.nativeDeck X x P q)
    (LoopCellQuotientCellPresentation.oldDeck X x P q)
      (LoopCellQuotientCellPresentation.oldDeck_toCover X x P q)

/-- The whole original pulled-cover component is retained by the simplicial action. -/
theorem nativeDeckSimplicialPair_left (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    (nativeDeckSimplicialPair X x P q).hom.left =
        LoopCellQuotientCellPresentation.oldDeck X x P q := by
  rfl

/-- The ambient simplicial action is the SAME actual native deck map. -/
theorem nativeDeckSimplicialPair_right (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    (nativeDeckSimplicialPair X x P q).hom.right =
        LoopCellQuotientCellPresentation.nativeDeck X x P q := by
  rfl

/-- The original regular relative homology action is induced by its actual
coefficient natural transformation and original cokernel, without transport as a definition. -/
def originalRegularDeckHomologyMap (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    originalRegularHomologyTwo X x P ⟶ originalRegularHomologyTwo X x P :=
  HomologicalComplex.homologyMap
    (TopCat.originalRegularRelativeDeckChainMap (LoopCellAttachment.inclusion X x P)
      (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q)) 2

private theorem pairedDeck_equals_native (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    OriginalNativeRelativeBasis.pairedDeckAtVertex
        (LoopCellSphericalGenerators.nativeInclusion X x P)
        (LoopCellSphericalGenerators.nativeTargetPoint X x P)
          ((LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q) =
      nativeDeckSimplicialPair X x P q := by
  let f := LoopCellSphericalGenerators.nativeInclusion X x P
  let y := LoopCellSphericalGenerators.nativeTargetPoint X x P
  let a := (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q
  let d := SSet.KanComplex.nativeRegularPullbackDeckMap f y a
  let d' := LoopCellQuotientCellPresentation.oldDeck X x P q
  have hOld : d = d' := by
    apply pullback.hom_ext
    · exact (SSet.KanComplex.nativeRegularPullbackDeckMap_fst f y a).trans
        (LoopCellQuotientCellPresentation.oldDeck_source X x P q).symm
    · exact (SSet.KanComplex.nativeRegularPullbackDeckMap_snd f y a).trans
        (LoopCellQuotientCellPresentation.oldDeck_toCover X x P q).symm
  apply MorphismProperty.Arrow.Hom.ext
  · change d = d'
    exact hOld
  · rfl

private theorem originalDeckPair_equals_atVertex {A Y : TopCat.{u}} (f : A ⟶ Y) [Mono f]
    (y : Y) (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    TopCat.originalRegularNativeDeckPair f y a =
      OriginalNativeRelativeBasis.pairedDeckAtVertex (TopCat.toSSet.map f)
          (TopCat.toSSetObj₀Equiv.symm y) a := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact TopCat.originalRegularNativeDeckPair_left f y a
  · exact TopCat.originalRegularNativeDeckPair_right f y a

/-- The SAME original regular pair action is carried to the chosen native
pair by the derived singular-point equality. -/
theorem originalRegularDeckPair_to_native (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    TopCat.originalRegularNativeDeckPair (LoopCellAttachment.inclusion X x P)
        (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q) ≫
      (eqToIso (originalRegularPair_eq_native X x P)).hom =
        (eqToIso (originalRegularPair_eq_native X x P)).hom ≫ nativeDeckSimplicialPair X x P q := by
  let f := LoopCellSphericalGenerators.nativeInclusion X x P
  let w := LoopCellSphericalGenerators.nativeTargetPoint X x P
  let y := TopCat.toSSetObj₀Equiv.symm (LoopCellAttachment.inclusion X x P x)
  let h : w = y := nativeTargetPoint_eq_original X x P
  let a := (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q
  let e := eqToIso (congrArg (OriginalNativeRelativeBasis.pairedCoverAtVertex f) h)
  let dW := OriginalNativeRelativeBasis.pairedDeckAtVertex f w a
  let dY := OriginalNativeRelativeBasis.pairedDeckAtVertex f y (originalQuotientDeckIndex X x P q)
  have hMap : dW ≫ e.hom = e.hom ≫ dY :=
    OriginalNativeRelativeBasis.pairedDeck_point_transport f h a
  have hInverse : dY ≫ e.inv = e.inv ≫ dW := by
    apply (cancel_mono e.hom).mp
    have hL : (dY ≫ e.inv) ≫ e.hom = dY :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => dY ≫ k) e.inv_hom_id).trans (Category.comp_id _))
    have hR : (e.inv ≫ dW) ≫ e.hom = dY :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => e.inv ≫ k) hMap).trans (e.inv_hom_id_assoc dY))
    exact hL.trans hR.symm
  have hOriginal := originalDeckPair_equals_atVertex (LoopCellAttachment.inclusion X x P)
    (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q)
  have hNative := pairedDeck_equals_native X x P q
  have hCast : e.inv = (eqToIso (originalRegularPair_eq_native X x P)).hom := by
    rfl
  exact
      (congrArg (fun d => d ≫ (eqToIso (originalRegularPair_eq_native X x P)).hom)
        hOriginal).trans
    ((congrArg (fun t => dY ≫ t) hCast.symm).trans
      (hInverse.trans
        ((congrArg (fun d => e.inv ≫ d) hNative).trans
          (congrArg (fun t => t ≫ nativeDeckSimplicialPair X x P q) hCast))))

/-- The SAME relative unit intertwines the actual simplicial and realized
paired deck maps, on entire chains and arbitrary additive coefficients. -/
theorem nativeRelativeUnitChainMap_deck (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (R : AddCommGrpCat.{u}) :
    SSetPair.chainComplexMap (nativeDeckSimplicialPair X x P q) R ≫
        nativeRelativeUnitChainMap X x P R =
      nativeRelativeUnitChainMap X x P R ≫ (relativeSingularChainFunctor AddCommGrpCat.{u} R).map
        (LoopCellQuotientCellPresentation.nativeDeckPair X x P q) := by
  let A := LoopCellPulledSimplicialModel.nativePair X x P
  let T := LoopCellSphericalGenerators.liftedPair X x P
  let C := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  let K := (singularChainComplexFunctor AddCommGrpCat.{u}).obj R
  let d := LoopCellQuotientCellPresentation.nativeDeck X x P q
  let σ := nativeDeckSimplicialPair X x P q
  let τ := LoopCellQuotientCellPresentation.nativeDeckPair X x P q
  let qS := A.chainComplexπ R
  let qT := relativeSingularChainQuotient AddCommGrpCat.{u} R T
  let u := C.map (sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P))
  let g := nativeRelativeUnitChainMap X x P R
  let dS := SSetPair.chainComplexMap σ R
  let dA := C.map d
  let dT := (relativeSingularChainFunctor AddCommGrpCat.{u} R).map τ
  let dAbs := K.map (SSet.toTop.map d)
  have hS : qS ≫ dS = dA ≫ qS :=
    (((SSetPair.chainComplexFunctorπ AddCommGrpCat.{u}).app R).naturality σ).symm.trans
      (congrArg (fun f => C.map f ≫ qS) (nativeDeckSimplicialPair_right X x P q))
  have hT : qT ≫ dT = dAbs ≫ qT :=
    (relativeSingularChainQuotient_naturality AddCommGrpCat.{u} R τ).trans
      (congrArg (fun f => K.map f ≫ qT)
          (LoopCellQuotientCellPresentation.nativeDeckPair_fst X x P q))
  have hUnit : d ≫ sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P) =
      sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P) ≫
        TopCat.toSSet.map (SSet.toTop.map d) := by
    simpa only [Functor.id_map, Functor.comp_map] using sSetTopAdj.unit.naturality d
  have hU : dA ≫ u = u ≫ dAbs :=
    (C.map_comp _ _).symm.trans ((congrArg C.map hUnit).trans (C.map_comp _ _))
  have hQ : qS ≫ g = u ≫ qT := nativeRelativeUnitChainMap_projection X x P R
  apply (cancel_epi qS).mp
  have hL : qS ≫ (dS ≫ g) = (u ≫ qT) ≫ dT :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ g) hS).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => dA ≫ f) hQ).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun f => f ≫ qT) hU).trans
                ((Category.assoc _ _ _).trans
                  ((congrArg (fun f => u ≫ f) hT.symm).trans (Category.assoc _ _ _).symm)))))))
  have hR : qS ≫ (g ≫ dT) = (u ≫ qT) ≫ dT :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ dT) hQ)
  exact hL.trans hR.symm

/-- The actual native relative homology unit has the same equivariance in every degree. -/
theorem nativeRelativeUnitHomologyIso_deck (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (R : AddCommGrpCat.{u}) (n : ℕ) :
    SSetPair.homologyMap (nativeDeckSimplicialPair X x P q) R n ≫
        (nativeRelativeUnitHomologyIso X x P R n).hom =
      (nativeRelativeUnitHomologyIso X x P R n).hom ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map
          (LoopCellQuotientCellPresentation.nativeDeckPair X x P q) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n
  rw [nativeRelativeUnitHomologyIso_hom]
  change H.map (SSetPair.chainComplexMap (nativeDeckSimplicialPair X x P q) R) ≫
      H.map (nativeRelativeUnitChainMap X x P R) =
    H.map (nativeRelativeUnitChainMap X x P R) ≫
      H.map ((relativeSingularChainFunctor AddCommGrpCat.{u} R).map
        (LoopCellQuotientCellPresentation.nativeDeckPair X x P q))
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map (nativeRelativeUnitChainMap_deck X x P q R)).trans (H.map_comp _ _))

/-- The full original regular quotient-chain comparison preserves the
original coefficient action after the actual point transport. -/
theorem originalRegularNativeChainIso_deck (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (TopCat.originalRegularRelativeDeckChainMap (LoopCellAttachment.inclusion X x P)
          (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q)) ≫
      (originalRegularNativeChainIso X x P).hom =
        (originalRegularNativeChainIso X x P).hom ≫
          SSetPair.chainComplexMap (nativeDeckSimplicialPair X x P q)
            (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let f := LoopCellAttachment.inclusion X x P
  let y := f x
  let a := originalQuotientDeckIndex X x P q
  let A := TopCat.originalRegularPulledCoverPair f y
  let B := LoopCellPulledSimplicialModel.nativePair X x P
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let S := (SSetPair.chainComplexFunctor AddCommGrpCat.{u}).obj
    (singularIntegralCoefficients : AddCommGrpCat.{u})
  let e := TopCat.originalRegularRelativeChainIso f y
  let eF := OriginalNativeRelativeBasis.forgetRelativeChainIso A
  let h : A = B := originalRegularPair_eq_native X x P
  let t := eqToIso (congrArg S.obj h)
  let t0 := eqToIso h
  let m := TopCat.originalRegularRelativeDeckChainMap f y a
  let σ := TopCat.originalRegularNativeDeckPair f y a
  let τ := nativeDeckSimplicialPair X x P q
  let σM := SSetPair.chainComplexMap σ R
  let σA := S.map σ
  let τA := S.map τ
  have h1 : F.map m ≫ F.map e.hom = F.map e.hom ≫ F.map σM :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map (TopCat.originalRegularRelativeChainIso_deck f y a)).trans (F.map_comp _ _))
  have h2 : F.map σM ≫ eF.hom = eF.hom ≫ σA :=
    OriginalNativeRelativeBasis.forgetRelativeChainIso_naturality σ
  have hTag : S.map t0.hom = t.hom := eqToHom_map S h
  have h3 : σA ≫ t.hom = t.hom ≫ τA :=
    (congrArg (fun f => σA ≫ f) hTag.symm).trans
      ((S.map_comp σ t0.hom).symm.trans
        ((congrArg S.map (originalRegularDeckPair_to_native X x P q)).trans
          ((S.map_comp t0.hom τ).trans (congrArg (fun f => f ≫ τA) hTag))))
  change F.map m ≫ (F.map e.hom ≫ eF.hom ≫ t.hom) =
    (F.map e.hom ≫ eF.hom ≫ t.hom) ≫ τA
  have h12 : F.map m ≫ (F.map e.hom ≫ eF.hom) = F.map e.hom ≫ (eF.hom ≫ σA) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ eF.hom) h1).trans
        ((Category.assoc _ _ _).trans (congrArg (fun f => F.map e.hom ≫ f) h2)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ t.hom) h12).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => F.map e.hom ≫ f)
          ((Category.assoc _ _ _).trans (congrArg (fun f => eF.hom ≫ f) h3))).trans
            (by simp only [Category.assoc]))))

/-- The whole original regular H2 action intertwines with the SAME native
relative deck action, through the actual quotient and realization unit. -/
theorem originalRegularNativeHomologyIso_deck (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map (originalRegularDeckHomologyMap X x P q) ≫
      (originalRegularNativeHomologyIso X x P).hom =
        (originalRegularNativeHomologyIso X x P).hom ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{u}
            (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
              (LoopCellQuotientCellPresentation.nativeDeckPair X x P q) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 2
  let C := TopCat.originalRegularRelativeChainComplex (LoopCellAttachment.inclusion X x P)
    (LoopCellAttachment.inclusion X x P x)
  let c := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 2 U
  let m := TopCat.originalRegularRelativeDeckChainMap (LoopCellAttachment.inclusion X x P)
    (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q)
  let e := originalRegularNativeChainIso X x P
  let u := nativeRelativeUnitHomologyIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) 2
  let dS := SSetPair.homologyMap (nativeDeckSimplicialPair X x P q)
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 2
  let dT := (relativeSingularHomologyFunctor AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
      (LoopCellQuotientCellPresentation.nativeDeckPair X x P q)
  have h1 : U.map (HomologicalComplex.homologyMap m 2) ≫ c.inv.app C =
      c.inv.app C ≫ H.map (F.map m) := c.inv.naturality m
  have h2 : H.map (F.map m) ≫ H.map e.hom = H.map e.hom ≫ dS :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (originalRegularNativeChainIso_deck X x P q)).trans (H.map_comp _ _))
  have h3 : dS ≫ u.hom = u.hom ≫ dT :=
    nativeRelativeUnitHomologyIso_deck X x P q (singularIntegralCoefficients : AddCommGrpCat.{u}) 2
  change U.map (HomologicalComplex.homologyMap m 2) ≫ (c.inv.app C ≫ H.map e.hom ≫ u.hom) =
    (c.inv.app C ≫ H.map e.hom ≫ u.hom) ≫ dT
  have h12 : U.map (HomologicalComplex.homologyMap m 2) ≫ (c.inv.app C ≫ H.map e.hom) =
      c.inv.app C ≫ (H.map e.hom ≫ dS) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ H.map e.hom) h1).trans
        ((Category.assoc _ _ _).trans (congrArg (fun f => c.inv.app C ≫ f) h2)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ u.hom) h12).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => c.inv.app C ≫ f)
          ((Category.assoc _ _ _).trans (congrArg (fun f => H.map e.hom ≫ f) h3))).trans
            ((congrArg (fun k => c.inv.app C ≫ k)
              (Category.assoc (H.map e.hom) u.hom dT).symm).trans
                (Category.assoc (c.inv.app C) (H.map e.hom ≫ u.hom) dT).symm))))

/-- The computed copy index is the original canonical quotient loop index,
with the proved singular point equality and no disk-path normalization. -/
theorem originalQuotientDeckIndex_eq_canonical (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    originalQuotientDeckIndex X x P q =
      (TopCat.singularFundamentalGroupoidEndMulEquiv (LoopCellAttachment.space X x P)
        (LoopCellAttachment.inclusion X x P x)).symm
          (LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P q) := by
  let Y : TopCat.{u} := LoopCellAttachment.space X x P
  let f : X ⟶ Y := LoopCellAttachment.inclusion X x P
  let K : SSet.{u} := TopCat.toSSet.obj Y
  let sx : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm x
  let F : SSet.FundamentalGroupoid (TopCat.toSSet.obj X) ⥤ SSet.FundamentalGroupoid K :=
    SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
  let A : SSet.FundamentalGroupoid K := F.obj (SSet.FundamentalGroupoid.mk sx)
  let B : SSet.FundamentalGroupoid K :=
    SSet.FundamentalGroupoid.mk (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let C : SSet.FundamentalGroupoid K :=
    SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x))
  let e : End B ≃* (FundamentalGroup X x ⧸ P) :=
      LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P
  let a : End B := e.symm q
  let Q : (FundamentalGroup X x ⧸ P) ≃* FundamentalGroup Y (f x) :=
    LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P
  let E : End C ≃* FundamentalGroup Y (f x) := TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
  let hPoint : B = C := congrArg SSet.FundamentalGroupoid.mk (nativeTargetPoint_eq_original X x P)
  let c : B ≅ C := eqToIso hPoint
  have hObj : A = B := SSet.mapFundamentalGroupoid_obj_mk (TopCat.toSSet.map f) sx
  have hMap : A = C := TopCat.singularMappedVertex_eq f x
  have hCast : (eqToIso (hObj.symm.trans hMap) : B ≅ C) = c := by rfl
  have hIndex : originalQuotientDeckIndex X x P q = c.conj a := by rfl
  have hCanonical : e a = Q.symm (E (originalQuotientDeckIndex X x P q)) :=
    (LoopCellNativeCoverCopies.nativeDeckGroupEquiv_canonical X x P a).trans
      ((congrArg (fun t : B ≅ C => Q.symm (E (t.conj a))) hCast).trans
        (congrArg (fun t : End C => Q.symm (E t)) hIndex.symm))
  have hL : Q.symm (E (originalQuotientDeckIndex X x P q)) = q :=
    hCanonical.symm.trans (e.apply_symm_apply q)
  apply E.injective
  apply Q.symm.injective
  have hR : Q.symm (E (E.symm (Q q))) = q :=
    (congrArg Q.symm (E.apply_symm_apply (Q q))).trans (Q.symm_apply_apply q)
  exact hL.trans hR.symm

/-- The original coefficient action uses the actual positive quotient loop;
its inverse precomposition is not an arbitrary conjugated label. -/
theorem originalQuotientDeckEnd_eq (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    TopCat.singularRegularEndHom (LoopCellAttachment.space X x P)
        (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q) =
      LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P q := by
  let Y := LoopCellAttachment.space X x P
  let y := LoopCellAttachment.inclusion X x P x
  let E := TopCat.singularFundamentalGroupoidEndMulEquiv Y y
  exact (TopCat.singularRegularEndHom_eq Y y (originalQuotientDeckIndex X x P q)).trans
    ((congrArg E (originalQuotientDeckIndex_eq_canonical X x P q)).trans (E.apply_symm_apply _))

/-- The LEFT quotient action on the original regular stalk has its literal
inverse-precomposition formula at the original basepoint. -/
theorem originalRegularCoefficient_left_formula (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P)
    (γ : _root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x) ⟶
      _root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)) :
    (TopCat.originalRegularDeckCoefficient (LoopCellAttachment.space X x P)
        (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q)).app
      (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))
          (FreeAbelianGroup.of γ) =
        FreeAbelianGroup.of
          (((LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P q)⁻¹).asHom ≫ γ) := by
  exact (TopCat.originalRegularDeckCoefficient_of (LoopCellAttachment.space X x P)
    (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q) _ γ).trans
      (congrArg (fun a => FreeAbelianGroup.of ((a⁻¹).asHom ≫ γ))
          (originalQuotientDeckEnd_eq X x P q))

/-- Positive forward path transport retains the RIGHT inverse quotient-ring convention. -/
theorem originalRegularCoefficient_right_inverse (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P)
    (t : (CategoryTheory.regularPathModuleCoefficientFunctor
      (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))).obj
        (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))) :
    (LoopCellAttachment.regularQuotientGroupRingIso X x P).hom
        ((CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))).map
            (FundamentalGroup.toArrow
                (LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P q)) t) =
      (LoopCellAttachment.regularQuotientGroupRingIso X x P).hom t *
          MonoidAlgebra.single q⁻¹ (1 : ℤ) := by
  simpa only [MulEquiv.symm_apply_apply] using
    LoopCellAttachment.regularQuotientGroupRingIso_postcomp_positive X x P
      (LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P q) t

/-- The actual quotient action on the ORIGINAL regular relative H2 group. -/
def originalRegularDeckRepresentation (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    FundamentalGroup X x ⧸ P →* AddMonoid.End (originalRegularHomologyTwo X x P) := by
  let ρ := fun q : FundamentalGroup X x ⧸ P =>
    (originalRegularDeckHomologyMap X x P q).hom.toAddMonoidHom
  let e := originalRegularNativeHomologyIso X x P
  let E := e.addCommGroupIsoToAddEquiv
  let N := nativeDeckRepresentation X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  have h : ∀ q a, e.hom (ρ q a) = N q (e.hom a) :=
    fun q a => ConcreteCategory.congr_hom (originalRegularNativeHomologyIso_deck X x P q) a
  refine { toFun := ρ, map_one' := ?_, map_mul' := ?_ }
  · ext a
    apply E.injective
    exact (h 1 a).trans (congrArg (fun r : AddMonoid.End _ => r (e.hom a)) N.map_one)
  · intro q r
    ext a
    apply E.injective
    have hL : e.hom (ρ (q*r) a) = N q (N r (e.hom a)) :=
      (h (q*r) a).trans (congrArg (fun s : AddMonoid.End _ => s (e.hom a)) (N.map_mul q r))
    have hR : e.hom (ρ q (ρ r a)) = N q (N r (e.hom a)) :=
      (h q (ρ r a)).trans (congrArg (N q) (h r a))
    exact hL.trans hR.symm

/-- Linearize the SAME original coefficient action, retaining its literal quotient group. -/
def originalRegularDeckRingHom (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    quotientGroupRing X x P →+* AddMonoid.End (originalRegularHomologyTwo X x P) :=
  MonoidAlgebra.liftNCRingHom (Int.castRingHom (AddMonoid.End (originalRegularHomologyTwo X x P)))
    (originalRegularDeckRepresentation X x P)
    (fun z q => Int.cast_commute z (originalRegularDeckRepresentation X x P q))

/-- The quotient-ring module on the unchanged original regular-relative homology group. -/
def originalRegularDeckModule (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    Module (quotientGroupRing X x P) (originalRegularHomologyTwo X x P) :=
  Module.compHom (originalRegularHomologyTwo X x P) (originalRegularDeckRingHom X x P)

/-- Every single quotient-ring coefficient acts by the original coefficient-induced map. -/
theorem originalRegularDeckModule_single (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (z : ℤ) (a : originalRegularHomologyTwo X x P) :
    letI := originalRegularDeckModule X x P
    (MonoidAlgebra.single q z : quotientGroupRing X x P) • a =
      z • originalRegularDeckRepresentation X x P q a := by
  let := originalRegularDeckModule X x P
  have h : originalRegularDeckRingHom X x P (MonoidAlgebra.single q z) =
      (z : AddMonoid.End (originalRegularHomologyTwo X x P)) *
          originalRegularDeckRepresentation X x P q :=
    MonoidAlgebra.liftNCRingHom_single
      (Int.castRingHom (AddMonoid.End (originalRegularHomologyTwo X x P)))
      (originalRegularDeckRepresentation X x P) _ q z
  change originalRegularDeckRingHom X x P (MonoidAlgebra.single q z) a = _
  exact (congrArg (fun f : AddMonoid.End (originalRegularHomologyTwo X x P) => f a) h).trans (by
    change (z : AddMonoid.End (originalRegularHomologyTwo X x P))
      (originalRegularDeckRepresentation X x P q a) = _
    rw [AddMonoid.End.intCast_def]
    rfl)

/-- The actual original regular/native comparison is linear for the two
computed coefficient and geometric quotient-ring actions. -/
def originalRegularLambdaComparisonMap (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    letI := originalRegularDeckModule X x P
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    originalRegularHomologyTwo X x P →ₗ[quotientGroupRing X x P]
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  letI := originalRegularDeckModule X x P
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let e := originalRegularNativeHomologyIso X x P
  refine { toFun := e.hom, map_add' := e.hom.hom.map_add, map_smul' := ?_ }
  intro r a
  let f : quotientGroupRing X x P →+
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
    { toFun := fun s => e.hom (s • a)
      map_zero' := by rw [zero_smul, map_zero]
      map_add' := by intro s t; rw [add_smul, map_add] }
  let g : quotientGroupRing X x P →+
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
    { toFun := fun s => s • e.hom a
      map_zero' := zero_smul _ _
      map_add' := fun s t => add_smul s t (e.hom a) }
  have h : f = g := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro q z
    have hDeck : e.hom (originalRegularDeckRepresentation X x P q a) =
        nativeDeckRepresentation X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) q
            (e.hom a) :=
      ConcreteCategory.congr_hom (originalRegularNativeHomologyIso_deck X x P q) a
    exact (congrArg e.hom (originalRegularDeckModule_single X x P q z a)).trans
      ((e.hom.hom.map_zsmul z _).trans
        ((congrArg (fun c => z • c) hDeck).trans
          (nativeDeckModule_single X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) q z
              (e.hom a)).symm))
  exact congrArg (fun h => h r) h

/-- The SAME original regular/native comparison, with its genuine linear inverse. -/
def originalRegularLambdaComparisonIso (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    letI := originalRegularDeckModule X x P
    letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
    originalRegularHomologyTwo X x P ≃ₗ[quotientGroupRing X x P]
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  letI := originalRegularDeckModule X x P
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let f := originalRegularLambdaComparisonMap X x P
  exact LinearEquiv.ofBijective f
      (originalRegularNativeHomologyIso X x P).addCommGroupIsoToAddEquiv.bijective

/-- Its forward value is the original coefficient/quotient/unit comparison itself. -/
theorem originalRegularLambdaComparisonIso_apply (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (a : originalRegularHomologyTwo X x P) :
    originalRegularLambdaComparisonIso X x P a =
        (originalRegularNativeHomologyIso X x P).hom a := by
  rfl

/-- The linear inverse is the actual inverse original regular/native homology map. -/
theorem originalRegularLambdaComparisonIso_inverse_apply (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (a : nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u})) :
    (originalRegularLambdaComparisonIso X x P).symm a =
        (originalRegularNativeHomologyIso X x P).inv a := by
  let e := originalRegularLambdaComparisonIso X x P
  let E := originalRegularNativeHomologyIso X x P
  apply e.injective
  have hL : e (e.symm a) = a := e.apply_symm_apply a
  have hR : e (E.inv a) = a :=
    (originalRegularLambdaComparisonIso_apply X x P (E.inv a)).trans
      (ConcreteCategory.congr_hom E.inv_hom_id a)
  exact hL.trans hR.symm

/-- The ENTIRE original regular relative two-cell module is free over the
original quotient-group ring, with the actual geometric labelled generators. -/
def originalRegularLambdaBasisIso (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    letI := originalRegularDeckModule X x P
    (P →₀ quotientGroupRing X x P) ≃ₗ[quotientGroupRing X x P]
        originalRegularHomologyTwo X x P := by
  letI := originalRegularDeckModule X x P
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  exact (nativeLambdaBasisIso X x P).trans (originalRegularLambdaComparisonIso X x P).symm

/-- Every original free column is its SAME whole native two-disk class,
returned through the actual original coefficient comparison at every integer. -/
theorem originalRegularLambdaBasisIso_single (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    originalRegularLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z)) =
      (originalRegularNativeHomologyIso X x P).inv
        (((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u}
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
            (relativeSingularHomologyFunctor AddCommGrpCat.{u}
              (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
                (LoopCellQuotientCellPresentation.cellPairToCover X x P (q,p))) (ULift.up z)) := by
  let := originalRegularDeckModule X x P
  let := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let e := originalRegularLambdaComparisonIso X x P
  let b := nativeLambdaBasisIso X x P
  let a := Finsupp.single p (MonoidAlgebra.single q z)
  let E := originalRegularNativeHomologyIso X x P
  have hClass : z • nativeGenerator X x P (q,p) =
      (((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{u}
            (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
              (LoopCellQuotientCellPresentation.cellPairToCover X x P (q,p))) (ULift.up z)) :=
    (nativeGenerator_coefficient X x P (q,p) (ULift.up z)).symm.trans
      (ConcreteCategory.congr_hom (nativeCoefficientBasisIso_ι X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u}) (q,p)) (ULift.up z))
  change e.symm (b a) = _
  exact (originalRegularLambdaComparisonIso_inverse_apply X x P (b a)).trans
    (congrArg E.inv ((nativeLambdaBasisIso_single X x P q p z).trans hClass))

/-- The genuine inverse recovers every original regular two-cell quotient label and coefficient. -/
theorem originalRegularLambdaBasisIso_inverse_single (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    (originalRegularLambdaBasisIso X x P).symm
      ((originalRegularNativeHomologyIso X x P).inv
        (((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u}
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
            (relativeSingularHomologyFunctor AddCommGrpCat.{u}
              (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
                (LoopCellQuotientCellPresentation.cellPairToCover X x P (q,p))) (ULift.up z))) =
      Finsupp.single p (MonoidAlgebra.single q z) := by
  exact (congrArg (originalRegularLambdaBasisIso X x P).symm
    (originalRegularLambdaBasisIso_single X x P q p z).symm).trans
      ((originalRegularLambdaBasisIso X x P).symm_apply_apply _)

/-- LEFT deck multiplication is the original scalar action on the complete free module. -/
theorem originalRegularLambdaBasisIso_deck (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (v : P →₀ quotientGroupRing X x P) :
    originalRegularDeckRepresentation X x P q (originalRegularLambdaBasisIso X x P v) =
      originalRegularLambdaBasisIso X x P ((MonoidAlgebra.single q (1 : ℤ)) • v) := by
  let := originalRegularDeckModule X x P
  let e := originalRegularLambdaBasisIso X x P
  have hMap := e.map_smul (MonoidAlgebra.single q (1 : ℤ)) v
  have hAction : (MonoidAlgebra.single q (1 : ℤ)) • e v =
      originalRegularDeckRepresentation X x P q (e v) :=
    (originalRegularDeckModule_single X x P q 1 (e v)).trans (one_zsmul _)
  exact hAction.symm.trans hMap.symm

/-- The SAME actual upstairs boundary, transported to the ORIGINAL regular
relative two-cell module through its proven coefficient/unit comparison. -/
def actualThreeToOriginalRegularLambdaMap (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    letI := upstairsThreeDeckModule X x P
    letI := originalRegularDeckModule X x P
    upstairsThreeHomology X x P →ₗ[quotientGroupRing X x P] originalRegularHomologyTwo X x P := by
  letI := upstairsThreeDeckModule X x P
  letI := originalRegularDeckModule X x P
  letI := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  exact (originalRegularLambdaComparisonIso X x P).symm.toLinearMap.comp
      (actualThreeToTwoLambdaMap X x P)

/-- The transported boundary is the actual LES map followed by the SAME original inverse
comparison. -/
theorem actualThreeToOriginalRegularLambdaMap_apply (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (a : upstairsThreeHomology X x P) :
    actualThreeToOriginalRegularLambdaMap X x P a =
      (originalRegularNativeHomologyIso X x P).inv (actualThreeRelativeBoundary X x P a) :=
  originalRegularLambdaComparisonIso_inverse_apply X x P (actualThreeRelativeBoundary X x P a)

/-- The complete actual three-to-two matrix in the ORIGINAL regular-relative quotient-ring basis. -/
def actualOriginalRegularThreeToTwoMatrix (X : TopCat.{u}) [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (P →₀ quotientGroupRing X x P) →ₗ[quotientGroupRing X x P] (P →₀ quotientGroupRing X x P) := by
  letI := upstairsThreeDeckModule X x P
  letI := originalRegularDeckModule X x P
  exact (originalRegularLambdaBasisIso X x P).symm.toLinearMap.comp
    ((actualThreeToOriginalRegularLambdaMap X x P).comp
        (upstairsThreeLambdaBasisIso X x P).toLinearMap)

/-- Every original quotient coefficient is retained: the ENTIRE transported
matrix is identity, not only its ordinary integral augmentation. -/
theorem actualOriginalRegularThreeToTwoMatrix_eq_id (X : TopCat.{u})
    [PathConnectedSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    actualOriginalRegularThreeToTwoMatrix X x P = LinearMap.id := by
  let := upstairsThreeDeckModule X x P
  let := originalRegularDeckModule X x P
  let := nativeDeckModule X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let e := nativeLambdaBasisIso X x P
  let c := originalRegularLambdaComparisonIso X x P
  let b := actualThreeToTwoLambdaEquiv X x P
  apply LinearMap.ext
  intro a
  change e.symm (c (c.symm (b (b.symm (e a))))) = a
  exact (congrArg e.symm (c.apply_symm_apply _)).trans
    ((congrArg e.symm (b.apply_symm_apply (e a))).trans (e.symm_apply_apply a))

end AlgebraicTopology.LoopCellNativeRelativeBasis

end

/-!
# The original regular three-cell relative basis and boundary

The same upstairs spherical attachment is compared with the native cover of
Sing of the original three-cell space. The original regular cokernel and LES
are retained through their actual chain comparisons. The original coefficient
action gives the quotient-group-ring basis; the complete three-to-two matrix
is computed for every quotient/P label and integer coefficient.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology Topology
    Topology.CWComplex
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory


attribute [local instance] TopCat.toSSet_obj_kanComplex

namespace OriginalRegularThreeComparison

private theorem mono_from_simplexZero {K : SSet.{u}} (s : (Δ[0] : SSet.{u}) ⟶ K) : Mono s := by
  constructor
  intro Z f g _
  apply NatTrans.ext
  funext n
  rcases n with ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro z
  exact SSet.stdSimplex.ext _ _ (fun i => by
    apply Fin.ext
    exact (Nat.lt_one_iff.mp (((f.app (Opposite.op ⦋d⦌)) z) i).isLt).trans
      (Nat.lt_one_iff.mp (((g.app (Opposite.op ⦋d⦌)) z) i).isLt).symm)

/-- The actual model factorization and two original lifting squares extend
an existing weak comparison over a fibration while retaining its represented
basepoint. All comparison inputs are internal, computed in the applications. -/
private theorem exists_based_weak_extension
    {K L E B : SSet.{u}} (u : K ⟶ L) (g : K ⟶ E) (f : L ⟶ B) (p : E ⟶ B)
    [HomotopicalAlgebra.WeakEquivalence u] [HomotopicalAlgebra.WeakEquivalence g]
    [HomotopicalAlgebra.Fibration p] (s : (Δ[0] : SSet.{u}) ⟶ K)
    (h : g ≫ p = u ≫ f) :
    ∃ l : L ⟶ E, l ≫ p = f ∧ HomotopicalAlgebra.WeakEquivalence l ∧
      (s ≫ u) ≫ l = s ≫ g := by
  let d := MorphismProperty.factorizationData
    (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) u
  let j := d.i
  let q := d.p
  let : Cofibration j := (cofibration_iff _).mpr d.hi
  let : Fibration q := (fibration_iff _).mpr d.hp.1
  let : WeakEquivalence q := (weakEquivalence_iff _).mpr d.hp.2
  let : WeakEquivalence j := weakEquivalence_of_postcomp_of_fac d.fac
  have hjp : g ≫ p = j ≫ (q ≫ f) :=
    h.trans ((congrArg (fun k => k ≫ f) d.fac.symm).trans (Category.assoc j q f))
  let sq : CommSq g j p (q ≫ f) := ⟨hjp⟩
  let r : d.Z ⟶ E := sq.lift
  have hjr : j ≫ r = g := sq.fac_left
  have hrp : r ≫ p = q ≫ f := sq.fac_right
  let : WeakEquivalence r := weakEquivalence_of_precomp_of_fac hjr
  let a : (Δ[0] : SSet.{u}) ⟶ L := s ≫ u
  let b : (Δ[0] : SSet.{u}) ⟶ d.Z := s ≫ j
  let : Mono a := mono_from_simplexZero a
  let : Cofibration a := (SSet.modelCategoryQuillen.cofibration_iff a).mpr inferInstance
  have hb : b ≫ q = a ≫ 𝟙 L :=
    (Category.assoc s j q).trans
      ((congrArg (fun k => s ≫ k) d.fac).trans (Category.comp_id a).symm)
  let sqs : CommSq b a q (𝟙 L) := ⟨hb⟩
  let t : L ⟶ d.Z := sqs.lift
  have htq : t ≫ q = 𝟙 L := sqs.fac_right
  have hat : a ≫ t = b := sqs.fac_left
  let : WeakEquivalence t := weakEquivalence_of_postcomp_of_fac htq
  refine ⟨t ≫ r, ?_, inferInstance, ?_⟩
  · exact (Category.assoc t r p).trans
      ((congrArg (fun k => t ≫ k) hrp).trans
        ((Category.assoc t q f).symm.trans
          ((congrArg (fun k => k ≫ f) htq).trans (Category.id_comp f))))
  · change a ≫ (t ≫ r) = s ≫ g
    exact (Category.assoc a t r).symm.trans
      ((congrArg (fun k => k ≫ r) hat).trans
        ((Category.assoc s j r).trans (congrArg (fun k => s ≫ k) hjr)))

private theorem nativeProjection_fibration (Y : SSet.{u}) (y : Y _⦋0⦌) :
    HomotopicalAlgebra.Fibration (SSet.KanComplex.nativeCoverProjection Y y) := by
  let : Groupoid (Under (SSet.FundamentalGroupoid.mk y)) := Groupoid.ofIsGroupoid
  let : Fibration (SSet.KanComplex.nativeCoverNerveProjection Y y) :=
    CategoryTheory.nerve.fibration_nerveMap_of_isIsofibration
      (Under.forget (SSet.FundamentalGroupoid.mk y))
  change Fibration (pullback.fst (SSet.KanComplex.nativeCoverUnit Y)
    (SSet.KanComplex.nativeCoverNerveProjection Y y))
  infer_instance

private theorem nativeLift_eq_of_vertexRestriction {Y : SSet.{u}} {y : Y _⦋0⦌} {n : ℕ}
    (L M : (Δ[n] : SSet.{u}) ⟶ SSet.KanComplex.nativeCover Y y)
    (hP : L ≫ SSet.KanComplex.nativeCoverProjection Y y = M ≫
        SSet.KanComplex.nativeCoverProjection Y y)
    (theta : ⦋0⦌ ⟶ ⦋n⦌)
    (hVertex : SSet.stdSimplex.map theta ≫ L = SSet.stdSimplex.map theta ≫ M) : L = M := by
  let p := SSet.KanComplex.nativeCoverProjection Y y
  let sigma := L ≫ p
  let a : {L : (Δ[n] : SSet.{u}) ⟶ SSet.KanComplex.nativeCover Y y // L ≫ p = sigma} := ⟨L, rfl⟩
  let b : {L : (Δ[n] : SSet.{u}) ⟶ SSet.KanComplex.nativeCover Y y // L ≫ p = sigma} := ⟨M, hP.symm⟩
  let ta := SSet.KanComplex.nativeCoverSimplexFiberPathEquiv_restrict sigma theta a
  let tb := SSet.KanComplex.nativeCoverSimplexFiberPathEquiv_restrict sigma theta b
  have hR :
      (⟨SSet.stdSimplex.map theta ≫ L,
          (Category.assoc _ _ _).trans (congrArg
            (fun k => SSet.stdSimplex.map theta ≫ k) a.property)⟩ :
        {L : (Δ[0] : SSet.{u}) ⟶ SSet.KanComplex.nativeCover Y y //
          L ≫ p = SSet.stdSimplex.map theta ≫ sigma}) =
      ⟨SSet.stdSimplex.map theta ≫ M,
          (Category.assoc _ _ _).trans (congrArg
            (fun k => SSet.stdSimplex.map theta ≫ k) b.property)⟩ :=
    Subtype.ext hVertex
  have hPaths := ta.symm.trans
    ((congrArg (SSet.KanComplex.nativeCoverSimplexFiberPathEquiv
        (SSet.stdSimplex.map theta ≫ sigma)) hR).trans tb)
  have hFirst : SSet.KanComplex.nativeCoverSimplexFiberPathEquiv sigma a =
      SSet.KanComplex.nativeCoverSimplexFiberPathEquiv sigma b :=
    (cancel_mono (SSet.KanComplex.nativeCoverSimplexPathTransport sigma theta)).mp hPaths
  exact congrArg Subtype.val
      ((SSet.KanComplex.nativeCoverSimplexFiberPathEquiv sigma).injective hFirst)

/-- Cover lifts of the same connected source are determined by the actual
image of one represented vertex. The proof uses the existing native path
restriction equation and the original simplicial component quotient. -/
private theorem nativeLift_hom_ext_of_connected {K Y : SSet.{u}} [K.IsConnected] {y : Y _⦋0⦌}
    (L M : K ⟶ SSet.KanComplex.nativeCover Y y)
    (hP : L ≫ SSet.KanComplex.nativeCoverProjection Y y = M ≫
        SSet.KanComplex.nativeCoverProjection Y y)
    (k : K _⦋0⦌) (hk : L.app (Opposite.op ⦋0⦌) k = M.app (Opposite.op ⦋0⦌) k) : L = M := by
  let P := fun v : K _⦋0⦌ => (SSet.const v : (Δ[0] : SSet.{u}) ⟶ K) ≫ L = SSet.const v ≫ M
  have hEdge : ∀ {a b : K _⦋0⦌} (e : K.Edge a b), P a ↔ P b := by
    intro a b e
    let sigma : (Δ[1] : SSet.{u}) ⟶ K := SSet.yonedaEquiv.symm e.edge
    have hsrc : SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ sigma = SSet.const a :=
      (SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ (1 : Fin 2)) e.edge).trans
        ((congrArg SSet.yonedaEquiv.symm e.src_eq).trans (SSet.yonedaEquiv_symm_zero a))
    have htgt : SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ sigma = SSet.const b :=
      (SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ (0 : Fin 2)) e.edge).trans
        ((congrArg SSet.yonedaEquiv.symm e.tgt_eq).trans (SSet.yonedaEquiv_symm_zero b))
    have hp : (sigma ≫ L) ≫ SSet.KanComplex.nativeCoverProjection Y y =
        (sigma ≫ M) ≫ SSet.KanComplex.nativeCoverProjection Y y :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => sigma ≫ f) hP).trans (Category.assoc _ _ _).symm)
    have fromVertex : ∀ (theta : ⦋0⦌ ⟶ ⦋1⦌) (v : K _⦋0⦌)
        (hv : SSet.stdSimplex.map theta ≫ sigma = SSet.const v), P v → sigma ≫ L = sigma ≫ M := by
      intro theta v hv h
      apply nativeLift_eq_of_vertexRestriction (sigma ≫ L) (sigma ≫ M) hp theta
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ L) hv).trans
          (h.trans ((congrArg (fun f => f ≫ M) hv.symm).trans (Category.assoc _ _ _))))
    have toVertex : ∀ (theta : ⦋0⦌ ⟶ ⦋1⦌) (v : K _⦋0⦌)
        (hv : SSet.stdSimplex.map theta ≫ sigma = SSet.const v), sigma ≫ L = sigma ≫ M → P v := by
      intro theta v hv h
      exact (congrArg (fun f => f ≫ L) hv.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => SSet.stdSimplex.map theta ≫ f) h).trans
            ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ M) hv))))
    exact ⟨fun h => toVertex _ b htgt (fromVertex _ a hsrc h),
      fun h => toVertex _ a hsrc (fromVertex _ b htgt h)⟩
  have hAtK : P k := (SSet.const_comp k L).trans
    ((congrArg (fun v => (SSet.const v : (Δ[0] : SSet.{u}) ⟶
        SSet.KanComplex.nativeCover Y y)) hk).trans
      (SSet.const_comp k M).symm)
  have hAll : ∀ v : K _⦋0⦌, P v := by
    intro v
    have h : Relation.EqvGen (SSet.π₀Rel (X := K)) k v :=
      (SSet.π₀.mk_eq_mk_iff k v).mp (Subsingleton.elim _ _)
    have hTransport : ∀ {a b : K _⦋0⦌},
        Relation.EqvGen (SSet.π₀Rel (X := K)) a b → (P a ↔ P b) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
        obtain ⟨e⟩ := hab
        exact hEdge e
      | refl a => exact Iff.rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (hTransport h).mp hAtK
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro v
  let n := d.unop.len
  let sigma : (Δ[n] : SSet.{u}) ⟶ K := SSet.yonedaEquiv.symm v
  let theta : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const _ _ 0
  let a := SSet.yonedaEquiv (SSet.stdSimplex.map theta ≫ sigma)
  have ha : SSet.stdSimplex.map theta ≫ sigma = SSet.const a :=
    ((SSet.yonedaEquiv (X := K) (n := ⦋0⦌)).symm_apply_apply _).symm.trans
      (SSet.yonedaEquiv_symm_zero a)
  have hp : (sigma ≫ L) ≫ SSet.KanComplex.nativeCoverProjection Y y =
      (sigma ≫ M) ≫ SSet.KanComplex.nativeCoverProjection Y y :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => sigma ≫ f) hP).trans (Category.assoc _ _ _).symm)
  have hVertex : SSet.stdSimplex.map theta ≫ (sigma ≫ L) =
      SSet.stdSimplex.map theta ≫ (sigma ≫ M) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ L) ha).trans
        ((hAll a).trans ((congrArg (fun f => f ≫ M) ha.symm).trans (Category.assoc _ _ _))))
  have hSigma := nativeLift_eq_of_vertexRestriction (sigma ≫ L) (sigma ≫ M) hp theta hVertex
  have hValue := congrArg SSet.yonedaEquiv hSigma
  simpa only [SSet.yonedaEquiv_comp, sigma, Equiv.apply_symm_apply] using hValue

private theorem nativeLift_hom_ext_of_connected_pointMap {K Y : SSet.{u}}
    [K.IsConnected] {y : Y _⦋0⦌}
    (L M : K ⟶ SSet.KanComplex.nativeCover Y y)
    (hP : L ≫ SSet.KanComplex.nativeCoverProjection Y y = M ≫
        SSet.KanComplex.nativeCoverProjection Y y)
    (s : (Δ[0] : SSet.{u}) ⟶ K) (hs : s ≫ L = s ≫ M) : L = M := by
  apply nativeLift_hom_ext_of_connected L M hP (SSet.yonedaEquiv s)
  exact (SSet.yonedaEquiv_comp s L).symm.trans
    ((congrArg SSet.yonedaEquiv hs).trans (SSet.yonedaEquiv_comp s M))

private theorem unit_mate_projection {E : SSet.{u}} {Y : TopCat.{u}} (p : E ⟶ TopCat.toSSet.obj Y) :
    sSetTopAdj.unit.app E ≫ TopCat.toSSet.map (SSet.toTop.map p ≫ sSetTopAdj.counit.app Y) = p := by
  have h : (sSetTopAdj.homEquiv E Y).symm p = SSet.toTop.map p ≫ sSetTopAdj.counit.app Y := rfl
  have h' := (congrArg (sSetTopAdj.homEquiv E Y) h.symm).trans
    ((sSetTopAdj.homEquiv E Y).apply_symm_apply p)
  exact h'

private theorem actualOldSingularLiftExists (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    let Y := LoopCellAttachment.space X x P
    let E := LoopCellSphericalGenerators.nativeCover X x P
    let p := SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
      (LoopCellSphericalGenerators.nativeTargetPoint X x P)
    let a := SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj Y)
      (LoopCellSphericalGenerators.nativeTargetPoint X x P)
    ∃ l : TopCat.toSSet.obj (SSet.toTop.obj E) ⟶ E,
      l ≫ p = TopCat.toSSet.map (SSet.toTop.map p ≫ sSetTopAdj.counit.app Y) ∧
      WeakEquivalence l ∧ (a ≫ sSetTopAdj.unit.app E) ≫ l = a := by
  let Y := LoopCellAttachment.space X x P
  let E := LoopCellSphericalGenerators.nativeCover X x P
  let p := SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let a := SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj Y)
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let u := sSetTopAdj.unit.app E
  let v := sSetTopAdj.unit.app (TopCat.toSSet.obj Y)
  let c := TopCat.toSSet.map (sSetTopAdj.counit.app Y)
  let f := TopCat.toSSet.map (SSet.toTop.map p ≫ sSetTopAdj.counit.app Y)
  have hMap : f = TopCat.toSSet.map (SSet.toTop.map p) ≫ c :=
    TopCat.toSSet.map_comp (SSet.toTop.map p) (sSetTopAdj.counit.app Y)
  have hUnit : p ≫ v = u ≫ TopCat.toSSet.map (SSet.toTop.map p) :=
    sSetTopAdj.unit.naturality p
  have hTriangle : v ≫ c = 𝟙 (TopCat.toSSet.obj Y) := sSetTopAdj.right_triangle_components Y
  have h : u ≫ f = p :=
    (congrArg (fun k => u ≫ k) hMap).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ c) hUnit.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => p ≫ k) hTriangle).trans (Category.comp_id p)))))
  let : WeakEquivalence u := (weakEquivalence_iff _).mpr
    (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences E)
  let : WeakEquivalence (𝟙 E) := (weakEquivalence_iff _).mpr
    (SSet.realizationWeakEquivalences.id_mem E)
  let : Fibration p := nativeProjection_fibration _ _
  obtain ⟨l, hl, hw, ha⟩ := exists_based_weak_extension u (𝟙 E) f p a
    ((Category.id_comp p).trans h.symm)
  exact ⟨l, hl, hw, ha.trans (Category.comp_id a)⟩

private def boundaryThreeFirstVertex : (SSet.boundary.{u} 3).toSSet _⦋0⦌ :=
  ⟨SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 4), by
    rw [SSet.boundary_obj_eq_univ 0 3 (by decide)]
    exact Set.mem_univ _⟩

private theorem piZero_eq_of_fundamentalGroupoidHom {K : SSet.{u}}
    {a b : K _⦋0⦌} (f : SSet.FundamentalGroupoid.mk a ⟶ SSet.FundamentalGroupoid.mk b) :
    SSet.π₀.mk a = SSet.π₀.mk b := by
  have h : ∀ {x y : SSet.FundamentalGroupoid K} (g : x ⟶ y),
      SSet.π₀.mk x.pt = SSet.π₀.mk y.pt := by
    intro x y g
    induction g using SSet.FundamentalGroupoid.hom_rec with
    | homMk e => exact SSet.π₀.sound e
    | inv f hf => exact hf.symm
    | comp f g hf hg => exact hf.trans hg
  exact h f

/-- Connectedness is derived through the SAME two-truncation groupoid Iso:
the complete standard-simplex edge from0 to each vertex lifts by fullness,
then the original simplicial component quotient identifies those vertices. -/
private theorem boundaryThree_isConnected : (SSet.boundary.{u} 3).toSSet.IsConnected := by
  let f := (SSet.boundary.{u} 3).ι
  let : (SSet.mapFundamentalGroupoid f).IsIso :=
    SSet.isIso_mapFundamentalGroupoid_of_isIso f
      (AlgebraicTopology.CellFamilySimplicialModel.truncation_boundary_isIso 2 (by decide))
  let : (SSet.mapFundamentalGroupoid f).IsEquivalence := inferInstance
  have reach : ∀ v : (SSet.boundary.{u} 3).toSSet _⦋0⦌,
      SSet.π₀.mk boundaryThreeFirstVertex = SSet.π₀.mk v := by
    intro v
    let i : Fin 4 := SSet.stdSimplex.obj₀Equiv v.val
    let sigma : (Δ[3] : SSet.{u}) _⦋1⦌ :=
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.mkOfLe (n := 3) (0 : Fin 4) i (Fin.zero_le i))
    let e : (Δ[3] : SSet.{u}).Edge (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 4)) v.val :=
      SSet.Edge.mk sigma (by
        apply SSet.stdSimplex.obj₀Equiv.injective
        change (SimplexCategory.mkOfLe (n := 3) (0 : Fin 4) i (Fin.zero_le i)).toOrderHom 0 = 0
        rfl) (by
        apply SSet.stdSimplex.obj₀Equiv.injective
        change i = SSet.stdSimplex.obj₀Equiv v.val
        rfl)
    exact piZero_eq_of_fundamentalGroupoidHom
      ((SSet.mapFundamentalGroupoid f).preimage (SSet.FundamentalGroupoid.homMk e))
  apply (SSet.isConnected_iff (X := (SSet.boundary.{u} 3).toSSet)).mpr
  refine ⟨?_, ⟨boundaryThreeFirstVertex⟩⟩
  constructor
  intro a b
  obtain ⟨va, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨vb, rfl⟩ := SSet.π₀.mk_surjective b
  exact (reach va).symm.trans (reach vb)

private theorem pullbackCongr_fst {A B Y : SSet.{u}} {f g : A ⟶ Y}
    (p : B ⟶ Y) (h : f = g) :
    (pullback.congrHom h (rfl : p = p)).hom ≫ pullback.fst g p = pullback.fst f p := by
  simp only [pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]

private theorem pullbackCongr_snd {A B Y : SSet.{u}} {f g : A ⟶ Y}
    (p : B ⟶ Y) (h : f = g) :
    (pullback.congrHom h (rfl : p = p)).hom ≫ pullback.snd g p = pullback.snd f p := by
  simp only [pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]

private theorem fundamentalGroupoidHom_of_piZeroEq {Y : SSet.{u}}
    {a b : Y _⦋0⦌} (h : SSet.π₀.mk a = SSet.π₀.mk b) :
    Nonempty (SSet.FundamentalGroupoid.mk a ⟶ SSet.FundamentalGroupoid.mk b) := by
  have hR := (SSet.π₀.mk_eq_mk_iff a b).mp h
  have hTransport : ∀ {a b : Y _⦋0⦌},
      Relation.EqvGen (SSet.π₀Rel (X := Y)) a b →
        Nonempty (SSet.FundamentalGroupoid.mk a ⟶ SSet.FundamentalGroupoid.mk b) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      obtain ⟨e⟩ := hab
      exact ⟨SSet.FundamentalGroupoid.homMk e⟩
    | refl a => exact ⟨𝟙 _⟩
    | symm a b _ ih =>
      obtain ⟨f⟩ := ih
      exact ⟨inv f⟩
    | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨f⟩ := ih₁
      obtain ⟨g⟩ := ih₂
      exact ⟨f ≫ g⟩
  exact hTransport hR

/-- Fullness of the actual induced groupoid map reflects connectedness once
one actual source vertex is represented. No source Kan or connectedness is assumed. -/
private theorem connected_of_full_fundamentalGroupoid {K Y : SSet.{u}} [Y.IsConnected]
    (f : K ⟶ Y) [(SSet.mapFundamentalGroupoid f).Full] (k : K _⦋0⦌) : K.IsConnected := by
  apply (SSet.isConnected_iff (X := K)).mpr
  refine ⟨?_, ⟨k⟩⟩
  constructor
  intro a b
  obtain ⟨va, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨vb, rfl⟩ := SSet.π₀.mk_surjective b
  let F := SSet.mapFundamentalGroupoid f
  obtain ⟨g⟩ := fundamentalGroupoidHom_of_piZeroEq
    (Subsingleton.elim (SSet.π₀.mk (f.app (Opposite.op ⦋0⦌) va))
      (SSet.π₀.mk (f.app (Opposite.op ⦋0⦌) vb)))
  exact piZero_eq_of_fundamentalGroupoidHom (F.preimage g)

private theorem pairChainInclusion_transport {C : Type v} [Category.{w} C] [Abelian C]
    [HasCoproducts.{u} C] (A B : SSetPair.{u}) (h : A = B) (R : C) :
    SSet.chainComplexMap A.hom R ≫
      (eqToIso (congrArg (fun P : SSetPair.{u} => P.fst.chainComplex R) h)).hom =
        (eqToIso (congrArg (fun P : SSetPair.{u} => P.snd.chainComplex R) h)).hom ≫
          SSet.chainComplexMap B.hom R := by
  cases h
  change SSet.chainComplexMap A.hom R ≫ 𝟙 _ = 𝟙 _ ≫ SSet.chainComplexMap A.hom R
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end OriginalRegularThreeComparison

public section

namespace AlgebraicTopology.LoopCellRegularThreeComparison

open LoopCellNativeRelativeBasis

/-- The actual singular old-cover comparison is computed from the original
unit and native-cover fibration, with the original identity point retained. -/
def oldSingularToNative (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    TopCat.toSSet.obj (SSet.toTop.obj (LoopCellSphericalGenerators.nativeCover X x P)) ⟶
      LoopCellSphericalGenerators.nativeCover X x P :=
  Classical.choose (OriginalRegularThreeComparison.actualOldSingularLiftExists X x P)

/-- It projects by the original realized covering map followed by the
original counit, as a strict equality of singular maps. -/
theorem oldSingularToNative_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    oldSingularToNative X x P ≫ SSet.KanComplex.nativeCoverProjection
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
        (LoopCellSphericalGenerators.nativeTargetPoint X x P) =
      TopCat.toSSet.map
        (SSet.toTop.map (SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
            (LoopCellSphericalGenerators.nativeTargetPoint X x P)) ≫
          sSetTopAdj.counit.app (LoopCellAttachment.space X x P)) :=
  (Classical.choose_spec (OriginalRegularThreeComparison.actualOldSingularLiftExists X x P)).1

/-- Its weakness is derived from the actual original realization unit and
lifting squares, not supplied as an expected comparison. -/
theorem oldSingularToNative_weak (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
        SSet.realizationWeakEquivalences (oldSingularToNative X x P) :=
  (weakEquivalence_iff _).mp
    (Classical.choose_spec (OriginalRegularThreeComparison.actualOldSingularLiftExists X x P)).2.1

/-- The same actual identity-point map is fixed by the unit/comparison composite. -/
theorem oldSingularToNative_identityPoint (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (SSet.KanComplex.nativeCoverIdentityPointMap
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
          (LoopCellSphericalGenerators.nativeTargetPoint X x P) ≫
      sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P)) ≫
        oldSingularToNative X x P =
      SSet.KanComplex.nativeCoverIdentityPointMap
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
          (LoopCellSphericalGenerators.nativeTargetPoint X x P) :=
  (Classical.choose_spec (OriginalRegularThreeComparison.actualOldSingularLiftExists X x P)).2.2


/-- The unit followed by the computed comparison is the exact identity on
the SAME native cover, by connected-cover lift uniqueness at its actual point. -/
theorem oldSingularToNative_unit (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P) ≫
      oldSingularToNative X x P = 𝟙 _ := by
  let Y := LoopCellAttachment.space X x P
  let E := LoopCellSphericalGenerators.nativeCover X x P
  let p := SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let u := sSetTopAdj.unit.app E
  let l := oldSingularToNative X x P
  let f := TopCat.toSSet.map (SSet.toTop.map p ≫ sSetTopAdj.counit.app Y)
  let a := SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj Y)
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let : E.IsConnected := SSet.KanComplex.nativeCover_isConnected
  have hp : (u ≫ l) ≫ p = (𝟙 E) ≫ p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => u ≫ k) (oldSingularToNative_projection X x P)).trans
        ((OriginalRegularThreeComparison.unit_mate_projection p).trans (Category.id_comp p).symm))
  have ha : a ≫ (u ≫ l) = a ≫ 𝟙 E :=
    (Category.assoc _ _ _).symm.trans
      ((oldSingularToNative_identityPoint X x P).trans (Category.comp_id a).symm)
  exact OriginalRegularThreeComparison.nativeLift_hom_ext_of_connected_pointMap
    (K := E) (Y := TopCat.toSSet.obj Y)
      (y := LoopCellSphericalGenerators.nativeTargetPoint X x P) (u ≫ l) (𝟙 E) hp a ha

/-- The actual weak comparison respects EVERY native deck element. Point
compatibility follows from the whole unit identity, not an identity-path
normalization of any selected disk. -/
theorem oldSingularToNative_deck (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x))
    (a : End (SSet.FundamentalGroupoid.mk (LoopCellSphericalGenerators.nativeTargetPoint X x P))) :
    TopCat.toSSet.map
        (SSet.toTop.map (SSet.KanComplex.nativeCoverDeckMap a)) ≫ oldSingularToNative X x P =
      oldSingularToNative X x P ≫ SSet.KanComplex.nativeCoverDeckMap a := by
  let Y := LoopCellAttachment.space X x P
  let E := LoopCellSphericalGenerators.nativeCover X x P
  let p := SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let l := oldSingularToNative X x P
  let u := sSetTopAdj.unit.app E
  let d : E ⟶ E := SSet.KanComplex.nativeCoverDeckMap a
  let dd := TopCat.toSSet.map (SSet.toTop.map d)
  let f := TopCat.toSSet.map (SSet.toTop.map p ≫ sSetTopAdj.counit.app Y)
  let v := SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj Y)
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let : E.IsConnected := SSet.KanComplex.nativeCover_isConnected
  let : PathConnectedSpace (SSet.toTop.obj E) :=
    SSet.pathConnectedSpace_realization_of_isConnected E
  let : (TopCat.toSSet.obj (SSet.toTop.obj E)).IsConnected := inferInstance
  have hd : d ≫ p = p := SSet.KanComplex.nativeCoverDeckMap_projection a
  have hTop : SSet.toTop.map d ≫ (SSet.toTop.map p ≫ sSetTopAdj.counit.app Y) =
      SSet.toTop.map p ≫ sSetTopAdj.counit.app Y :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ sSetTopAdj.counit.app Y) (SSet.toTop.map_comp d p).symm).trans
        (congrArg (fun k => SSet.toTop.map k ≫ sSetTopAdj.counit.app Y) hd))
  have hdf : dd ≫ f = f :=
    (TopCat.toSSet.map_comp _ _).symm.trans (congrArg TopCat.toSSet.map hTop)
  have hpL : (dd ≫ l) ≫ p = f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => dd ≫ k) (oldSingularToNative_projection X x P)).trans hdf)
  have hpR : (l ≫ d) ≫ p = f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => l ≫ k) hd).trans (oldSingularToNative_projection X x P))
  have hUnit : d ≫ u = u ≫ dd := sSetTopAdj.unit.naturality d
  have hL : u ≫ (dd ≫ l) = d :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ l) hUnit.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => d ≫ k) (oldSingularToNative_unit X x P)).trans
              (Category.comp_id d))))
  have hR : u ≫ (l ≫ d) = d :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ d) (oldSingularToNative_unit X x P)).trans (Category.id_comp d))
  have hPoint : (v ≫ u) ≫ (dd ≫ l) = (v ≫ u) ≫ (l ≫ d) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => v ≫ k) (hL.trans hR.symm)).trans (Category.assoc _ _ _).symm)
  exact OriginalRegularThreeComparison.nativeLift_hom_ext_of_connected_pointMap
    (dd ≫ l) (l ≫ d) (hpL.trans hpR.symm) (v ≫ u) hPoint

/-- The original old two-cell space, with no replacement of its carrier. -/
abbrev originalTwo (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : TopCat.{u} :=
  LoopCellAttachment.space X x P

/-- The exact original three-cell attachment using the same public sphere family. -/
abbrev originalThree (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : TopCat.{u} :=
  LoopCellNativeRelativeBasis.originalThreeSpace X x P

/-- The unchanged original inclusion of the old two-cell space into that attachment. -/
abbrev originalThreeInclusion (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    originalTwo X x P ⟶ originalThree X x P :=
  CellFamilyAttachment.inclusion (originalTwo X x P) 2
    (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- Cofibrancy of the actual old two-cell space follows from the original
CW structure and its actual first cell-family pushout. -/
theorem originalTwo_isCofibrant (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) : IsCofibrant (originalTwo X x P) := by
  let : IsCofibrant X := CellFamilySimplicialModel.isCofibrant_of_classicalCW X
  change IsCofibrant (CellFamilyAttachment.space X 1 (LoopCellAttachment.attachingMap X x P))
  exact CellFamilySimplicialModel.isCofibrant_attachment X 1 P
    (LoopCellAttachment.attachingMap X x P)

/-- The actual simplicial model of the original three-cell family. -/
abbrev originalThreeModel (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : SSet.{u} :=
  CellFamilySimplicialModel.model (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- Its actual original counit comparison is weak, with cofibrancy derived
from the preceding original pushout. -/
theorem originalThreeModel_toSingular_weak (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    SSet.realizationWeakEquivalences
      (CellFamilySimplicialModel.toSingular (originalTwo X x P) 2 P
        (LoopCellSphericalGenerators.sphericalGenerator X x P)) := by
  let := originalTwo_isCofibrant X x P
  exact CellFamilySimplicialModel.toSingular_weak (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- The same upstairs attachment has a model built from the exact same
calibrated sphere copies and unchanged native old space. -/
abbrev upstairsThreeModel (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : SSet.{u} :=
  CellFamilySimplicialModel.model (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)

/-- This model's map to the singular set of the actual upstairs attachment
is weak; its old space is the literal realization of the same native cover. -/
theorem upstairsThreeModel_toSingular_weak (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    SSet.realizationWeakEquivalences
      (CellFamilySimplicialModel.toSingular (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)) := by
  let : IsCofibrant (LoopCellSphericalGenerators.liftedPair X x P).fst :=
    SSet.RealizationCWUpgrade.realization_isCofibrant
        (LoopCellSphericalGenerators.nativeCover X x P)
  exact CellFamilySimplicialModel.toSingular_weak
      (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)

/-- The actual original three-cell inclusion preserves the whole fundamental
groupoid, by the two-truncation theorem and same computed model comparison. -/
theorem originalThreeInclusionFundamentalGroupoid_isEquivalence
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [PathConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map
        (originalThreeInclusion X x P))).IsEquivalence := by
  let := originalTwo_isCofibrant X x P
  exact CellFamilySimplicialModel.inclusionFundamentalGroupoid_isEquivalence
    (originalTwo X x P) 2 (by decide) P (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- The three-cell cover point is the actual image of the same original
native point under the actual original inclusion. -/
abbrev nativeThreePoint (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (TopCat.toSSet.obj (originalThree X x P)) _⦋0⦌ :=
  (TopCat.toSSet.map (originalThreeInclusion X x P)).app (Opposite.op ⦋0⦌)
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)

/-- Its actual native covering object lies over Sing of the SAME original
three-cell attachment, not a substitute base or independently given cover. -/
abbrev nativeThreeCover (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : SSet.{u} :=
  SSet.KanComplex.nativeCover (TopCat.toSSet.obj (originalThree X x P)) (nativeThreePoint X x P)

/-- The original native projection from that computed cover. -/
abbrev nativeThreeProjection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    nativeThreeCover X x P ⟶ TopCat.toSSet.obj (originalThree X x P) :=
  SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj (originalThree X x P))
      (nativeThreePoint X x P)

/-- The actual old pulled cover in the original three-cell relative pair. -/
abbrev nativeThreeOldPullback (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] : SSet.{u} :=
  pullback (TopCat.toSSet.map (originalThreeInclusion X x P)) (nativeThreeProjection X x P)

/-- The exact original native base-change map to that old pullback. -/
def nativeTwoToThreePullback (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    LoopCellSphericalGenerators.nativeCover X x P ⟶ nativeThreeOldPullback X x P :=
  SSet.KanComplex.nativeCoverCartesianComparison (TopCat.toSSet.map (originalThreeInclusion X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)

/-- This SAME original comparison is an isomorphism, derived from the actual
higher-cell fundamental-groupoid equivalence and all simplex/path coordinates. -/
theorem nativeTwoToThreePullback_isIso (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    IsIso (nativeTwoToThreePullback X x P) := by
  let := originalThreeInclusionFundamentalGroupoid_isEquivalence X x P
  exact SSet.KanComplex.nativeCoverCartesianComparison_isIso
    (TopCat.toSSet.map (originalThreeInclusion X x P))
        (LoopCellSphericalGenerators.nativeTargetPoint X x P)

/-- The actual original base-change map itself is the computed Iso; no replacement of its map is
chosen. -/
def nativeTwoToThreePullbackIso (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [PathConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal]
        [Group.IsPerfect P] :
    LoopCellSphericalGenerators.nativeCover X x P ≅ nativeThreeOldPullback X x P := by
  letI : IsIso (nativeTwoToThreePullback X x P) := nativeTwoToThreePullback_isIso X x P
  exact asIso (nativeTwoToThreePullback X x P)

/-- The entire hom of the computed Iso is the actual original base-change map. -/
theorem nativeTwoToThreePullbackIso_hom (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    [PathConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal]
        [Group.IsPerfect P] :
    (nativeTwoToThreePullbackIso X x P).hom = nativeTwoToThreePullback X x P := by
  rfl

/-- The ACTUAL original old-cover comparison retains its unchanged
source projection. This exposes the proved map equation, not its definition. -/
theorem nativeTwoToThreePullback_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    nativeTwoToThreePullback X x P ≫
      pullback.fst (TopCat.toSSet.map (originalThreeInclusion X x P))
        (nativeThreeProjection X x P) =
      SSet.KanComplex.nativeCoverProjection
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
        (LoopCellSphericalGenerators.nativeTargetPoint X x P) := by
  unfold nativeTwoToThreePullback
  exact SSet.KanComplex.nativeCoverCartesianComparison_fst
    (TopCat.toSSet.map (originalThreeInclusion X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)

/-- The actual weak old-space leg for the three-cell comparison uses the
computed original unit retraction and exact native pullback map. -/
def oldSingularToThreePullback (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    TopCat.toSSet.obj (SSet.toTop.obj (LoopCellSphericalGenerators.nativeCover X x P)) ⟶
      nativeThreeOldPullback X x P :=
  oldSingularToNative X x P ≫ nativeTwoToThreePullback X x P

/-- Weakness of that actual old-space comparison is derived, not provided. -/
theorem oldSingularToThreePullback_weak (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    SSet.realizationWeakEquivalences (oldSingularToThreePullback X x P) := by
  let : WeakEquivalence (oldSingularToNative X x P) :=
    (weakEquivalence_iff _).mpr (oldSingularToNative_weak X x P)
  let := nativeTwoToThreePullback_isIso X x P
  exact (weakEquivalence_iff _).mp
    (inferInstance : WeakEquivalence (oldSingularToNative X x P ≫ nativeTwoToThreePullback X x P))

/-- The cover component of the same original old-space comparison. -/
abbrev oldSingularToThreeCover (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    TopCat.toSSet.obj (SSet.toTop.obj (LoopCellSphericalGenerators.nativeCover X x P)) ⟶
      nativeThreeCover X x P :=
  oldSingularToThreePullback X x P ≫
    pullback.snd (TopCat.toSSet.map (originalThreeInclusion X x P)) (nativeThreeProjection X x P)

/-- The original quotient labels map to the SAME actual native three-cover
endomorphisms, via the genuine original inclusion functor. -/
def quotientThreeDeckIndex (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [PathConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal]
        [Group.IsPerfect P] :
    FundamentalGroup X x ⧸ P ≃* End (SSet.FundamentalGroupoid.mk (nativeThreePoint X x P)) := by
  let F := SSet.mapFundamentalGroupoid (TopCat.toSSet.map (originalThreeInclusion X x P))
  letI : F.IsEquivalence := originalThreeInclusionFundamentalGroupoid_isEquivalence X x P
  exact (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm.trans
    ((Functor.FullyFaithful.ofFullyFaithful F).mulEquivEnd
      (SSet.FundamentalGroupoid.mk (LoopCellSphericalGenerators.nativeTargetPoint X x P)))

/-- Its whole map is literally induced by the original fundamental-groupoid
map, preserving all quotient labels and their noncommutative product. -/
theorem quotientThreeDeckIndex_apply (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) :
    quotientThreeDeckIndex X x P q =
      (SSet.mapFundamentalGroupoid (TopCat.toSSet.map (originalThreeInclusion X x P))).mapEnd
        (SSet.FundamentalGroupoid.mk (LoopCellSphericalGenerators.nativeTargetPoint X x P))
        ((LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q) := by
  rfl

/-- The same actual old-cover projection to the original old two-cell space. -/
abbrev oldCoverDown (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    (LoopCellSphericalGenerators.liftedPair X x P).fst ⟶ originalTwo X x P :=
  SSet.toTop.map (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj (originalTwo X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)) ≫
        sSetTopAdj.counit.app (originalTwo X x P)

/-- The actual old leg into the new native cover is the original native map
postcomposed with the computed old singular comparison. -/
theorem oldSingularToThreeCover_eq (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    oldSingularToThreeCover X x P = oldSingularToNative X x P ≫
      SSet.KanComplex.nativeCoverMap (TopCat.toSSet.map (originalThreeInclusion X x P))
        (LoopCellSphericalGenerators.nativeTargetPoint X x P) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun k => oldSingularToNative X x P ≫ k)
      (SSet.KanComplex.nativeCoverCartesianComparison_snd
        (TopCat.toSSet.map (originalThreeInclusion X x P))
            (LoopCellSphericalGenerators.nativeTargetPoint X x P)))

/-- Its strict projection is the original old-space map followed by the
original three-cell inclusion. -/
theorem oldSingularToThreeCover_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    oldSingularToThreeCover X x P ≫ nativeThreeProjection X x P =
      TopCat.toSSet.map (oldCoverDown X x P) ≫
          TopCat.toSSet.map (originalThreeInclusion X x P) := by
  let c := SSet.KanComplex.nativeCoverMap (TopCat.toSSet.map (originalThreeInclusion X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let p := SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj (originalTwo X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let l := oldSingularToNative X x P
  let f := TopCat.toSSet.map (originalThreeInclusion X x P)
  have h : c ≫ nativeThreeProjection X x P = p ≫ f := SSet.KanComplex.nativeCoverMap_projection _ _
  exact (congrArg (fun k => k ≫ nativeThreeProjection X x P)
      (oldSingularToThreeCover_eq X x P)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => l ≫ k) h).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ f) (oldSingularToNative_projection X x P)))))

/-- The new actual old-cover leg respects every original quotient deck
label through the exact inclusion-induced index. -/
theorem oldSingularToThreeCover_deck (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) :
    TopCat.toSSet.map (SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)) ≫
      oldSingularToThreeCover X x P =
        oldSingularToThreeCover X x P ≫
            SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P q) := by
  let a := (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q
  let d := LoopCellQuotientCellPresentation.nativeDeck X x P q
  let f := TopCat.toSSet.map (originalThreeInclusion X x P)
  let c := SSet.KanComplex.nativeCoverMap f (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let l := oldSingularToNative X x P
  let dd := TopCat.toSSet.map (SSet.toTop.map d)
  let dy := SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P q)
  have hd : d ≫ c = c ≫ dy :=
    (SSet.KanComplex.nativeCoverMap_deck f
        (LoopCellSphericalGenerators.nativeTargetPoint X x P) a).trans
      (congrArg (fun k => c ≫ SSet.KanComplex.nativeCoverDeckMap k)
          (quotientThreeDeckIndex_apply X x P q).symm)
  rw [oldSingularToThreeCover_eq]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ c) (oldSingularToNative_deck X x P a)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => l ≫ k) hd).trans (Category.assoc _ _ _).symm)))

/-- The actual original three-cell characteristic disk adjoint. -/
abbrev originalThreeDiskMate (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (Δ[3] : SSet.{u}) ⟶ TopCat.toSSet.obj (originalThree X x P) :=
  sSetTopAdj.homEquiv _ _ ((SSet.boundary.toClassicalCellDiskArrowIso 3).hom.right ≫
    CellFamilyAttachment.cell (originalTwo X x P) 2
        (LoopCellSphericalGenerators.sphericalGenerator X x P) p)

/-- The same unit upstairs sphere gives its actual boundary adjoint. -/
abbrev upstairsUnitBoundaryMate (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (SSet.boundary.{u} 3).toSSet ⟶ TopCat.toSSet.obj
        (LoopCellSphericalGenerators.liftedPair X x P).fst :=
  sSetTopAdj.homEquiv _ _ ((SSet.boundary.toClassicalCellDiskArrowIso 3).hom.left ≫
    chosenSphericalCopy X x P (1,p))

/-- The same original boundary adjoint is strictly compatible with the
original characteristic3-disk after projection to the original three-cell space. -/
theorem upstairsUnitBoundaryMate_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    upstairsUnitBoundaryMate X x P p ≫ oldSingularToThreeCover X x P ≫ nativeThreeProjection X x P =
      (SSet.boundary.{u} 3).ι ≫ originalThreeDiskMate X x P p := by
  let A := (SSet.boundary.toClassicalCellDiskArrowIso.{u} 3).hom.left
  let S := chosenSphericalCopy X x P (1,p)
  let B := oldCoverDown X x P
  let T := LoopCellSphericalGenerators.sphericalGenerator X x P p
  let E := sSetTopAdj.homEquiv (SSet.boundary.{u} 3).toSSet (originalTwo X x P)
  let f := TopCat.toSSet.map (originalThreeInclusion X x P)
  have hTop : (A ≫ S) ≫ B = A ≫ T :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => A ≫ k) (chosenSphericalCopy_down X x P (1,p)))
  have hB : upstairsUnitBoundaryMate X x P p ≫ TopCat.toSSet.map B = E (A ≫ T) :=
    (sSetTopAdj.homEquiv_naturality_right (A ≫ S) B).symm.trans (congrArg E hTop)
  have hSquare : E (A ≫ T) ≫ f = (SSet.boundary.{u} 3).ι ≫ originalThreeDiskMate X x P p :=
    CellFamilySimplicialModel.adjunctSquare_cell (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P) p
  exact (congrArg (fun k => upstairsUnitBoundaryMate X x P p ≫ k)
      (oldSingularToThreeCover_projection X x P)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ f) hB).trans hSquare))

/-- The exact unit upstairs sphere boundary, mapped into the new actual
native cover by the already computed old-space leg. -/
abbrev unitBoundaryLiftThree (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (SSet.boundary.{u} 3).toSSet ⟶ nativeThreeCover X x P :=
  upstairsUnitBoundaryMate X x P p ≫ oldSingularToThreeCover X x P

/-- Its original projection is the whole original characteristic disk boundary. -/
theorem unitBoundaryLiftThree_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    unitBoundaryLiftThree X x P p ≫ nativeThreeProjection X x P =
      (SSet.boundary.{u} 3).ι ≫ originalThreeDiskMate X x P p :=
  (Category.assoc _ _ _).trans (upstairsUnitBoundaryMate_projection X x P p)

private theorem boundaryFirst_ι :
    (SSet.const OriginalRegularThreeComparison.boundaryThreeFirstVertex :
      (Δ[0] : SSet.{u}) ⟶ (SSet.boundary.{u} 3).toSSet) ≫ (SSet.boundary.{u} 3).ι =
        (SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 4)) :
          (Δ[0] : SSet.{u}) ⟶ Δ[3]) :=
  (SSet.const_comp _ _).trans (SSet.yonedaEquiv_symm_zero _).symm

/-- The actual first vertex is chosen from the same unit boundary lift;
it is not normalized independently to an identity sheet. -/
abbrev nativeThreeDiskFirstVertex (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (nativeThreeCover X x P) _⦋0⦌ :=
  (unitBoundaryLiftThree X x P p).app (Opposite.op ⦋0⦌)
    ⟨SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 4), by
      rw [SSet.boundary_obj_eq_univ 0 3 (by decide)]
      exact Set.mem_univ _⟩

private theorem nativeThreeDiskFirst_compatible (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 4)) :
        (Δ[0] : SSet.{u}) ⟶ Δ[3]) ≫ originalThreeDiskMate X x P p =
      SSet.const ((nativeThreeProjection X x P).app (Opposite.op ⦋0⦌)
        (nativeThreeDiskFirstVertex X x P p)) := by
  let a : (Δ[0] : SSet.{u}) ⟶ (SSet.boundary.{u} 3).toSSet :=
    SSet.const OriginalRegularThreeComparison.boundaryThreeFirstVertex
  let b := (SSet.boundary.{u} 3).ι
  let d := originalThreeDiskMate X x P p
  let t := unitBoundaryLiftThree X x P p
  let q := nativeThreeProjection X x P
  have hA : a ≫ b = SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 4)) :=
      boundaryFirst_ι
  have hB : t ≫ q = b ≫ d := unitBoundaryLiftThree_projection X x P p
  have hC : a ≫ t = SSet.const (nativeThreeDiskFirstVertex X x P p) := by
    change (SSet.const OriginalRegularThreeComparison.boundaryThreeFirstVertex :
      (Δ[0] : SSet.{u}) ⟶ (SSet.boundary.{u} 3).toSSet) ≫ t =
        SSet.const (t.app (Opposite.op ⦋0⦌) OriginalRegularThreeComparison.boundaryThreeFirstVertex)
    exact SSet.const_comp _ t
  exact (congrArg (fun k => k ≫ d) hA.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => a ≫ k) hB.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ q) hC).trans (SSet.const_comp _ _)))))

/-- The SAME original characteristic3-disk is lifted using the actual first
vertex of its unit upstairs boundary. No spherical or extension witness is supplied. -/
def nativeThreeDiskLift (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (Δ[3] : SSet.{u}) ⟶ nativeThreeCover X x P :=
  SSet.KanComplex.nativeCoverSimplexLiftFromFirstMap (originalThreeDiskMate X x P p)
    (nativeThreeDiskFirstVertex X x P p) (nativeThreeDiskFirst_compatible X x P p)

/-- The whole lifted disk projects to the original characteristic adjoint. -/
theorem nativeThreeDiskLift_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    nativeThreeDiskLift X x P p ≫ nativeThreeProjection X x P = originalThreeDiskMate X x P p :=
  SSet.KanComplex.nativeCoverSimplexLiftFromFirstMap_projection _ _ _

/-- Its complete boundary is the SAME unit upstairs sphere boundary lift,
not merely a homology class with the correct ordinary augmentation. -/
theorem nativeThreeDiskLift_boundary (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (SSet.boundary.{u} 3).ι ≫ nativeThreeDiskLift X x P p = unitBoundaryLiftThree X x P p := by
  let t := unitBoundaryLiftThree X x P p
  let d := nativeThreeDiskLift X x P p
  let q := nativeThreeProjection X x P
  let a : (Δ[0] : SSet.{u}) ⟶ (SSet.boundary.{u} 3).toSSet :=
    SSet.const OriginalRegularThreeComparison.boundaryThreeFirstVertex
  let alpha : (Δ[0] : SSet.{u}) ⟶ Δ[3] :=
    SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 4))
  let : (SSet.boundary.{u} 3).toSSet.IsConnected :=
      OriginalRegularThreeComparison.boundaryThree_isConnected
  have hp : ((SSet.boundary.{u} 3).ι ≫ d) ≫ q = t ≫ q :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (SSet.boundary.{u} 3).ι ≫ k)
          (nativeThreeDiskLift_projection X x P p)).trans
        (unitBoundaryLiftThree_projection X x P p).symm)
  have hFirst : alpha ≫ d = SSet.const (nativeThreeDiskFirstVertex X x P p) :=
    SSet.KanComplex.nativeCoverSimplexLiftFromFirstMap_firstVertex _ _ _
  have hAt : a ≫ t = SSet.const (nativeThreeDiskFirstVertex X x P p) := by
    change (SSet.const OriginalRegularThreeComparison.boundaryThreeFirstVertex :
      (Δ[0] : SSet.{u}) ⟶ (SSet.boundary.{u} 3).toSSet) ≫ t =
        SSet.const (t.app (Opposite.op ⦋0⦌) OriginalRegularThreeComparison.boundaryThreeFirstVertex)
    exact SSet.const_comp _ t
  have hPoint : a ≫ ((SSet.boundary.{u} 3).ι ≫ d) = a ≫ t :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ d) boundaryFirst_ι).trans (hFirst.trans hAt.symm))
  exact OriginalRegularThreeComparison.nativeLift_hom_ext_of_connected_pointMap
    ((SSet.boundary.{u} 3).ι ≫ d) t hp a hPoint

/-- Every labelled upstairs boundary mate uses the SAME selected spherical
copy, including its arbitrary original first-path shift. -/
abbrev upstairsBoundaryMate (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (SSet.boundary.{u} 3).toSSet ⟶ TopCat.toSSet.obj
        (LoopCellSphericalGenerators.liftedPair X x P).fst :=
  sSetTopAdj.homEquiv _ _ ((SSet.boundary.toClassicalCellDiskArrowIso 3).hom.left ≫
      chosenSphericalCopy X x P i)

/-- Boundary mate translation is derived from the actual spherical-copy
translation equation and the original adjunction naturality. -/
theorem upstairsBoundaryMate_translate (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) (p : P) :
    upstairsBoundaryMate X x P (q,p) = upstairsUnitBoundaryMate X x P p ≫
      TopCat.toSSet.map (SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)) := by
  let A := (SSet.boundary.toClassicalCellDiskArrowIso.{u} 3).hom.left
  let D := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)
  let E := sSetTopAdj.homEquiv (SSet.boundary.{u} 3).toSSet
      (LoopCellSphericalGenerators.liftedPair X x P).fst
  have h : chosenSphericalCopy X x P (q,p) = chosenSphericalCopy X x P (1,p) ≫ D := by
    simpa only [mul_one] using chosenSphericalCopy_deck X x P q 1 p
  exact (congrArg (fun k => E (A ≫ k)) h).trans
    ((congrArg E (Category.assoc _ _ _).symm).trans
      (sSetTopAdj.homEquiv_naturality_right (A ≫ chosenSphericalCopy X x P (1,p)) D))

/-- The original3-disk lift in EVERY original quotient/P copy is obtained
by the SAME actual target deck map, with its inclusion-induced index. -/
def nativeThreeDiskCopy (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [PathConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal]
        [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) : (Δ[3] : SSet.{u}) ⟶
        nativeThreeCover X x P :=
  nativeThreeDiskLift X x P i.2 ≫ SSet.KanComplex.nativeCoverDeckMap
      (quotientThreeDeckIndex X x P i.1)

/-- Every whole translated3-disk keeps its original downstairs characteristic
mate; projection does not erase the upstairs quotient label in its basis. -/
theorem nativeThreeDiskCopy_projection (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    nativeThreeDiskCopy X x P i ≫ nativeThreeProjection X x P = originalThreeDiskMate X x P i.2 :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => nativeThreeDiskLift X x P i.2 ≫ k)
      (SSet.KanComplex.nativeCoverDeckMap_projection (quotientThreeDeckIndex X x P i.1))).trans
        (nativeThreeDiskLift_projection X x P i.2))

/-- The entire boundary of EVERY quotient-labelled original3-disk agrees
with the SAME actual upstairs spherical boundary and computed old-space leg. -/
theorem nativeThreeDiskCopy_boundary (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (SSet.boundary.{u} 3).ι ≫ nativeThreeDiskCopy X x P i =
      upstairsBoundaryMate X x P i ≫ oldSingularToThreeCover X x P := by
  rcases i with ⟨q,p⟩
  let A := (SSet.boundary.{u} 3).ι
  let L := nativeThreeDiskLift X x P p
  let B := upstairsUnitBoundaryMate X x P p
  let G := oldSingularToThreeCover X x P
  let D := SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P q)
  let S := TopCat.toSSet.map (SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q))
  exact (Category.assoc A L D).symm.trans
    ((congrArg (fun k => k ≫ D) (nativeThreeDiskLift_boundary X x P p)).trans
      ((Category.assoc B G D).trans
        ((congrArg (fun k => B ≫ k) (oldSingularToThreeCover_deck X x P q).symm).trans
          ((Category.assoc B S G).symm.trans
            (congrArg (fun k => k ≫ G) (upstairsBoundaryMate_translate X x P q p).symm)))))


section PulledThreeCellFamily

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
  [PathConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
  [P.Normal] [Group.IsPerfect P]

local instance originalThreeInclusionMono : Mono (originalThreeInclusion X x P) :=
  (TopCat.mono_iff_injective _).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))

/-- The same original characteristic three-disks, before pullback. -/
abbrev originalThreeDiskFamily : SSet.{u} := CellFamilySimplicialModel.disks 2 P

/-- The same original three-boundaries, before pullback. -/
abbrev originalThreeBoundaryFamily : SSet.{u} := CellFamilySimplicialModel.boundaries 2 P

/-- The whole original three-disk family adjoint. -/
abbrev originalThreeDiskFamilyMate : originalThreeDiskFamily X x P ⟶
    TopCat.toSSet.obj (originalThree X x P) :=
  CellFamilySimplicialModel.diskMates (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- The actual original boundary-family adjoint into the old singular space. -/
abbrev originalThreeBoundaryFamilyMate : originalThreeBoundaryFamily X x P ⟶
    TopCat.toSSet.obj (originalTwo X x P) :=
  CellFamilySimplicialModel.attaching (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)

/-- The literal three-cell model pulled through the computed native cover. -/
abbrev nativePulledThreeModel : SSet.{u} :=
  pullback (CellFamilySimplicialModel.toSingular (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)) (nativeThreeProjection X x P)

/-- Every actual original three-disk is pulled through that same cover. -/
abbrev nativePulledThreeDisks : SSet.{u} :=
  pullback (originalThreeDiskFamilyMate X x P) (nativeThreeProjection X x P)

/-- Every actual original boundary is pulled through that same cover. -/
abbrev nativePulledThreeBoundaries : SSet.{u} :=
  pullback (originalThreeBoundaryFamilyMate X x P ≫
    TopCat.toSSet.map (originalThreeInclusion X x P)) (nativeThreeProjection X x P)

/-- The unchanged original boundary-family inclusion induces the actual pulled leg. -/
def nativePulledThreeBoundaryToDisks : nativePulledThreeBoundaries X x P ⟶
    nativePulledThreeDisks X x P :=
  SSet.pullbackLegMap _ _ (nativeThreeProjection X x P)
    (CellFamilySimplicialModel.boundarySum 2 P)
    (CellFamilySimplicialModel.adjunctSquare (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)).symm

/-- The actual pulled attaching leg retains both original projections. -/
def nativePulledThreeAttaching : nativePulledThreeBoundaries X x P ⟶ nativeThreeOldPullback X x P :=
  SSet.pullbackLegMap _ _ (nativeThreeProjection X x P) (originalThreeBoundaryFamilyMate X x P) rfl

/-- The original new-disk inclusion gives the actual disk leg in the pulled model. -/
def nativePulledThreeDiskInclusion : nativePulledThreeDisks X x P ⟶ nativePulledThreeModel X x P :=
  SSet.pullbackLegMap _ _ (nativeThreeProjection X x P)
    (CellFamilySimplicialModel.newDisks (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
    (CellFamilySimplicialModel.toSingular_disks (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)).symm

/-- The original old-model inclusion gives the actual old leg in the pulled model. -/
def nativePulledThreeOldInclusion : nativeThreeOldPullback X x P ⟶ nativePulledThreeModel X x P :=
  SSet.pullbackLegMap _ _ (nativeThreeProjection X x P)
    (CellFamilySimplicialModel.oldInclusion (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
    (CellFamilySimplicialModel.toSingular_old (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)).symm

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- Simplicial Van Kampen stability proves the entire actual pulled original pushout. -/
theorem nativePulledThree_isPushout : IsPushout (nativePulledThreeBoundaryToDisks X x P)
    (nativePulledThreeAttaching X x P) (nativePulledThreeDiskInclusion X x P)
      (nativePulledThreeOldInclusion X x P) := by
  let b := CellFamilySimplicialModel.boundarySum 2 P
  let : Mono b := by
    change Mono (CellFamilySimplicialModel.boundarySum 2 P)
    rw [CellFamilySimplicialModel.boundarySum_eq]
    infer_instance
  exact SSet.pullbackLegPushout
    (CellFamilySimplicialModel.isPushout (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
    (CellFamilySimplicialModel.toSingular (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)) (nativeThreeProjection X x P)
    (originalThreeDiskFamilyMate X x P)
    (TopCat.toSSet.map (originalThreeInclusion X x P))
    (CellFamilySimplicialModel.toSingular_disks (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)).symm
    (CellFamilySimplicialModel.toSingular_old (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)).symm

/-- The actual pulled model's cover projection is weak by the original model
comparison and existing right properness against the derived cover fibration. -/
theorem nativePulledThree_toCover_weak : SSet.realizationWeakEquivalences
    (pullback.snd (CellFamilySimplicialModel.toSingular (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)) (nativeThreeProjection X x P)) := by
  let f := CellFamilySimplicialModel.toSingular (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)
  let p := nativeThreeProjection X x P
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr (originalThreeModel_toSingular_weak X x P)
  let : Fibration p := OriginalRegularThreeComparison.nativeProjection_fibration _ _
  exact (weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback (IsPullback.of_hasPullback f p))

/-- The whole selected unit three-disk family, with its actual first-path shifts. -/
abbrev nativeThreeDiskFamilyLift : originalThreeDiskFamily X x P ⟶ nativeThreeCover X x P :=
  SSet.KanComplex.nativeCoverCellFamilyLift (nativeThreeDiskLift X x P)

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- Its projection is the entire original characteristic family. -/
theorem nativeThreeDiskFamilyLift_projection :
    nativeThreeDiskFamilyLift X x P ≫ nativeThreeProjection X x P =
        originalThreeDiskFamilyMate X x P := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro p
  let a := CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[3] : SSet.{u})) p
  let L := nativeThreeDiskFamilyLift X x P
  let q := nativeThreeProjection X x P
  have hL : a ≫ L = nativeThreeDiskLift X x P p :=
    SSet.KanComplex.nativeCoverCellFamilyLift_ι
      (Y := TopCat.toSSet.obj (originalThree X x P)) (y := nativeThreePoint X x P)
      (V := (Δ[3] : SSet.{u})) (I := P) (nativeThreeDiskLift X x P) p
  have hD : a ≫ originalThreeDiskFamilyMate X x P = originalThreeDiskMate X x P p :=
    CellFamilySimplicialModel.diskMates_ι (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P) p
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ q) hL).trans
      ((nativeThreeDiskLift_projection X x P p).trans hD.symm))

/-- The whole selected unit boundary family is the exact restriction of those disks. -/
abbrev nativeThreeBoundaryFamilyLift : originalThreeBoundaryFamily X x P ⟶ nativeThreeCover X x P :=
  SSet.KanComplex.nativeCoverCellFamilyLift (unitBoundaryLiftThree X x P)

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The whole unit boundary family projects through the original old-space inclusion. -/
theorem nativeThreeBoundaryFamilyLift_projection :
    nativeThreeBoundaryFamilyLift X x P ≫ nativeThreeProjection X x P =
      originalThreeBoundaryFamilyMate X x P ≫ TopCat.toSSet.map (originalThreeInclusion X x P) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro p
  let a := CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 3).toSSet) p
  let L := nativeThreeBoundaryFamilyLift X x P
  let q := nativeThreeProjection X x P
  let b := CellFamilySimplicialModel.boundarySum 2 P
  let D := originalThreeDiskFamilyMate X x P
  have hL : a ≫ L = unitBoundaryLiftThree X x P p :=
    SSet.KanComplex.nativeCoverCellFamilyLift_ι
      (Y := TopCat.toSSet.obj (originalThree X x P)) (y := nativeThreePoint X x P)
      (V := (SSet.boundary.{u} 3).toSSet) (I := P) (unitBoundaryLiftThree X x P) p
  have hb : a ≫ b = (SSet.boundary.{u} 3).ι ≫
      CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[3] : SSet.{u})) p := by
    change CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 3).toSSet) p ≫
      CellFamilySimplicialModel.boundarySum 2 P =
        (SSet.boundary.{u} 3).ι ≫ CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[3] : SSet.{u})) p
    rw [CellFamilySimplicialModel.boundarySum_eq]
    exact CategoryTheory.Limits.Sigma.ι_map _ p
  have hD : CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[3] : SSet.{u})) p ≫ D =
      originalThreeDiskMate X x P p :=
    CellFamilySimplicialModel.diskMates_ι (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P) p
  have hSquare := CellFamilySimplicialModel.adjunctSquare (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ q) hL).trans
      ((unitBoundaryLiftThree_projection X x P p).trans
        ((congrArg (fun f => (SSet.boundary.{u} 3).ι ≫ f) hD.symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ D) hb.symm).trans
              ((Category.assoc _ _ _).trans (congrArg (fun f => a ≫ f) hSquare)))))))

/-- The complete actual disk-family Iso contains every quotient label and every original cell. -/
def nativeThreeDiskFamilyCopiesIso :
    CellFamilySimplicialModel.disks 2 (LoopCellQuotientCellPresentation.labels X x P) ≅
      nativePulledThreeDisks X x P :=
  SSet.KanComplex.nativeCoverCellFamilyCopiesIso (nativeThreeDiskLift X x P)
      (quotientThreeDeckIndex X x P) ≪≫
    pullback.congrHom (nativeThreeDiskFamilyLift_projection X x P) rfl

/-- The complete actual boundary-family Iso contains every quotient label and every original
boundary. -/
def nativeThreeBoundaryFamilyCopiesIso :
    CellFamilySimplicialModel.boundaries 2 (LoopCellQuotientCellPresentation.labels X x P) ≅
      nativePulledThreeBoundaries X x P :=
  SSet.KanComplex.nativeCoverCellFamilyCopiesIso (unitBoundaryLiftThree X x P)
      (quotientThreeDeckIndex X x P) ≪≫
    pullback.congrHom (nativeThreeBoundaryFamilyLift_projection X x P) rfl

/-- Each actual disk copy keeps the original p-cell in its first projection. -/
theorem nativeThreeDiskFamilyCopiesIso_ι_fst (i : LoopCellQuotientCellPresentation.labels X x P) :
    (CategoryTheory.Limits.Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (Δ[3] : SSet.{u})) i ≫
      (nativeThreeDiskFamilyCopiesIso X x P).hom) ≫
        pullback.fst (originalThreeDiskFamilyMate X x P) (nativeThreeProjection X x P) =
      CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[3] : SSet.{u})) i.2 := by
  let h := nativeThreeDiskFamilyLift_projection X x P
  let E := SSet.KanComplex.nativeCoverCellFamilyCopiesIso (nativeThreeDiskLift X x P)
      (quotientThreeDeckIndex X x P)
  let a := CategoryTheory.Limits.Sigma.ι
      (fun _ : LoopCellQuotientCellPresentation.labels X x P => (Δ[3] : SSet.{u})) i
  have hF := OriginalRegularThreeComparison.pullbackCongr_fst (nativeThreeProjection X x P) h
  change (a ≫ (E.hom ≫ (pullback.congrHom h rfl).hom)) ≫ _ = _
  simp only [Category.assoc]
  rw [hF]
  rw [← Category.assoc, SSet.KanComplex.nativeCoverCellFamilyCopiesIso_ι]
  exact SSet.KanComplex.nativeCoverCellCopy_fst _ _ i

/-- Each actual disk copy retains the whole chosen original lift and actual target deck
translate. -/
theorem nativeThreeDiskFamilyCopiesIso_ι_snd (i : LoopCellQuotientCellPresentation.labels X x P) :
    (CategoryTheory.Limits.Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (Δ[3] : SSet.{u})) i ≫
      (nativeThreeDiskFamilyCopiesIso X x P).hom) ≫
        pullback.snd (originalThreeDiskFamilyMate X x P) (nativeThreeProjection X x P) =
            nativeThreeDiskCopy X x P i := by
  let h := nativeThreeDiskFamilyLift_projection X x P
  let E := SSet.KanComplex.nativeCoverCellFamilyCopiesIso (nativeThreeDiskLift X x P)
      (quotientThreeDeckIndex X x P)
  let a := CategoryTheory.Limits.Sigma.ι
      (fun _ : LoopCellQuotientCellPresentation.labels X x P => (Δ[3] : SSet.{u})) i
  have hF := OriginalRegularThreeComparison.pullbackCongr_snd (nativeThreeProjection X x P) h
  change (a ≫ (E.hom ≫ (pullback.congrHom h rfl).hom)) ≫ _ = _
  simp only [Category.assoc]
  rw [hF]
  rw [← Category.assoc, SSet.KanComplex.nativeCoverCellFamilyCopiesIso_ι]
  exact SSet.KanComplex.nativeCoverCellCopy_snd _ _ i

/-- Each actual boundary copy keeps the original p-boundary in its first projection. -/
theorem nativeThreeBoundaryFamilyCopiesIso_ι_fst
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (CategoryTheory.Limits.Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (SSet.boundary.{u} 3).toSSet) i ≫
      (nativeThreeBoundaryFamilyCopiesIso X x P).hom) ≫
        pullback.fst (originalThreeBoundaryFamilyMate X x P ≫
            TopCat.toSSet.map (originalThreeInclusion X x P))
          (nativeThreeProjection X x P) =
              CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 3).toSSet) i.2 := by
  let h := nativeThreeBoundaryFamilyLift_projection X x P
  let E := SSet.KanComplex.nativeCoverCellFamilyCopiesIso (unitBoundaryLiftThree X x P)
      (quotientThreeDeckIndex X x P)
  let a := CategoryTheory.Limits.Sigma.ι
      (fun _ : LoopCellQuotientCellPresentation.labels X x P => (SSet.boundary.{u} 3).toSSet) i
  have hF := OriginalRegularThreeComparison.pullbackCongr_fst (nativeThreeProjection X x P) h
  change (a ≫ (E.hom ≫ (pullback.congrHom h rfl).hom)) ≫ _ = _
  simp only [Category.assoc]
  rw [hF]
  rw [← Category.assoc, SSet.KanComplex.nativeCoverCellFamilyCopiesIso_ι]
  exact SSet.KanComplex.nativeCoverCellCopy_fst _ _ i

/-- The second projection retains the entire same chosen spherical boundary. -/
theorem nativeThreeBoundaryFamilyCopiesIso_ι_snd
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (CategoryTheory.Limits.Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (SSet.boundary.{u} 3).toSSet) i ≫
      (nativeThreeBoundaryFamilyCopiesIso X x P).hom) ≫
        pullback.snd (originalThreeBoundaryFamilyMate X x P ≫
            TopCat.toSSet.map (originalThreeInclusion X x P))
          (nativeThreeProjection X x P) = upstairsBoundaryMate X x P i ≫
              oldSingularToThreeCover X x P := by
  let h := nativeThreeBoundaryFamilyLift_projection X x P
  let E := SSet.KanComplex.nativeCoverCellFamilyCopiesIso (unitBoundaryLiftThree X x P)
      (quotientThreeDeckIndex X x P)
  let a := CategoryTheory.Limits.Sigma.ι
      (fun _ : LoopCellQuotientCellPresentation.labels X x P => (SSet.boundary.{u} 3).toSSet) i
  let q := nativeThreeProjection X x P
  have hF := OriginalRegularThreeComparison.pullbackCongr_snd q h
  have hCopy : (a ≫ (nativeThreeBoundaryFamilyCopiesIso X x P).hom) ≫
      pullback.snd (originalThreeBoundaryFamilyMate X x P ≫
          TopCat.toSSet.map (originalThreeInclusion X x P)) q =
        unitBoundaryLiftThree X x P i.2 ≫
            SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P i.1) := by
    change (a ≫ (E.hom ≫ (pullback.congrHom h rfl).hom)) ≫ _ = _
    simp only [Category.assoc]
    rw [hF]
    rw [← Category.assoc, SSet.KanComplex.nativeCoverCellFamilyCopiesIso_ι]
    exact SSet.KanComplex.nativeCoverCellCopy_snd _ _ i
  have hRestrict : unitBoundaryLiftThree X x P i.2 ≫
      SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P i.1) =
        (SSet.boundary.{u} 3).ι ≫ nativeThreeDiskCopy X x P i :=
    (congrArg (fun f => f ≫ SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P i.1))
      (nativeThreeDiskLift_boundary X x P i.2).symm).trans (Category.assoc _ _ _)
  exact hCopy.trans (hRestrict.trans (nativeThreeDiskCopy_boundary X x P i))

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The computed old pullback leg retains the exact original realized-cover map. -/
theorem oldSingularToThreePullback_fst : oldSingularToThreePullback X x P ≫
    pullback.fst (TopCat.toSSet.map (originalThreeInclusion X x P)) (nativeThreeProjection X x P) =
      TopCat.toSSet.map (oldCoverDown X x P) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun f => oldSingularToNative X x P ≫ f)
      (SSet.KanComplex.nativeCoverCartesianComparison_fst
        (TopCat.toSSet.map (originalThreeInclusion X x P))
            (LoopCellSphericalGenerators.nativeTargetPoint X x P))).trans
          (oldSingularToNative_projection X x P))

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- Every same chosen upstairs boundary has the exact original old-space adjoint after
projection. -/
theorem upstairsBoundaryMate_to_original (i : LoopCellQuotientCellPresentation.labels X x P) :
    upstairsBoundaryMate X x P i ≫ TopCat.toSSet.map (oldCoverDown X x P) =
      sSetTopAdj.homEquiv (SSet.boundary.{u} 3).toSSet (originalTwo X x P)
        ((SSet.boundary.toClassicalCellDiskArrowIso 3).hom.left ≫
          LoopCellSphericalGenerators.sphericalGenerator X x P i.2) := by
  let A := (SSet.boundary.toClassicalCellDiskArrowIso.{u} 3).hom.left
  let S := chosenSphericalCopy X x P i
  let B := oldCoverDown X x P
  let T := LoopCellSphericalGenerators.sphericalGenerator X x P i.2
  let E := sSetTopAdj.homEquiv (SSet.boundary.{u} 3).toSSet (originalTwo X x P)
  have hTop : (A ≫ S) ≫ B = A ≫ T :=
    (Category.assoc _ _ _).trans (congrArg (fun k => A ≫ k) (chosenSphericalCopy_down X x P i))
  exact (sSetTopAdj.homEquiv_naturality_right (A ≫ S) B).symm.trans (congrArg E hTop)


/-- The complete copied boundary-family square retains the actual pulled original boundary
inclusion. -/
theorem nativeThreeCopies_boundarySquare :
    CellFamilySimplicialModel.boundarySum 2 (LoopCellQuotientCellPresentation.labels X x P) ≫
      (nativeThreeDiskFamilyCopiesIso X x P).hom =
        (nativeThreeBoundaryFamilyCopiesIso X x P).hom ≫
            nativePulledThreeBoundaryToDisks X x P := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro i
  let jB := CategoryTheory.Limits.Sigma.ι
    (fun _ : LoopCellQuotientCellPresentation.labels X x P => (SSet.boundary.{u} 3).toSSet) i
  let jD := CategoryTheory.Limits.Sigma.ι
    (fun _ : LoopCellQuotientCellPresentation.labels X x P => (Δ[3] : SSet.{u})) i
  let kB := CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 3).toSSet) i.2
  let kD := CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[3] : SSet.{u})) i.2
  let t := (SSet.boundary.{u} 3).ι
  let b := CellFamilySimplicialModel.boundarySum 2 (LoopCellQuotientCellPresentation.labels X x P)
  let a := (nativeThreeBoundaryFamilyCopiesIso X x P).hom
  let d := (nativeThreeDiskFamilyCopiesIso X x P).hom
  let b0 := CellFamilySimplicialModel.boundarySum 2 P
  let i0 := nativePulledThreeBoundaryToDisks X x P
  let fB := pullback.fst (originalThreeBoundaryFamilyMate X x P ≫
    TopCat.toSSet.map (originalThreeInclusion X x P)) (nativeThreeProjection X x P)
  let fD := pullback.fst (originalThreeDiskFamilyMate X x P) (nativeThreeProjection X x P)
  let pB := pullback.snd (originalThreeBoundaryFamilyMate X x P ≫
    TopCat.toSSet.map (originalThreeInclusion X x P)) (nativeThreeProjection X x P)
  let pD := pullback.snd (originalThreeDiskFamilyMate X x P) (nativeThreeProjection X x P)
  have hb : jB ≫ b = t ≫ jD := by
    change CategoryTheory.Limits.Sigma.ι
      (fun _ : LoopCellQuotientCellPresentation.labels X x P => (SSet.boundary.{u} 3).toSSet) i ≫
      CellFamilySimplicialModel.boundarySum 2 (LoopCellQuotientCellPresentation.labels X x P) =
        (SSet.boundary.{u} 3).ι ≫ CategoryTheory.Limits.Sigma.ι
          (fun _ : LoopCellQuotientCellPresentation.labels X x P => (Δ[3] : SSet.{u})) i
    rw [CellFamilySimplicialModel.boundarySum_eq]
    exact CategoryTheory.Limits.Sigma.ι_map _ i
  have hb0 : kB ≫ b0 = t ≫ kD := by
    change CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 3).toSSet) i.2 ≫
      CellFamilySimplicialModel.boundarySum 2 P =
        (SSet.boundary.{u} 3).ι ≫ CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[3] : SSet.{u})) i.2
    rw [CellFamilySimplicialModel.boundarySum_eq]
    exact CategoryTheory.Limits.Sigma.ι_map _ i.2
  have hiF : i0 ≫ fD = fB ≫ b0 := SSet.pullbackLegMap_fst _ _ _ _ _
  have hiP : i0 ≫ pD = pB := SSet.pullbackLegMap_snd _ _ _ _ _
  have hA : jB ≫ (b ≫ d) = t ≫ (jD ≫ d) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ d) hb).trans (Category.assoc _ _ _))
  apply pullback.hom_ext
  · have hL : (jB ≫ (b ≫ d)) ≫ fD = t ≫ kD :=
      (congrArg (fun f => f ≫ fD) hA).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun f => t ≫ f) (nativeThreeDiskFamilyCopiesIso_ι_fst X x P i)))
    have hR : (jB ≫ (a ≫ i0)) ≫ fD = t ≫ kD := by
      have h1 : (jB ≫ (a ≫ i0)) ≫ fD = (jB ≫ a) ≫ (fB ≫ b0) := by
        simpa only [Category.assoc] using congrArg (fun f => (jB ≫ a) ≫ f) hiF
      have h2 : (jB ≫ a) ≫ (fB ≫ b0) = kB ≫ b0 :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ b0) (nativeThreeBoundaryFamilyCopiesIso_ι_fst X x P i))
      exact h1.trans (h2.trans hb0)
    exact hL.trans hR.symm
  · have hL : (jB ≫ (b ≫ d)) ≫ pD = upstairsBoundaryMate X x P i ≫ oldSingularToThreeCover X x P :=
      (congrArg (fun f => f ≫ pD) hA).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => t ≫ f) (nativeThreeDiskFamilyCopiesIso_ι_snd X x P i)).trans
            (nativeThreeDiskCopy_boundary X x P i)))
    have hR : (jB ≫ (a ≫ i0)) ≫ pD = upstairsBoundaryMate X x P i ≫ oldSingularToThreeCover X x P :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => jB ≫ f) ((Category.assoc _ _ _).trans
          (congrArg (fun f => a ≫ f) hiP))).trans
            (nativeThreeBoundaryFamilyCopiesIso_ι_snd X x P i))
    exact hL.trans hR.symm

/-- The complete copied attaching square uses the same upstairs sphere family
and the computed weak comparison of the actual old cover. -/
theorem nativeThreeCopies_attachingSquare :
    CellFamilySimplicialModel.attaching (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) ≫
      oldSingularToThreePullback X x P =
        (nativeThreeBoundaryFamilyCopiesIso X x P).hom ≫ nativePulledThreeAttaching X x P := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro i
  let j := CategoryTheory.Limits.Sigma.ι
    (fun _ : LoopCellQuotientCellPresentation.labels X x P => (SSet.boundary.{u} 3).toSSet) i
  let k := CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 3).toSSet) i.2
  let g := CellFamilySimplicialModel.attaching (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let c := oldSingularToThreePullback X x P
  let a := (nativeThreeBoundaryFamilyCopiesIso X x P).hom
  let g0 := nativePulledThreeAttaching X x P
  let fO := pullback.fst (TopCat.toSSet.map (originalThreeInclusion X x P))
      (nativeThreeProjection X x P)
  let pO := pullback.snd (TopCat.toSSet.map (originalThreeInclusion X x P))
      (nativeThreeProjection X x P)
  let fB := pullback.fst (originalThreeBoundaryFamilyMate X x P ≫
    TopCat.toSSet.map (originalThreeInclusion X x P)) (nativeThreeProjection X x P)
  let pB := pullback.snd (originalThreeBoundaryFamilyMate X x P ≫
    TopCat.toSSet.map (originalThreeInclusion X x P)) (nativeThreeProjection X x P)
  let b0 := originalThreeBoundaryFamilyMate X x P
  let m := upstairsBoundaryMate X x P i
  have hj : j ≫ g = m := CellFamilySimplicialModel.attaching_ι
    (LoopCellSphericalGenerators.liftedPair X x P).fst 2
      (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) i
  have hk : k ≫ b0 = sSetTopAdj.homEquiv (SSet.boundary.{u} 3).toSSet (originalTwo X x P)
      ((SSet.boundary.toClassicalCellDiskArrowIso 3).hom.left ≫
        LoopCellSphericalGenerators.sphericalGenerator X x P i.2) :=
    CellFamilySimplicialModel.attaching_ι (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P) i.2
  have hgF : g0 ≫ fO = fB ≫ b0 := SSet.pullbackLegMap_fst _ _ _ _ _
  have hgP : g0 ≫ pO = pB := SSet.pullbackLegMap_snd _ _ _ _ _
  apply pullback.hom_ext
  · have hL : (j ≫ (g ≫ c)) ≫ fO = k ≫ b0 :=
      (congrArg (fun f => f ≫ fO) ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ c) hj))).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => m ≫ f) (oldSingularToThreePullback_fst X x P)).trans
              ((upstairsBoundaryMate_to_original X x P i).trans hk.symm)))
    have hR : (j ≫ (a ≫ g0)) ≫ fO = k ≫ b0 := by
      have h1 : (j ≫ (a ≫ g0)) ≫ fO = (j ≫ a) ≫ (fB ≫ b0) := by
        simpa only [Category.assoc] using congrArg (fun f => (j ≫ a) ≫ f) hgF
      exact h1.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ b0) (nativeThreeBoundaryFamilyCopiesIso_ι_fst X x P i)))
    exact hL.trans hR.symm
  · have hL : (j ≫ (g ≫ c)) ≫ pO = m ≫ oldSingularToThreeCover X x P :=
      (congrArg (fun f => f ≫ pO) ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ c) hj))).trans (Category.assoc _ _ _)
    have hR : (j ≫ (a ≫ g0)) ≫ pO = m ≫ oldSingularToThreeCover X x P := by
      have h1 : (j ≫ (a ≫ g0)) ≫ pO = (j ≫ a) ≫ pB := by
        simpa only [Category.assoc] using congrArg (fun f => (j ≫ a) ≫ f) hgP
      exact h1.trans (nativeThreeBoundaryFamilyCopiesIso_ι_snd X x P i)
    exact hL.trans hR.symm

private theorem nativeThreeModelSpan_commutes :
    CellFamilySimplicialModel.boundarySum 2 (LoopCellQuotientCellPresentation.labels X x P) ≫
      ((nativeThreeDiskFamilyCopiesIso X x P).hom ≫ nativePulledThreeDiskInclusion X x P) =
        CellFamilySimplicialModel.attaching (LoopCellSphericalGenerators.liftedPair X x P).fst 2
          (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) ≫
            (oldSingularToThreePullback X x P ≫ nativePulledThreeOldInclusion X x P) := by
  let b := CellFamilySimplicialModel.boundarySum 2 (LoopCellQuotientCellPresentation.labels X x P)
  let g := CellFamilySimplicialModel.attaching (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let a := (nativeThreeBoundaryFamilyCopiesIso X x P).hom
  let d := (nativeThreeDiskFamilyCopiesIso X x P).hom
  let c := oldSingularToThreePullback X x P
  let b0 := nativePulledThreeBoundaryToDisks X x P
  let g0 := nativePulledThreeAttaching X x P
  let p0 := nativePulledThreeDiskInclusion X x P
  let q0 := nativePulledThreeOldInclusion X x P
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ p0) (nativeThreeCopies_boundarySquare X x P)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a ≫ f) (nativePulledThree_isPushout X x P).w).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ q0) (nativeThreeCopies_attachingSquare X x P).symm).trans
              (Category.assoc _ _ _))))))

/-- The actual upstairs model maps into the literal pulled original model by
its original old-space leg and every same selected three-disk copy. -/
def upstairsThreeModelToPulled : upstairsThreeModel X x P ⟶ nativePulledThreeModel X x P :=
  (CellFamilySimplicialModel.isPushout (LoopCellSphericalGenerators.liftedPair X x P).fst 2
      (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)).desc
    ((nativeThreeDiskFamilyCopiesIso X x P).hom ≫ nativePulledThreeDiskInclusion X x P)
    (oldSingularToThreePullback X x P ≫ nativePulledThreeOldInclusion X x P)
    (nativeThreeModelSpan_commutes X x P)

/-- Its complete original new-disk leg is the computed copy family. -/
theorem upstairsThreeModelToPulled_disks :
    CellFamilySimplicialModel.newDisks (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) ≫
      upstairsThreeModelToPulled X x P =
        (nativeThreeDiskFamilyCopiesIso X x P).hom ≫ nativePulledThreeDiskInclusion X x P :=
  (CellFamilySimplicialModel.isPushout (LoopCellSphericalGenerators.liftedPair X x P).fst 2
      (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)).inl_desc _ _ _

/-- Its complete original old-space leg is the computed old pullback comparison. -/
theorem upstairsThreeModelToPulled_old :
    CellFamilySimplicialModel.oldInclusion (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) ≫
      upstairsThreeModelToPulled X x P =
        oldSingularToThreePullback X x P ≫ nativePulledThreeOldInclusion X x P :=
  (CellFamilySimplicialModel.isPushout (LoopCellSphericalGenerators.liftedPair X x P).fst 2
      (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)).inr_desc _ _ _

/-- The entire actual model comparison is weak by the existing cofibrant
pushout theorem, the complete cell-family Isos, and the derived old comparison. -/
theorem upstairsThreeModelToPulled_weak :
    SSet.realizationWeakEquivalences (upstairsThreeModelToPulled X x P) := by
  let b := CellFamilySimplicialModel.boundarySum 2 (LoopCellQuotientCellPresentation.labels X x P)
  let b0 := CellFamilySimplicialModel.boundarySum 2 P
  let i0 := nativePulledThreeBoundaryToDisks X x P
  let : Mono b := by
    change Mono (CellFamilySimplicialModel.boundarySum 2
        (LoopCellQuotientCellPresentation.labels X x P))
    rw [CellFamilySimplicialModel.boundarySum_eq]
    infer_instance
  let : Mono b0 := by
    change Mono (CellFamilySimplicialModel.boundarySum 2 P)
    rw [CellFamilySimplicialModel.boundarySum_eq]
    infer_instance
  let : Mono i0 := (SSet.pullbackLegMap_isPullback _ _ _ _
    (CellFamilySimplicialModel.adjunctSquare (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)).symm).mono_fst_of_mono
  let : Cofibration b := (SSet.modelCategoryQuillen.cofibration_iff b).mpr inferInstance
  let : Cofibration i0 := (SSet.modelCategoryQuillen.cofibration_iff i0).mpr inferInstance
  let : WeakEquivalence (nativeThreeBoundaryFamilyCopiesIso X x P).hom := inferInstance
  let : WeakEquivalence (nativeThreeDiskFamilyCopiesIso X x P).hom := inferInstance
  let cOld : TopCat.toSSet.obj (LoopCellSphericalGenerators.liftedPair X x P).fst ⟶
      nativeThreeOldPullback X x P := oldSingularToThreePullback X x P
  let : WeakEquivalence cOld :=
    (weakEquivalence_iff cOld).mpr (oldSingularToThreePullback_weak X x P)
  have hCof (T : SSet.{u}) : IsCofibrant T := by
    change Cofibration (initial.to T)
    exact (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let :=
      hCof (CellFamilySimplicialModel.boundaries 2 (LoopCellQuotientCellPresentation.labels X x P))
  let := hCof (nativePulledThreeBoundaries X x P)
  let := hCof (TopCat.toSSet.obj (LoopCellSphericalGenerators.liftedPair X x P).fst)
  let := hCof (nativeThreeOldPullback X x P)
  exact (weakEquivalence_iff _).mp
    (weakEquivalence_map_of_isPushouts_of_cofibrant
      (C := SSet.{u}) (c := cOld)
      (a := (nativeThreeBoundaryFamilyCopiesIso X x P).hom)
      (b := (nativeThreeDiskFamilyCopiesIso X x P).hom)
      (d := upstairsThreeModelToPulled X x P)
      (CellFamilySimplicialModel.isPushout (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P))
      (nativePulledThree_isPushout X x P)
      (nativeThreeCopies_boundarySquare X x P) (nativeThreeCopies_attachingSquare X x P)
      (upstairsThreeModelToPulled_disks X x P) (upstairsThreeModelToPulled_old X x P))

/-- The complete actual upstairs model maps weakly into the native cover of
Sing of the SAME original three-cell attachment. -/
def upstairsThreeModelToCover : upstairsThreeModel X x P ⟶ nativeThreeCover X x P :=
  upstairsThreeModelToPulled X x P ≫ pullback.snd
    (CellFamilySimplicialModel.toSingular (originalTwo X x P) 2 P
      (LoopCellSphericalGenerators.sphericalGenerator X x P)) (nativeThreeProjection X x P)

/-- Weakness of the cover map uses both original computed comparison steps. -/
theorem upstairsThreeModelToCover_weak :
    SSet.realizationWeakEquivalences (upstairsThreeModelToCover X x P) :=
  SSet.realizationWeakEquivalences.comp_mem _ _
    (upstairsThreeModelToPulled_weak X x P) (nativePulledThree_toCover_weak X x P)

/-- Every whole original upstairs characteristic disk has the computed native lift. -/
theorem upstairsThreeModelToCover_cell (i : LoopCellQuotientCellPresentation.labels X x P) :
    CategoryTheory.Limits.Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (Δ[3] : SSet.{u})) i ≫
      CellFamilySimplicialModel.newDisks (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) ≫
      upstairsThreeModelToCover X x P = nativeThreeDiskCopy X x P i := by
  let a := CategoryTheory.Limits.Sigma.ι
      (fun _ : LoopCellQuotientCellPresentation.labels X x P => (Δ[3] : SSet.{u})) i
  let b := CellFamilySimplicialModel.newDisks (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let r := pullback.snd (CellFamilySimplicialModel.toSingular (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)) (nativeThreeProjection X x P)
  have hR : nativePulledThreeDiskInclusion X x P ≫ r =
      pullback.snd (originalThreeDiskFamilyMate X x P) (nativeThreeProjection X x P) :=
    SSet.pullbackLegMap_snd _ _ _ _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => a ≫ (f ≫ r)) (upstairsThreeModelToPulled_disks X x P)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a ≫ ((nativeThreeDiskFamilyCopiesIso X x P).hom ≫ f)) hR).trans
          ((Category.assoc _ _ _).symm.trans (nativeThreeDiskFamilyCopiesIso_ι_snd X x P i)))))

/-- The complete original old-space leg is the unchanged computed cover comparison. -/
theorem upstairsThreeModelToCover_old :
    CellFamilySimplicialModel.oldInclusion (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) ≫
      upstairsThreeModelToCover X x P = oldSingularToThreeCover X x P := by
  let r := pullback.snd (CellFamilySimplicialModel.toSingular (originalTwo X x P) 2 P
    (LoopCellSphericalGenerators.sphericalGenerator X x P)) (nativeThreeProjection X x P)
  have hR : nativePulledThreeOldInclusion X x P ≫ r =
      pullback.snd (TopCat.toSSet.map (originalThreeInclusion X x P))
          (nativeThreeProjection X x P) :=
    SSet.pullbackLegMap_snd _ _ _ _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ r) (upstairsThreeModelToPulled_old X x P)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f => oldSingularToThreePullback X x P ≫ f) hR)))


/-- The computed cover map is over the actual projection from the same
upstairs attachment to the original three-cell space. -/
theorem upstairsThreeModelToCover_projection :
    upstairsThreeModelToCover X x P ≫ nativeThreeProjection X x P =
      CellFamilySimplicialModel.toSingular (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) ≫
          TopCat.toSSet.map (upstairsThreeDown X x P) := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let c := CellFamilySimplicialModel.toSingular V 2
      (LoopCellQuotientCellPresentation.labels X x P) a
  let g := upstairsThreeModelToCover X x P
  let p := nativeThreeProjection X x P
  let f := TopCat.toSSet.map (upstairsThreeDown X x P)
  let o := CellFamilySimplicialModel.oldInclusion V 2
      (LoopCellQuotientCellPresentation.labels X x P) a
  let d := CellFamilySimplicialModel.newDisks V 2 (LoopCellQuotientCellPresentation.labels X x P) a
  let j := CellFamilyAttachment.inclusion V 2 a
  apply (CellFamilySimplicialModel.isPushout V 2
      (LoopCellQuotientCellPresentation.labels X x P) a).hom_ext
  · apply CategoryTheory.Limits.Sigma.hom_ext
    intro i
    let b := CategoryTheory.Limits.Sigma.ι
        (fun _ : LoopCellQuotientCellPresentation.labels X x P => (Δ[3] : SSet.{u})) i
    let E := sSetTopAdj.homEquiv (Δ[3] : SSet.{u}) (originalThree X x P)
    let eu := (SSet.boundary.toClassicalCellDiskArrowIso.{u} 3).hom.right
    let du := CellFamilyAttachment.cell V 2 a i
    let dy := CellFamilyAttachment.cell (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P) i.2
    have hL : b ≫ (d ≫ (g ≫ p)) = originalThreeDiskMate X x P i.2 := by
      have hCell := upstairsThreeModelToCover_cell X x P i
      have hCellP : b ≫ (d ≫ (g ≫ p)) = nativeThreeDiskCopy X x P i ≫ p := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ p) hCell
      exact hCellP.trans (nativeThreeDiskCopy_projection X x P i)
    have hTop : (eu ≫ du) ≫ upstairsThreeDown X x P = eu ≫ dy :=
      (Category.assoc _ _ _).trans (congrArg (fun k => eu ≫ k) (upstairsThreeDown_cell X x P i))
    have hC : b ≫ (d ≫ c) = sSetTopAdj.homEquiv (Δ[3] : SSet.{u}) (upstairsThreeSpace X x P)
        (eu ≫ du) :=
      (congrArg (fun k => b ≫ k) (CellFamilySimplicialModel.toSingular_disks V 2
        (LoopCellQuotientCellPresentation.labels X x P) a)).trans
          (CellFamilySimplicialModel.diskMates_ι V 2
              (LoopCellQuotientCellPresentation.labels X x P) a i)
    have hR : b ≫ (d ≫ (c ≫ f)) = originalThreeDiskMate X x P i.2 :=
      (congrArg (fun k => b ≫ k) (Category.assoc _ _ _).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ f) hC).trans
            ((sSetTopAdj.homEquiv_naturality_right (eu ≫ du) (upstairsThreeDown X x P)).symm.trans
              (congrArg E hTop))))
    exact hL.trans hR.symm
  · have hL : o ≫ (g ≫ p) = TopCat.toSSet.map (oldCoverDown X x P) ≫
        TopCat.toSSet.map (originalThreeInclusion X x P) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ p) (upstairsThreeModelToCover_old X x P)).trans
          (oldSingularToThreeCover_projection X x P))
    have hR : o ≫ (c ≫ f) = TopCat.toSSet.map (oldCoverDown X x P) ≫
        TopCat.toSSet.map (originalThreeInclusion X x P) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ f) (CellFamilySimplicialModel.toSingular_old V 2
          (LoopCellQuotientCellPresentation.labels X x P) a)).trans
            ((TopCat.toSSet.map_comp j (upstairsThreeDown X x P)).symm.trans
              ((congrArg TopCat.toSSet.map (upstairsThreeDown_old X x P)).trans
                (TopCat.toSSet.map_comp (oldCoverDown X x P) (originalThreeInclusion X x P)))))
    exact hL.trans hR.symm

/-- The model's represented point is the actual old native identity point,
followed by the original unit and original old-model inclusion. -/
abbrev upstairsThreeModelPointMap : (Δ[0] : SSet.{u}) ⟶ upstairsThreeModel X x P :=
  (SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj (originalTwo X x P))
      (LoopCellSphericalGenerators.nativeTargetPoint X x P) ≫
    sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P)) ≫
      CellFamilySimplicialModel.oldInclusion (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)

/-- The cover comparison sends that actual old identity point to the actual
three-cover identity point through the original inclusion functor. -/
theorem upstairsThreeModelPointMap_toCover :
    upstairsThreeModelPointMap X x P ≫ upstairsThreeModelToCover X x P =
      SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj (originalThree X x P))
        (nativeThreePoint X x P) := by
  let a := SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj (originalTwo X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let u := sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P)
  let j := CellFamilySimplicialModel.oldInclusion
      (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let g := upstairsThreeModelToCover X x P
  let l := oldSingularToNative X x P
  let c := SSet.KanComplex.nativeCoverMap (TopCat.toSSet.map (originalThreeInclusion X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  have hOld : j ≫ g = l ≫ c :=
    (upstairsThreeModelToCover_old X x P).trans (oldSingularToThreeCover_eq X x P)
  let E0 := LoopCellSphericalGenerators.nativeCover X x P
  let E1 := nativeThreeCover X x P
  let pa := SSet.KanComplex.nativeCoverIdentityPoint (TopCat.toSSet.obj (originalTwo X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  let t := SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj (originalThree X x P))
    (nativeThreePoint X x P)
  let pb := SSet.KanComplex.nativeCoverIdentityPoint (TopCat.toSSet.obj (originalThree X x P))
    (nativeThreePoint X x P)
  have hA : a = (SSet.const pa : (Δ[0] : SSet.{u}) ⟶ E0) :=
    ((SSet.yonedaEquiv (X := E0) (n := ⦋0⦌)).symm_apply_apply a).symm.trans
      (SSet.yonedaEquiv_symm_zero pa)
  have hT : t = (SSet.const pb : (Δ[0] : SSet.{u}) ⟶ E1) :=
    ((SSet.yonedaEquiv (X := E1) (n := ⦋0⦌)).symm_apply_apply t).symm.trans
      (SSet.yonedaEquiv_symm_zero pb)
  have hPoint : c.app (Opposite.op ⦋0⦌) pa = pb :=
    SSet.KanComplex.nativeCoverMap_identityPoint
      (TopCat.toSSet.map (originalThreeInclusion X x P))
        (LoopCellSphericalGenerators.nativeTargetPoint X x P)
  have hPointMap : a ≫ c = t :=
    (congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ E0 => k ≫ c) hA).trans
      ((SSet.const_comp pa c).trans
        ((congrArg (fun v : E1 _⦋0⦌ =>
            (SSet.const v : (Δ[0] : SSet.{u}) ⟶ E1)) hPoint).trans hT.symm))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (a ≫ u) ≫ k) hOld).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ c) (oldSingularToNative_identityPoint X x P)).trans
          hPointMap)))

private theorem actualUpstairsThreeSingularLiftExists :
    ∃ l : TopCat.toSSet.obj (upstairsThreeSpace X x P) ⟶ nativeThreeCover X x P,
      l ≫ nativeThreeProjection X x P = TopCat.toSSet.map (upstairsThreeDown X x P) ∧
        WeakEquivalence l ∧
          (upstairsThreeModelPointMap X x P ≫
            CellFamilySimplicialModel.toSingular
                (LoopCellSphericalGenerators.liftedPair X x P).fst 2
              (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)) ≫ l =
            upstairsThreeModelPointMap X x P ≫ upstairsThreeModelToCover X x P := by
  let u := CellFamilySimplicialModel.toSingular (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let g := upstairsThreeModelToCover X x P
  let f := TopCat.toSSet.map (upstairsThreeDown X x P)
  let p := nativeThreeProjection X x P
  let s := upstairsThreeModelPointMap X x P
  let : WeakEquivalence u := (weakEquivalence_iff _).mpr (upstairsThreeModel_toSingular_weak X x P)
  let : WeakEquivalence g := (weakEquivalence_iff _).mpr (upstairsThreeModelToCover_weak X x P)
  let : Fibration p := OriginalRegularThreeComparison.nativeProjection_fibration _ _
  exact OriginalRegularThreeComparison.exists_based_weak_extension u g f p s
    (upstairsThreeModelToCover_projection X x P)

/-- The actual singular set of the SAME upstairs three-cell space maps weakly
to the native cover of Sing of the SAME original three-cell space. -/
def singularUpstairsThreeToNative : TopCat.toSSet.obj (upstairsThreeSpace X x P) ⟶
    nativeThreeCover X x P :=
  Classical.choose (actualUpstairsThreeSingularLiftExists X x P)

/-- Its whole base projection is the original upstairs-to-original map. -/
theorem singularUpstairsThreeToNative_projection :
    singularUpstairsThreeToNative X x P ≫ nativeThreeProjection X x P =
        TopCat.toSSet.map (upstairsThreeDown X x P) :=
  (Classical.choose_spec (actualUpstairsThreeSingularLiftExists X x P)).1

/-- Its weakness is derived from the original two actual model comparisons. -/
theorem singularUpstairsThreeToNative_weak :
    SSet.realizationWeakEquivalences (singularUpstairsThreeToNative X x P) :=
  (weakEquivalence_iff _).mp (Classical.choose_spec
      (actualUpstairsThreeSingularLiftExists X x P)).2.1

/-- The exact original model point is retained, without normalizing any chosen disk path. -/
theorem singularUpstairsThreeToNative_modelPoint :
    (upstairsThreeModelPointMap X x P ≫
      CellFamilySimplicialModel.toSingular (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)) ≫
      singularUpstairsThreeToNative X x P = upstairsThreeModelPointMap X x P ≫
          upstairsThreeModelToCover X x P :=
  (Classical.choose_spec (actualUpstairsThreeSingularLiftExists X x P)).2.2

/-- The entire model leg is the SAME already constructed disk/old-space map,
by connected-cover uniqueness, not just a weakly equivalent replacement. -/
theorem singularUpstairsThreeToNative_model :
    CellFamilySimplicialModel.toSingular (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) ≫
      singularUpstairsThreeToNative X x P = upstairsThreeModelToCover X x P := by
  let u := CellFamilySimplicialModel.toSingular (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let g := upstairsThreeModelToCover X x P
  let l := singularUpstairsThreeToNative X x P
  let p := nativeThreeProjection X x P
  let s := upstairsThreeModelPointMap X x P
  let : (nativeThreeCover X x P).IsConnected := SSet.KanComplex.nativeCover_isConnected
  let : (SSet.mapFundamentalGroupoid g).IsEquivalence :=
    SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
        (upstairsThreeModelToCover_weak X x P)
  let : (upstairsThreeModel X x P).IsConnected :=
    OriginalRegularThreeComparison.connected_of_full_fundamentalGroupoid g (SSet.yonedaEquiv s)
  have hP : (u ≫ l) ≫ p = g ≫ p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => u ≫ f) (singularUpstairsThreeToNative_projection X x P)).trans
        (upstairsThreeModelToCover_projection X x P).symm)
  exact OriginalRegularThreeComparison.nativeLift_hom_ext_of_connected_pointMap
    (u ≫ l) g hP s (singularUpstairsThreeToNative_modelPoint X x P)

/-- The model equality retains the ENTIRE characteristic disk in every quotient/P copy. -/
theorem singularUpstairsThreeToNative_cell (i : LoopCellQuotientCellPresentation.labels X x P) :
    sSetTopAdj.homEquiv (Δ[3] : SSet.{u}) (upstairsThreeSpace X x P)
        ((SSet.boundary.toClassicalCellDiskArrowIso 3).hom.right ≫
          CellFamilyAttachment.cell (LoopCellSphericalGenerators.liftedPair X x P).fst 2
            (chosenSphericalCopy X x P) i) ≫ singularUpstairsThreeToNative X x P =
      nativeThreeDiskCopy X x P i := by
  let a := CategoryTheory.Limits.Sigma.ι
      (fun _ : LoopCellQuotientCellPresentation.labels X x P => (Δ[3] : SSet.{u})) i
  let j := CellFamilySimplicialModel.newDisks (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let c := CellFamilySimplicialModel.toSingular (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let l := singularUpstairsThreeToNative X x P
  have hC : a ≫ (j ≫ c) = sSetTopAdj.homEquiv (Δ[3] : SSet.{u}) (upstairsThreeSpace X x P)
      ((SSet.boundary.toClassicalCellDiskArrowIso 3).hom.right ≫
        CellFamilyAttachment.cell (LoopCellSphericalGenerators.liftedPair X x P).fst 2
            (chosenSphericalCopy X x P) i) :=
    (congrArg (fun f => a ≫ f) (CellFamilySimplicialModel.toSingular_disks
      (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P))).trans
          (CellFamilySimplicialModel.diskMates_ι
              (LoopCellSphericalGenerators.liftedPair X x P).fst 2
            (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) i)
  exact (congrArg (fun f => f ≫ l) hC.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => a ≫ f) ((Category.assoc _ _ _).trans
        (congrArg (fun f => j ≫ f) (singularUpstairsThreeToNative_model X x P)))).trans
          (upstairsThreeModelToCover_cell X x P i)))


/-- The whole singular old-space inclusion is strictly compatible with the
computed native old pullback, as an equation of the actual relative-pair maps. -/
theorem singularUpstairsThreeToNative_old :
    TopCat.toSSet.map (CellFamilyAttachment.inclusion
        (LoopCellSphericalGenerators.liftedPair X x P).fst 2
        (chosenSphericalCopy X x P)) ≫ singularUpstairsThreeToNative X x P =
      oldSingularToThreeCover X x P := by
  let j := CellFamilySimplicialModel.oldInclusion
      (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let c := CellFamilySimplicialModel.toSingular (LoopCellSphericalGenerators.liftedPair X x P).fst 2
    (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  let l := singularUpstairsThreeToNative X x P
  have hJ : j ≫ c = TopCat.toSSet.map
      (CellFamilyAttachment.inclusion (LoopCellSphericalGenerators.liftedPair X x P).fst 2
          (chosenSphericalCopy X x P)) :=
    CellFamilySimplicialModel.toSingular_old (LoopCellSphericalGenerators.liftedPair X x P).fst 2
      (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P)
  exact (congrArg (fun f => f ≫ l) hJ.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => j ≫ f) (singularUpstairsThreeToNative_model X x P)).trans
        (upstairsThreeModelToCover_old X x P)))

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The actual topological three-space projection is invariant under its
entire geometric deck action, while every cell label still multiplies on the left. -/
theorem upstairsThreeDown_deck (q : FundamentalGroup X x ⧸ P) :
    upstairsThreeDeck X x P q ≫ upstairsThreeDown X x P = upstairsThreeDown X x P := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let j := CellFamilyAttachment.inclusion V 2 a
  let d := SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q)
  let D := upstairsThreeDeck X x P q
  let F := upstairsThreeDown X x P
  let b := oldCoverDown X x P
  let k := originalThreeInclusion X x P
  have hTop : d ≫ SSet.toTop.map (LoopCellPulledSimplicialModel.projection X x P) =
      SSet.toTop.map (LoopCellPulledSimplicialModel.projection X x P) :=
    (SSet.toTop.map_comp (LoopCellQuotientCellPresentation.nativeDeck X x P q)
      (LoopCellPulledSimplicialModel.projection X x P)).symm.trans
        (congrArg SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck_projection X x P q))
  have hd : d ≫ b = b :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ sSetTopAdj.counit.app (originalTwo X x P)) hTop)
  apply CellFamilyAttachment.hom_ext V 2 a
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ F) (upstairsThreeDeck_old X x P q)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => d ≫ f) (upstairsThreeDown_old X x P)).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun f => f ≫ k) hd).trans (upstairsThreeDown_old X x P).symm)))))
  · intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ F) (upstairsThreeDeck_cell X x P q i)).trans
        ((upstairsThreeDown_cell X x P (q*i.1,i.2)).trans (upstairsThreeDown_cell X x P i).symm))

/-- The computed singular comparison respects EVERY quotient deck element,
using actual projection invariance and the whole original old-space equation. -/
theorem singularUpstairsThreeToNative_deck (q : FundamentalGroup X x ⧸ P) :
    TopCat.toSSet.map (upstairsThreeDeck X x P q) ≫ singularUpstairsThreeToNative X x P =
      singularUpstairsThreeToNative X x P ≫
          SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P q) := by
  let V := (LoopCellSphericalGenerators.liftedPair X x P).fst
  let a := chosenSphericalCopy X x P
  let i := TopCat.toSSet.map (CellFamilyAttachment.inclusion V 2 a)
  let d := TopCat.toSSet.map (upstairsThreeDeck X x P q)
  let d0 := TopCat.toSSet.map (SSet.toTop.map (LoopCellQuotientCellPresentation.nativeDeck X x P q))
  let d3 := SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P q)
  let l := singularUpstairsThreeToNative X x P
  let g0 := oldSingularToThreeCover X x P
  let p := nativeThreeProjection X x P
  let f := TopCat.toSSet.map (upstairsThreeDown X x P)
  let s0 := SSet.KanComplex.nativeCoverIdentityPointMap (TopCat.toSSet.obj (originalTwo X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P) ≫
      sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P)
  let s := s0 ≫ i
  let : (LoopCellSphericalGenerators.nativeCover X x P).IsConnected :=
      SSet.KanComplex.nativeCover_isConnected
  let : PathConnectedSpace V := SSet.pathConnectedSpace_realization_of_isConnected
    (LoopCellSphericalGenerators.nativeCover X x P)
  let : PathConnectedSpace (upstairsThreeSpace X x P) :=
      CellFamilyAttachment.pathConnectedSpace V 2 a
  let : (TopCat.toSSet.obj (upstairsThreeSpace X x P)).IsConnected := inferInstance
  have hProj : d ≫ f = f :=
    (TopCat.toSSet.map_comp _ _).symm.trans
        (congrArg TopCat.toSSet.map (upstairsThreeDown_deck X x P q))
  have hPL : (d ≫ l) ≫ p = f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => d ≫ k) (singularUpstairsThreeToNative_projection X x P)).trans hProj)
  have hPR : (l ≫ d3) ≫ p = f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => l ≫ k) (SSet.KanComplex.nativeCoverDeckMap_projection
          (quotientThreeDeckIndex X x P q))).trans
        (singularUpstairsThreeToNative_projection X x P))
  have hI : i ≫ d = d0 ≫ i :=
    (TopCat.toSSet.map_comp _ _).symm.trans
      ((congrArg TopCat.toSSet.map (upstairsThreeDeck_old X x P q)).trans
          (TopCat.toSSet.map_comp _ _))
  have hPre : i ≫ (d ≫ l) = i ≫ (l ≫ d3) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ l) hI).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => d0 ≫ k) (singularUpstairsThreeToNative_old X x P)).trans
            ((oldSingularToThreeCover_deck X x P q).trans
              ((congrArg (fun k => k ≫ d3) (singularUpstairsThreeToNative_old X x P).symm).trans
                (Category.assoc _ _ _))))))
  have hs : s ≫ (d ≫ l) = s ≫ (l ≫ d3) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => s0 ≫ k) hPre).trans (Category.assoc _ _ _).symm)
  exact OriginalRegularThreeComparison.nativeLift_hom_ext_of_connected_pointMap
    (d ≫ l) (l ≫ d3) (hPL.trans hPR.symm) s hs

/-- The target relative pair uses the literal original old-cover pullback and native projection. -/
abbrev nativeThreePair : SSetPair.{u} := by
  let f := originalThreeInclusion X x P
  letI : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  letI : Mono (TopCat.toSSet.map f) := inferInstance
  exact SSetPair.of (pullback.snd (TopCat.toSSet.map f) (nativeThreeProjection X x P))

/-- The source pair is the singular image of the actual same upstairs attachment inclusion. -/
abbrev singularUpstairsThreePair : SSetPair.{u} := by
  let f := CellFamilyAttachment.inclusion (LoopCellSphericalGenerators.liftedPair X x P).fst 2
      (chosenSphericalCopy X x P)
  letI : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (LoopCellSphericalGenerators.liftedPair X x P).fst 2
      (chosenSphericalCopy X x P))
  exact SSetPair.of (TopCat.toSSet.map f)

/-- The whole strict pair comparison is computed from the actual singular
comparison and its original old-space leg. -/
def singularUpstairsThreePairComparison : singularUpstairsThreePair X x P ⟶ nativeThreePair X x P :=
  SSetPair.ofHom (singularUpstairsThreeToNative X x P) (oldSingularToThreePullback X x P)
    (singularUpstairsThreeToNative_old X x P).symm

/-- The ambient component is the SAME constructed singular upstairs comparison. -/
theorem singularUpstairsThreePairComparison_right :
    (singularUpstairsThreePairComparison X x P).hom.right =
        singularUpstairsThreeToNative X x P := by
  rfl

/-- The old-space component is the SAME original pulled-cover comparison. -/
theorem singularUpstairsThreePairComparison_left :
    (singularUpstairsThreePairComparison X x P).hom.left = oldSingularToThreePullback X x P := by
  rfl


section RelativeChains

variable {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]

private def relativeThreeChainArrow (R : C) :
    Arrow.mk ((singularPairShortComplexFunctor C R).obj (upstairsThreePair X x P)).f ⟶
      Arrow.mk (SSet.chainComplexMap (nativeThreePair X x P).hom R) := by
  let F := (SSet.chainComplexFunctor C).obj R
  let f := TopCat.toSSet.map (CellFamilyAttachment.inclusion
    (LoopCellSphericalGenerators.liftedPair X x P).fst 2 (chosenSphericalCopy X x P))
  let p := (nativeThreePair X x P).hom
  let a := oldSingularToThreePullback X x P
  let b := singularUpstairsThreeToNative X x P
  have h : a ≫ p = f ≫ b := (singularUpstairsThreeToNative_old X x P).symm
  have hC : F.map a ≫ F.map p = F.map f ≫ F.map b :=
    (F.map_comp a p).symm.trans ((congrArg F.map h).trans (F.map_comp f b))
  exact Arrow.homMk (F.map a) (F.map b) hC

/-- The actual relative chain comparison uses the original singular quotient
and literal native pulled-cover quotient, with independent coefficient category. -/
def relativeThreeChainMap (R : C) :
    (relativeSingularChainFunctor C R).obj (upstairsThreePair X x P) ⟶
      (nativeThreePair X x P).chainComplex R := by
  let S := (singularPairShortComplexFunctor C R).obj (upstairsThreePair X x P)
  exact CokernelCofork.mapOfIsColimit
    (singularPairShortComplex_shortExact C R (upstairsThreePair X x P)).gIsCokernel
    ((nativeThreePair X x P).cokernelCoforkChainComplex R)
    (relativeThreeChainArrow X x P R)

/-- The whole original upstairs quotient commutes with the same ambient comparison. -/
theorem relativeThreeChainMap_projection (R : C) :
    relativeSingularChainQuotient C R (upstairsThreePair X x P) ≫ relativeThreeChainMap X x P R =
      SSet.chainComplexMap (singularUpstairsThreeToNative X x P) R ≫
        (nativeThreePair X x P).chainComplexπ R := by
  exact CokernelCofork.π_mapOfIsColimit
    (singularPairShortComplex_shortExact C R (upstairsThreePair X x P)).gIsCokernel
    ((nativeThreePair X x P).cokernelCoforkChainComplex R)
    (relativeThreeChainArrow X x P R)

private def relativeThreeShortComplexMap (R : C) :
    (singularPairShortComplexFunctor C R).obj (upstairsThreePair X x P) ⟶
      (nativeThreePair X x P).chainComplexShortComplex R :=
  ShortComplex.homMk (SSet.chainComplexMap (oldSingularToThreePullback X x P) R)
    (SSet.chainComplexMap (singularUpstairsThreeToNative X x P) R)
    (relativeThreeChainMap X x P R) (relativeThreeChainArrow X x P R).w
    (relativeThreeChainMap_projection X x P R).symm

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
private theorem oldPullback_kan : SSet.KanComplex (nativeThreeOldPullback X x P) := by
  let f := TopCat.toSSet.map (originalThreeInclusion X x P)
  let p := nativeThreeProjection X x P
  let q := pullback.fst f p
  let : Fibration p := OriginalRegularThreeComparison.nativeProjection_fibration _ _
  let : Fibration q := inferInstance
  exact isFibrant_of_fibration q

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
private theorem nativeThreeCover_kan : SSet.KanComplex (nativeThreeCover X x P) := by
  let p := nativeThreeProjection X x P
  let : Fibration p := OriginalRegularThreeComparison.nativeProjection_fibration _ _
  exact isFibrant_of_fibration p

/-- Both relative comparison components are Kan weak equivalences, so the
existing arbitrary-category chain theorem and stock relative LES prove a
quasi-isomorphism for every coefficient object. No unit-chain generalization is used. -/
theorem relativeThreeChainMap_quasiIso (R : C) : QuasiIso (relativeThreeChainMap X x P R) := by
  let : SSet.KanComplex (nativeThreeOldPullback X x P) := oldPullback_kan X x P
  let : SSet.KanComplex (nativeThreeCover X x P) := nativeThreeCover_kan X x P
  let S := (singularPairShortComplexFunctor C R).obj (upstairsThreePair X x P)
  let T := (nativeThreePair X x P).chainComplexShortComplex R
  let a := oldSingularToThreePullback X x P
  let b := singularUpstairsThreeToNative X x P
  let ψ := relativeThreeShortComplexMap X x P R
  have ha : SSet.KanComplex.W a := (SSet.KanComplex.W_iff_realizationWeakEquivalence a).mpr
    (oldSingularToThreePullback_weak X x P)
  have hb : SSet.KanComplex.W b := (SSet.KanComplex.W_iff_realizationWeakEquivalence b).mpr
    (singularUpstairsThreeToNative_weak X x P)
  have hA : QuasiIso ψ.τ₁ := ha.quasiIso_chainComplexMap R
  have hB : QuasiIso ψ.τ₂ := hb.quasiIso_chainComplexMap R
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (singularPairShortComplex_shortExact C R (upstairsThreePair X x P))
    ((nativeThreePair X x P).shortExact_chainComplexShortComplex R) hA hB

/-- The same actual map identifies relative homology in every degree and
retains independent coefficient universes through the required coproducts. -/
def relativeThreeHomologyIso (R : C) (n : ℕ) :
    (relativeSingularHomologyFunctor C R n).obj (upstairsThreePair X x P) ≅
      (nativeThreePair X x P).homology R n := by
  let a := relativeThreeChainMap X x P R
  let m : (relativeSingularHomologyFunctor C R n).obj (upstairsThreePair X x P) ⟶
      (nativeThreePair X x P).homology R n := HomologicalComplex.homologyMap a n
  have hQ : QuasiIso a := relativeThreeChainMap_quasiIso X x P R
  have hIso : IsIso m := (_root_.quasiIsoAt_iff_isIso_homologyMap a n).mp (hQ.quasiIsoAt n)
  exact @asIso _ _ _ _ m hIso

private theorem relativeThreeHomologyIso_hom (R : C) (n : ℕ) :
    (relativeThreeHomologyIso X x P R n).hom =
      HomologicalComplex.homologyMap (relativeThreeChainMap X x P R) n := by rfl

/-- The complete same ambient homology map is an isomorphism with arbitrary coefficients. -/
def ambientThreeHomologyIso (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (upstairsThreeSpace X x P) ≅
      (nativeThreeCover X x P).homology R n := by
  letI : SSet.KanComplex (nativeThreeCover X x P) := nativeThreeCover_kan X x P
  let b := singularUpstairsThreeToNative X x P
  have hb : SSet.KanComplex.W b := (SSet.KanComplex.W_iff_realizationWeakEquivalence b).mpr
    (singularUpstairsThreeToNative_weak X x P)
  let a := SSet.chainComplexMap b R
  let m : ((singularHomologyFunctor C n).obj R).obj (upstairsThreeSpace X x P) ⟶
      (nativeThreeCover X x P).homology R n := HomologicalComplex.homologyMap a n
  have hQ : QuasiIso a := hb.quasiIso_chainComplexMap R
  have hIso : IsIso m := (_root_.quasiIsoAt_iff_isIso_homologyMap a n).mp (hQ.quasiIsoAt n)
  exact @asIso _ _ _ _ m hIso

private theorem ambientThreeHomologyIso_hom (R : C) (n : ℕ) :
    (ambientThreeHomologyIso X x P R n).hom =
      HomologicalComplex.homologyMap (SSet.chainComplexMap
          (singularUpstairsThreeToNative X x P) R) n := by rfl

/-- The full quotient-to-relative homology square uses the original two quotients. -/
theorem relativeThreeHomologyIso_projection (R : C) (n : ℕ) :
    singularHomologyPairQuotientMap C R (upstairsThreePair X x P) n ≫
      (relativeThreeHomologyIso X x P R n).hom =
        (ambientThreeHomologyIso X x P R n).hom ≫ (nativeThreePair X x P).homologyπ R n := by
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n
  rw [relativeThreeHomologyIso_hom, ambientThreeHomologyIso_hom]
  change H.map (relativeSingularChainQuotient C R (upstairsThreePair X x P)) ≫
      H.map (relativeThreeChainMap X x P R) =
    H.map (SSet.chainComplexMap (singularUpstairsThreeToNative X x P) R) ≫
      H.map ((nativeThreePair X x P).chainComplexπ R)
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map (relativeThreeChainMap_projection X x P R)).trans (H.map_comp _ _))

/-- The inverse also commutes with the same entire quotient maps. -/
theorem relativeThreeHomologyIso_inverse_projection (R : C) (n : ℕ) :
    (nativeThreePair X x P).homologyπ R n ≫ (relativeThreeHomologyIso X x P R n).inv =
      (ambientThreeHomologyIso X x P R n).inv ≫
        singularHomologyPairQuotientMap C R (upstairsThreePair X x P) n := by
  let e := relativeThreeHomologyIso X x P R n
  let a := ambientThreeHomologyIso X x P R n
  let q := singularHomologyPairQuotientMap C R (upstairsThreePair X x P) n
  let r := (nativeThreePair X x P).homologyπ R n
  apply (cancel_mono e.hom).mp
  have hL : (r ≫ e.inv) ≫ e.hom = r :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => r ≫ f) e.inv_hom_id).trans (Category.comp_id _))
  have hR : (a.inv ≫ q) ≫ e.hom = r :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => a.inv ≫ f) (relativeThreeHomologyIso_projection X x P R n)).trans
        (a.inv_hom_id_assoc r))
  exact hL.trans hR.symm

/-- The actual native relative connecting morphism, before choosing any cell coordinates. -/
def nativeThreeRelativeBoundary (R : C) :
    (nativeThreePair X x P).homology R 3 ⟶ (nativeThreeOldPullback X x P).homology R 2 :=
  ((nativeThreePair X x P).shortExact_chainComplexShortComplex R).δ 3 2 (by simp)

/-- The original relative LES commutes with the actual pair comparison on
whole morphisms, not just on selected homology classes. -/
theorem relativeThreeHomologyIso_boundary (R : C) :
    (relativeThreeHomologyIso X x P R 3).hom ≫ nativeThreeRelativeBoundary X x P R =
      (relativeSingularBoundary C R 2).app (upstairsThreePair X x P) ≫
        HomologicalComplex.homologyMap (SSet.chainComplexMap
            (oldSingularToThreePullback X x P) R) 2 := by
  let ψ := relativeThreeShortComplexMap X x P R
  let hS := singularPairShortComplex_shortExact C R (upstairsThreePair X x P)
  let hT := (nativeThreePair X x P).shortExact_chainComplexShortComplex R
  have hτ₃ : ψ.τ₃ = relativeThreeChainMap X x P R := by rfl
  have hτ₁ : ψ.τ₁ = SSet.chainComplexMap (oldSingularToThreePullback X x P) R := by rfl
  have hδ : (relativeSingularBoundary C R 2).app (upstairsThreePair X x P) =
      hS.δ 3 2 (by simp) := by rfl
  have hNat := (HomologicalComplex.HomologySequence.δ_naturality ψ
    (singularPairShortComplex_shortExact C R (upstairsThreePair X x P))
    ((nativeThreePair X x P).shortExact_chainComplexShortComplex R) 3 2 (by simp)).symm
  rw [hτ₃, hτ₁] at hNat
  rw [relativeThreeHomologyIso_hom, hδ]
  exact hNat

end RelativeChains


/-- The original three-space basepoint is the literal image of the original X point through both
actual inclusions. -/
abbrev originalThreeBasePoint : originalThree X x P :=
  originalThreeInclusion X x P (LoopCellAttachment.inclusion X x P x)

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The computed native point is exactly that original singular basepoint,
using the existing source point equation and original singular-map point law. -/
theorem nativeThreePoint_eq_original : nativeThreePoint X x P =
    TopCat.toSSetObj₀Equiv.symm (originalThreeBasePoint X x P) := by
  let f := originalThreeInclusion X x P
  let z := LoopCellAttachment.inclusion X x P x
  have hV : (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm z) =
      TopCat.toSSetObj₀Equiv.symm (f z) :=
    congrArg (fun v : SSet.FundamentalGroupoid (TopCat.toSSet.obj (originalThree X x P)) => v.pt)
      (TopCat.singularMappedVertex_eq f z)
  exact (congrArg (fun t => (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌) t)
    (nativeTargetPoint_eq_original X x P)).trans hV

/-- The actual original regular relative chain complex uses the original
three-cell inclusion and literal original image basepoint. -/
abbrev originalRegularThreeChains : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  TopCat.originalRegularRelativeChainComplex (originalThreeInclusion X x P)
      (originalThreeBasePoint X x P)

/-- Its same original regular covering pullback is a pair, with monicity derived from the actual
inclusion. -/
abbrev originalRegularThreeNativePair : SSetPair.{u} := by
  let f := originalThreeInclusion X x P
  letI : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  exact TopCat.originalRegularPulledCoverPair f (originalThreeBasePoint X x P)

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The original regular native pair is the SAME computed pair after the proved point equation. -/
theorem originalRegularThreePair_eq_native : originalRegularThreeNativePair X x P =
    nativeThreePair X x P := by
  let f := TopCat.toSSet.map (originalThreeInclusion X x P)
  let : Mono (originalThreeInclusion X x P) := (TopCat.mono_iff_injective _).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let : Mono f := inferInstance
  let F := fun y : (TopCat.toSSet.obj (originalThree X x P)) _⦋0⦌ =>
    SSetPair.of
        (pullback.snd f (SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (originalThree X x P)) y))
  exact congrArg F (nativeThreePoint_eq_original X x P).symm

/-- The exact ORIGINAL regular chain short complex, before any basis or covering-coordinate
transport. -/
abbrev originalRegularThreeShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  by
    let f := originalThreeInclusion X x P
    let y := originalThreeBasePoint X x P
    let m := TopCat.localCoefficientPullbackChainMap f
      (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
    let q := TopCat.originalRegularRelativeChainProjection f y
    let e := eqToIso (TopCat.originalRegularRelativeChainComplex_eq_cokernel f y)
    have hQ : q ≫ e.hom = cokernel.π m :=
      TopCat.originalRegularRelativeChainProjection_eq_cokernelπ f y
    have hZero : m ≫ q = 0 := by
      apply (cancel_mono e.hom).mp
      exact (Category.assoc m q e.hom).trans
        ((congrArg (fun k => m ≫ k) hQ).trans
          ((cokernel.condition m).trans
            (show (0 : _ ⟶ _) ≫ e.hom = 0 from zero_comp).symm))
    exact ShortComplex.mk m q hZero

private def originalRegularThreeShortComplexCokernelIso :
    originalRegularThreeShortComplex X x P ≅
      ShortComplex.cokernelSequence
        (TopCat.localCoefficientPullbackChainMap (originalThreeInclusion X x P)
          (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk (originalThreeBasePoint X x P)))) := by
  let f := originalThreeInclusion X x P
  let y := originalThreeBasePoint X x P
  let m := TopCat.localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let q := TopCat.originalRegularRelativeChainProjection f y
  let e := eqToIso (TopCat.originalRegularRelativeChainComplex_eq_cokernel f y)
  have hQ : q ≫ e.hom = cokernel.π m :=
    TopCat.originalRegularRelativeChainProjection_eq_cokernelπ f y
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
    ((Category.id_comp m).trans (Category.comp_id m).symm)
    ((Category.id_comp (cokernel.π m)).trans hQ.symm)

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- Short exactness belongs to that same original quotient sequence, by the actual monic
inclusion. -/
theorem originalRegularThreeShortExact : (originalRegularThreeShortComplex X x P).ShortExact := by
  let f := originalThreeInclusion X x P
  let : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  exact ShortComplex.shortExact_of_iso
    (originalRegularThreeShortComplexCokernelIso X x P).symm
      (TopCat.originalRegularRelative_shortExact f (originalThreeBasePoint X x P))

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
private theorem originalRegularThreeShortExact_delta_cokernel :
    HomologicalComplex.homologyMap
        (originalRegularThreeShortComplexCokernelIso X x P).hom.τ₃ 3 ≫
      (TopCat.originalRegularRelative_shortExact
        (originalThreeInclusion X x P) (originalThreeBasePoint X x P)).δ 3 2 (by simp) =
        (originalRegularThreeShortExact X x P).δ 3 2 (by simp) := by
  let f := originalThreeInclusion X x P
  let : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let e := originalRegularThreeShortComplexCokernelIso X x P
  let hS := originalRegularThreeShortExact X x P
  let hT := TopCat.originalRegularRelative_shortExact f (originalThreeBasePoint X x P)
  have h := (HomologicalComplex.HomologySequence.δ_naturality e.hom hS hT 3 2 (by simp)).symm
  have hId : HomologicalComplex.homologyMap e.hom.τ₁ 2 = 𝟙 _ := by
    change HomologicalComplex.homologyMap (𝟙 _) 2 = 𝟙 _
    exact HomologicalComplex.homologyMap_id _ _
  exact h.trans ((congrArg (fun k => hS.δ 3 2 (by simp) ≫ k) hId).trans
    (Category.comp_id _))

/-- The actual old regular-coefficient chains identify with the same original pulled cover's old
chains. -/
def originalRegularThreeNativeOldModuleChainIso :
    (originalRegularThreeShortComplex X x P).X₁ ≅
      (nativeThreeOldPullback X x P).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let f := originalThreeInclusion X x P
  let y := originalThreeBasePoint X x P
  letI : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let h := originalRegularThreePair_eq_native X x P
  exact TopCat.originalTopRegularPullbackCoverChainIso f y ≪≫
    eqToIso (congrArg (fun A : SSetPair.{u} => A.snd.chainComplex
      (ModuleCat.of ℤ (ULift.{u} ℤ))) h)

/-- The whole original relative regular chains identify with the same native
pair in the ORIGINAL integer-module category. -/
def originalRegularThreeNativeRelativeModuleChainIso : originalRegularThreeChains X x P ≅
    (nativeThreePair X x P).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let f := originalThreeInclusion X x P
  let y := originalThreeBasePoint X x P
  letI : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let h := originalRegularThreePair_eq_native X x P
  exact TopCat.originalRegularRelativeChainIso f y ≪≫
    eqToIso (congrArg (fun A : SSetPair.{u} => A.chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))) h)

/-- The original absolute regular chains use the same ambient native cover in the original module
category. -/
def originalRegularThreeNativeAmbientModuleChainIso : (originalRegularThreeShortComplex X x P).X₂ ≅
    (nativeThreeCover X x P).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let f := originalThreeInclusion X x P
  let y := originalThreeBasePoint X x P
  letI : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let h := originalRegularThreePair_eq_native X x P
  exact TopCat.originalTopRegularCoverChainIso (originalThree X x P) y ≪≫
    eqToIso (congrArg (fun A : SSetPair.{u} => A.fst.chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))) h)

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The ORIGINAL whole inclusion chain map commutes with both same native module comparisons. -/
theorem originalRegularThreeNativeModule_inclusion :
    (originalRegularThreeShortComplex X x P).f ≫
        (originalRegularThreeNativeAmbientModuleChainIso X x P).hom =
      (originalRegularThreeNativeOldModuleChainIso X x P).hom ≫
        SSet.chainComplexMap (nativeThreePair X x P).hom (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let f := originalThreeInclusion X x P
  let y := originalThreeBasePoint X x P
  let : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let A := TopCat.originalRegularPulledCoverPair f y
  let B := nativeThreePair X x P
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let h : A = B := originalRegularThreePair_eq_native X x P
  let a := TopCat.originalTopRegularPullbackCoverChainIso f y
  let b := TopCat.originalTopRegularCoverChainIso (originalThree X x P) y
  let t := eqToIso (congrArg (fun A : SSetPair.{u} => A.snd.chainComplex R) h)
  let u := eqToIso (congrArg (fun A : SSetPair.{u} => A.fst.chainComplex R) h)
  let m := (originalRegularThreeShortComplex X x P).f
  have h0 : m ≫ b.hom = a.hom ≫ SSet.chainComplexMap A.hom R :=
    TopCat.originalTopRegularCoverChainMap_square f y
  have h1 : SSet.chainComplexMap A.hom R ≫ u.hom = t.hom ≫ SSet.chainComplexMap B.hom R :=
    OriginalRegularThreeComparison.pairChainInclusion_transport A B h R
  change m ≫ (b.hom ≫ u.hom) = (a.hom ≫ t.hom) ≫ SSet.chainComplexMap B.hom R
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ u.hom) h0).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => a.hom ≫ k) h1).trans (Category.assoc _ _ _).symm)))

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The ORIGINAL whole relative quotient commutes with the same module comparisons. -/
theorem originalRegularThreeNativeModule_projection :
    (originalRegularThreeShortComplex X x P).g ≫
        (originalRegularThreeNativeRelativeModuleChainIso X x P).hom =
      (originalRegularThreeNativeAmbientModuleChainIso X x P).hom ≫
        (nativeThreePair X x P).chainComplexπ (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let f := originalThreeInclusion X x P
  let y := originalThreeBasePoint X x P
  let : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let A := TopCat.originalRegularPulledCoverPair f y
  let B := nativeThreePair X x P
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let h : A = B := originalRegularThreePair_eq_native X x P
  let a := TopCat.originalRegularRelativeChainIso f y
  let b := TopCat.originalTopRegularCoverChainIso (originalThree X x P) y
  let t := eqToIso (congrArg (fun A : SSetPair.{u} => A.chainComplex R) h)
  let u := eqToIso (congrArg (fun A : SSetPair.{u} => A.fst.chainComplex R) h)
  let q := (originalRegularThreeShortComplex X x P).g
  have h0 : q ≫ a.hom = b.hom ≫ A.chainComplexπ R :=
      TopCat.originalRegularRelativeChainIso_projection f y
  have h1 : A.chainComplexπ R ≫ t.hom = u.hom ≫ B.chainComplexπ R :=
    OriginalNativeRelativeBasis.stockRelativeQuotient_transport_coefficients A B h R
  change q ≫ (a.hom ≫ t.hom) = (b.hom ≫ u.hom) ≫ B.chainComplexπ R
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ t.hom) h0).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => b.hom ≫ k) h1).trans (Category.assoc _ _ _).symm)))

/-- The original old regular chains keep the SAME native old pullback after scalar-category
change. -/
def originalRegularThreeNativeOldChainIso :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (originalRegularThreeShortComplex X x P).X₁ ≅
        (nativeThreeOldPullback X x P).chainComplex
            (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  exact (U.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
      (originalRegularThreeNativeOldModuleChainIso X x P) ≪≫
    (SSet.mapChainComplexFunctorIso U R).app (nativeThreeOldPullback X x P)

/-- The original relative regular chain Iso retains the actual original
quotient, changing only the scalar category and proved native point coordinates. -/
def originalRegularThreeNativeChainIso :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (originalRegularThreeChains X x P) ≅
        (nativeThreePair X x P).chainComplex
            (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  exact (U.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
      (originalRegularThreeNativeRelativeModuleChainIso X x P) ≪≫
    OriginalNativeRelativeBasis.forgetRelativeChainIso (nativeThreePair X x P)

/-- The entire ambient regular chain comparison uses the same native cover
and scalar-category comparison, with no expected relative homology input. -/
def originalRegularThreeNativeAmbientChainIso :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
        (_root_.FundamentalGroupoid.mk (originalThreeBasePoint X x P)))) ≅
          (nativeThreeCover X x P).chainComplex
              (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  exact (U.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
      (originalRegularThreeNativeAmbientModuleChainIso X x P) ≪≫
    (SSet.mapChainComplexFunctorIso U R).app (nativeThreeCover X x P)

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The whole ORIGINAL regular quotient chain map commutes with the SAME two relative and ambient
comparisons. -/
theorem originalRegularThreeNativeChainIso_projection :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (TopCat.originalRegularRelativeChainProjection (originalThreeInclusion X x P)
          (originalThreeBasePoint X x P)) ≫
        (originalRegularThreeNativeChainIso X x P).hom =
      (originalRegularThreeNativeAmbientChainIso X x P).hom ≫
        (nativeThreePair X x P).chainComplexπ
            (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let q := (originalRegularThreeShortComplex X x P).g
  let e := originalRegularThreeNativeRelativeModuleChainIso X x P
  let a := originalRegularThreeNativeAmbientModuleChainIso X x P
  let p := (nativeThreePair X x P).chainComplexπ (ModuleCat.of ℤ (ULift.{u} ℤ))
  let b := OriginalNativeRelativeBasis.forgetRelativeChainIso (nativeThreePair X x P)
  let c := (SSet.mapChainComplexFunctorIso U (ModuleCat.of ℤ (ULift.{u} ℤ))).app
      (nativeThreeCover X x P)
  have h0 : F.map q ≫ F.map e.hom = F.map a.hom ≫ F.map p :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map (originalRegularThreeNativeModule_projection X x P)).trans (F.map_comp _ _))
  have h1 : F.map p ≫ b.hom = c.hom ≫
      (nativeThreePair X x P).chainComplexπ (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
    OriginalNativeRelativeBasis.forgetRelativeChainIso_projection (nativeThreePair X x P)
  change F.map q ≫ (F.map e.hom ≫ b.hom) =
    (F.map a.hom ≫ c.hom) ≫ (nativeThreePair X x P).chainComplexπ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ b.hom) h0).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => F.map a.hom ≫ k) h1).trans (Category.assoc _ _ _).symm)))

/-- The same ORIGINAL regular relative homology object, in its original ModuleCat carrier. -/
abbrev originalRegularThreeHomology (n : ℕ) : ModuleCat.{u} ℤ :=
  (originalRegularThreeChains X x P).homology n

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The whole ORIGINAL inclusion map commutes after the same exact scalar change. -/
theorem originalRegularThreeNativeChainIso_inclusion :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (originalRegularThreeShortComplex X x P).f ≫
          (originalRegularThreeNativeAmbientChainIso X x P).hom =
        (originalRegularThreeNativeOldChainIso X x P).hom ≫
          SSet.chainComplexMap (nativeThreePair X x P).hom
              (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let m := (originalRegularThreeShortComplex X x P).f
  let a := originalRegularThreeNativeOldModuleChainIso X x P
  let b := originalRegularThreeNativeAmbientModuleChainIso X x P
  let i := (nativeThreePair X x P).hom
  let e := SSet.mapChainComplexFunctorIso U R
  have h0 : F.map m ≫ F.map b.hom = F.map a.hom ≫ F.map (SSet.chainComplexMap i R) :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map (originalRegularThreeNativeModule_inclusion X x P)).trans (F.map_comp _ _))
  have h1 : F.map (SSet.chainComplexMap i R) ≫ e.hom.app (nativeThreeCover X x P) =
      e.hom.app (nativeThreeOldPullback X x P) ≫
        SSet.chainComplexMap i (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
            e.hom.naturality i
  change F.map m ≫ (F.map b.hom ≫ e.hom.app _) =
    (F.map a.hom ≫ e.hom.app _) ≫ SSet.chainComplexMap i _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ e.hom.app _) h0).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => F.map a.hom ≫ f) h1).trans (Category.assoc _ _ _).symm)))

private def originalRegularThreeNativeShortComplexIso :
    (originalRegularThreeShortComplex X x P).map
      ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)) ≅
        (nativeThreePair X x P).chainComplexShortComplex
            (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  ShortComplex.isoMk (originalRegularThreeNativeOldChainIso X x P)
    (originalRegularThreeNativeAmbientChainIso X x P) (originalRegularThreeNativeChainIso X x P)
    (originalRegularThreeNativeChainIso_inclusion X x P).symm
    (originalRegularThreeNativeChainIso_projection X x P).symm

/-- The old source homology retains the exact original regular-coefficient pullback. -/
def originalRegularThreeNativeOldHomologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj
      ((originalRegularThreeShortComplex X x P).X₁.homology n) ≅
        (nativeThreeOldPullback X x P).homology
            (singularIntegralCoefficients : AddCommGrpCat.{u}) n := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let K := (originalRegularThreeShortComplex X x P).X₁
  exact ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n U).app K).symm ≪≫
    HomologicalComplex.homologyMapIso (originalRegularThreeNativeOldChainIso X x P) n

/-- The actual regular relative homology Iso uses the existing exact forgetful homology
comparison. -/
def originalRegularThreeNativeHomologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj (originalRegularThreeHomology X x P n) ≅
      (nativeThreePair X x P).homology (singularIntegralCoefficients : AddCommGrpCat.{u}) n := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let K := originalRegularThreeChains X x P
  exact ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n U).app K).symm ≪≫
    HomologicalComplex.homologyMapIso (originalRegularThreeNativeChainIso X x P) n

/-- The ORIGINAL regular relative homology identifies with the SAME upstairs three-cell homology, in
every degree. -/
def originalRegularThreeUpstairsHomologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj (originalRegularThreeHomology X x P n) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) n).obj (upstairsThreePair X x P) :=
  originalRegularThreeNativeHomologyIso X x P n ≪≫
    (relativeThreeHomologyIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) n).symm


/-- The old original regular absolute chains retain their unchanged native two-cover coordinate. -/
def originalRegularTwoNativeAmbientModuleChainIso :
    TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
      (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))) ≅
        (LoopCellSphericalGenerators.nativeCover X x P).chainComplex
            (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let y := LoopCellAttachment.inclusion X x P x
  let h := nativeTargetPoint_eq_original X x P
  exact TopCat.originalTopRegularCoverChainIso (originalTwo X x P) y ≪≫
    eqToIso (congrArg (fun z : (TopCat.toSSet.obj (originalTwo X x P)) _⦋0⦌ =>
      (SSet.KanComplex.nativeCover (TopCat.toSSet.obj (originalTwo X x P)) z).chainComplex
        (ModuleCat.of ℤ (ULift.{u} ℤ))) h.symm)

/-- The old coefficient return is computed through the same actual native
base-change inverse and the unchanged original regular two-cover comparison. -/
def originalRegularThreeOldCoefficientAddChainIso :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (originalRegularThreeShortComplex X x P).X₁ ≅
        ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)))) := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let C := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  exact originalRegularThreeNativeOldChainIso X x P ≪≫
    (C.mapIso (nativeTwoToThreePullbackIso X x P)).symm ≪≫
      (originalRegularNativeAmbientChainIso X x P).symm

/-- The original old coefficient return uses the SAME inclusion-induced
native base-change Iso and the two original regular chain comparisons. -/
def originalRegularThreeOldCoefficientChainIso :
    (originalRegularThreeShortComplex X x P).X₁ ≅
      TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
        (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  exact F.preimageIso (originalRegularThreeOldCoefficientAddChainIso X x P)

/-- Exact integer-module lifting preserves the entire computed old coefficient map. -/
theorem originalRegularThreeOldCoefficientChainIso_map :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (originalRegularThreeOldCoefficientChainIso X x P).hom =
        (originalRegularThreeOldCoefficientAddChainIso X x P).hom := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let e := originalRegularThreeOldCoefficientAddChainIso X x P
  change F.map (F.preimage e.hom) = e.hom
  exact F.map_preimage e.hom

/-- The whole old chain return uses the SAME original two-cover comparison and actual base-change
inverse. -/
theorem originalRegularThreeOldCoefficientChainIso_native :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (originalRegularThreeOldCoefficientChainIso X x P).hom ≫
          (originalRegularNativeAmbientChainIso X x P).hom =
        (originalRegularThreeNativeOldChainIso X x P).hom ≫
          ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
            (singularIntegralCoefficients : AddCommGrpCat.{u})).map
                (nativeTwoToThreePullbackIso X x P).inv := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let C := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  let a := originalRegularThreeNativeOldChainIso X x P
  let b := C.mapIso (nativeTwoToThreePullbackIso X x P)
  let c := originalRegularNativeAmbientChainIso X x P
  rw [originalRegularThreeOldCoefficientChainIso_map]
  change (a.hom ≫ (b.inv ≫ c.inv)) ≫ c.hom = a.hom ≫ b.inv
  exact (Category.assoc a.hom (b.inv ≫ c.inv) c.hom).trans
    ((congrArg (fun k => a.hom ≫ k) (Category.assoc b.inv c.inv c.hom)).trans
      ((congrArg (fun k => a.hom ≫ b.inv ≫ k) c.inv_hom_id).trans
        (congrArg (fun k => a.hom ≫ k) (Category.comp_id b.inv))))

/-- The actual ORIGINAL three-to-two boundary starts with its original
relative LES connecting map, then the computed old coefficient return and
unchanged original two-cell relative quotient. -/
def originalRegularThreeToTwoBoundary : originalRegularThreeHomology X x P 3 ⟶
    originalRegularHomologyTwo X x P :=
  (originalRegularThreeShortExact X x P).δ 3 2 (by simp) ≫
    HomologicalComplex.homologyMap (originalRegularThreeOldCoefficientChainIso X x P).hom 2 ≫
      HomologicalComplex.homologyMap
        (TopCat.originalRegularRelativeChainProjection (LoopCellAttachment.inclusion X x P)
          (LoopCellAttachment.inclusion X x P x)) 2


omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The SAME ORIGINAL module-valued LES connecting map commutes with the
native relative comparison, using the proved exact-functor connecting law. -/
theorem originalRegularThreeNativeHomologyIso_boundary :
    (originalRegularThreeNativeHomologyIso X x P 3).hom ≫
      nativeThreeRelativeBoundary X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) =
        (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
          ((originalRegularThreeShortExact X x P).δ 3 2 (by simp)) ≫
            (originalRegularThreeNativeOldHomologyIso X x P 2).hom := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let S := originalRegularThreeShortComplex X x P
  let hS := originalRegularThreeShortExact X x P
  let T := S.map F
  let hT : T.ShortExact := hS.map_of_exact F
  let e := originalRegularThreeNativeShortComplexIso X x P
  let B := (nativeThreePair X x P).chainComplexShortComplex
      (singularIntegralCoefficients : AddCommGrpCat.{u})
  let hB := (nativeThreePair X x P).shortExact_chainComplexShortComplex
      (singularIntegralCoefficients : AddCommGrpCat.{u})
  let e3 := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 3 U).app S.X₃
  let e1 := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 2 U).app S.X₁
  let a := HomologicalComplex.homologyMap (originalRegularThreeNativeOldChainIso X x P).hom 2
  let b := HomologicalComplex.homologyMap (originalRegularThreeNativeChainIso X x P).hom 3
  have hN : b ≫ hB.δ 3 2 (by simp) = hT.δ 3 2 (by simp) ≫ a :=
    (HomologicalComplex.HomologySequence.δ_naturality e.hom hT hB 3 2 (by simp)).symm
  have hF : e3.inv ≫ hT.δ 3 2 (by simp) ≫ e1.hom = U.map (hS.δ 3 2 (by simp)) :=
    CategoryTheory.ShortComplex.ShortExact.delta_mapFunctor hS U 3 2 (by simp)
  have hFc : e3.inv ≫ hT.δ 3 2 (by simp) = U.map (hS.δ 3 2 (by simp)) ≫ e1.inv := by
    apply (cancel_mono e1.hom).mp
    exact hF.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => U.map (hS.δ 3 2 (by simp)) ≫ f) e1.inv_hom_id).trans
            (Category.comp_id _))).symm
  change (e3.inv ≫ b) ≫ hB.δ 3 2 (by simp) = U.map (hS.δ 3 2 (by simp)) ≫ (e1.inv ≫ a)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => e3.inv ≫ f) hN).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ a) hFc).trans (Category.assoc _ _ _))))


omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
/-- The existing Nat-to-Int comparison identifies the SAME chosen-sphere
boundary with the actual original natural-degree LES connecting morphism. -/
theorem actualThreeRelativeBoundary_eq_nat : actualThreeRelativeBoundary X x P =
    (relativeSingularBoundary AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app
      (upstairsThreePair X x P) ≫ LoopCellSphericalGenerators.relativeProjection X x P := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let A := upstairsThreePair X x P
  let e3 := (relativeSingularHomologyNatToIntIso AddCommGrpCat.{u} R 3).app A
  let e2 := (singularHomologyNatToIntIso AddCommGrpCat.{u} R 2).app A.snd
  let b := (relativeSingularBoundary AddCommGrpCat.{u} R 2).app A
  let q := LoopCellSphericalGenerators.relativeProjection X x P
  have hB : (singularHomologyIntData AddCommGrpCat.{u} R).boundary 3 A = e3.hom ≫ b ≫ e2.inv :=
    (singularHomologyIntData_boundary AddCommGrpCat.{u} R 3 A).trans
      (relativeSingularBoundaryIntRel_natAgreement AddCommGrpCat.{u} R 2 A)
  change e3.inv ≫ (singularHomologyIntData AddCommGrpCat.{u} R).boundary 3 A ≫ e2.hom ≫ q = b ≫ q
  have hB0 : e3.inv ≫ (singularHomologyIntData AddCommGrpCat.{u} R).boundary 3 A = b ≫ e2.inv :=
    (congrArg (fun f => e3.inv ≫ f) hB).trans (e3.inv_hom_id_assoc (b ≫ e2.inv))
  exact (Category.assoc e3.inv ((singularHomologyIntData AddCommGrpCat.{u} R).boundary 3 A)
      (e2.hom ≫ q)).symm.trans
    ((congrArg (fun f => f ≫ (e2.hom ≫ q)) hB0).trans
      ((Category.assoc b e2.inv (e2.hom ≫ q)).trans
        (congrArg (fun f => b ≫ f) (e2.inv_hom_id_assoc q))))

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X] [P.Normal]
    [Group.IsPerfect P] in
/-- The actual old singular comparison and original realization unit are
inverse on homology, using its whole unit identity and existing unit homology Iso. -/
theorem oldSingularToNative_homology_unit (n : ℕ) :
    SSet.homologyMap (oldSingularToNative X x P)
        (singularIntegralCoefficients : AddCommGrpCat.{u}) n ≫
      (SSet.realizationSingularHomologyIso (singularIntegralCoefficients : AddCommGrpCat.{u})
        (LoopCellSphericalGenerators.nativeCover X x P) n).hom = 𝟙 _ := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let E := LoopCellSphericalGenerators.nativeCover X x P
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n
  let C := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  let u := sSetTopAdj.unit.app E
  let l := oldSingularToNative X x P
  let e := SSet.realizationSingularHomologyIso R E n
  let a := SSet.homologyMap l R n
  have hL : e.hom ≫ a = 𝟙 _ :=
    (SSet.homologyMap_comp E (TopCat.toSSet.obj (SSet.toTop.obj E)) E u l R n).symm.trans
      ((congrArg (fun f => SSet.homologyMap f R n) (oldSingularToNative_unit X x P)).trans
        (SSet.homologyMap_id E R n))
  apply (cancel_epi e.hom).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ e.hom) hL).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- The old pullback return, followed by the original unit, is the whole
homology identity on the actual old upstairs singular space. -/
theorem oldSingularToThreePullback_homology_return (n : ℕ) :
    SSet.homologyMap (oldSingularToThreePullback X x P)
        (singularIntegralCoefficients : AddCommGrpCat.{u}) n ≫
      SSet.homologyMap (nativeTwoToThreePullbackIso X x P).inv
        (singularIntegralCoefficients : AddCommGrpCat.{u}) n ≫
          (SSet.realizationSingularHomologyIso (singularIntegralCoefficients : AddCommGrpCat.{u})
            (LoopCellSphericalGenerators.nativeCover X x P) n).hom = 𝟙 _ := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let l := oldSingularToNative X x P
  let c := nativeTwoToThreePullbackIso X x P
  have hC : oldSingularToThreePullback X x P ≫ c.inv = l :=
    (congrArg (fun f => (l ≫ f) ≫ c.inv) (nativeTwoToThreePullbackIso_hom X x P).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => l ≫ f) c.hom_inv_id).trans (Category.comp_id _)))
  have hH : SSet.homologyMap (oldSingularToThreePullback X x P) R n ≫ SSet.homologyMap c.inv R n =
      SSet.homologyMap l R n :=
    (SSet.homologyMap_comp
      (TopCat.toSSet.obj (SSet.toTop.obj (LoopCellSphericalGenerators.nativeCover X x P)))
      (nativeThreeOldPullback X x P) (LoopCellSphericalGenerators.nativeCover X x P)
      (oldSingularToThreePullback X x P) c.inv R n).symm.trans
        (congrArg (fun f => SSet.homologyMap f R n) hC)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (SSet.realizationSingularHomologyIso R
      (LoopCellSphericalGenerators.nativeCover X x P) n).hom) hH).trans
        (oldSingularToNative_homology_unit X x P n))

/-- The native three-to-two map is its actual relative LES connecting map,
followed by the SAME old base-change inverse, unit and original old-pair quotient. -/
def nativeThreeToTwoBoundary : (nativeThreePair X x P).homology
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 3 ⟶
      nativeHomologyTwo X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  nativeThreeRelativeBoundary X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) ≫
    SSet.homologyMap (nativeTwoToThreePullbackIso X x P).inv
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2 ≫
        (SSet.realizationSingularHomologyIso (singularIntegralCoefficients : AddCommGrpCat.{u})
          (LoopCellSphericalGenerators.nativeCover X x P) 2).hom ≫
            LoopCellSphericalGenerators.relativeProjection X x P

/-- The entire native boundary is its SAME actual pair connecting map,
typed mapped-Cartesian inverse, original pair quotient and original unit
return. This is a whole map characteristic, for every original class. -/
theorem nativeThreeToTwoBoundary_recipe :
    let R : AddCommGrpCat.{u} := singularIntegralCoefficients
    let C := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
    let A := LoopCellPulledSimplicialModel.nativePair X x P
    let B := nativeThreePair X x P
    let c : A.right.chainComplex R ≅ B.left.chainComplex R :=
      C.mapIso (nativeTwoToThreePullbackIso X x P)
    let U : (A.chainComplex R).homology 2 ≅ nativeHomologyTwo X x P R :=
      nativeRelativeUnitHomologyIso X x P R 2
    nativeThreeToTwoBoundary X x P =
      (B.shortExact_chainComplexShortComplex R).δ 3 2 (by simp) ≫
        HomologicalComplex.homologyMap c.inv 2 ≫
          HomologicalComplex.homologyMap (A.chainComplexπ R) 2 ≫ U.hom := by
  dsimp only
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let C := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  let A := LoopCellPulledSimplicialModel.nativePair X x P
  let B := nativeThreePair X x P
  let d := (B.shortExact_chainComplexShortComplex R).δ 3 2 (by simp)
  let b := SSet.homologyMap (nativeTwoToThreePullbackIso X x P).inv R 2
  have hU : HomologicalComplex.homologyMap (A.chainComplexπ R) 2 ≫
      (nativeRelativeUnitHomologyIso X x P R 2).hom =
    SSet.homologyMap (sSetTopAdj.unit.app (LoopCellSphericalGenerators.nativeCover X x P)) R 2 ≫
      LoopCellSphericalGenerators.relativeProjection X x P :=
    nativeRelativeUnitHomologyIso_projection X x P R 2
  unfold nativeThreeToTwoBoundary nativeThreeRelativeBoundary
  rw [SSet.realizationSingularHomologyIso_hom]
  exact (congrArg (fun k => d ≫ (b ≫ k)) hU).symm

/-- The entire same-sphere boundary, with every integer/quotient/P column,
is carried to the actual native three-to-two map, using the ORIGINAL LES square. -/
theorem relativeThreeHomologyIso_threeToTwo :
    (relativeThreeHomologyIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).hom ≫
      nativeThreeToTwoBoundary X x P = actualThreeRelativeBoundary X x P := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let e := (relativeThreeHomologyIso X x P R 3).hom
  let b := nativeThreeRelativeBoundary X x P R
  let c := SSet.homologyMap (nativeTwoToThreePullbackIso X x P).inv R 2
  let u :=
      (SSet.realizationSingularHomologyIso R (LoopCellSphericalGenerators.nativeCover X x P) 2).hom
  let q := LoopCellSphericalGenerators.relativeProjection X x P
  let d := (relativeSingularBoundary AddCommGrpCat.{u} R 2).app (upstairsThreePair X x P)
  let a := SSet.homologyMap (oldSingularToThreePullback X x P) R 2
  have hN : e ≫ b = d ≫ a := relativeThreeHomologyIso_boundary X x P R
  have hU : a ≫ c ≫ u = 𝟙 _ := oldSingularToThreePullback_homology_return X x P 2
  change e ≫ (b ≫ (c ≫ (u ≫ q))) = actualThreeRelativeBoundary X x P
  have hAll : e ≫ (b ≫ (c ≫ (u ≫ q))) = d ≫ q := by
    have hInner : (a ≫ (c ≫ u)) ≫ q = q :=
      (congrArg (fun f => f ≫ q) hU).trans (Category.id_comp q)
    have hSuffix : a ≫ (c ≫ (u ≫ q)) = q :=
      (congrArg (fun f => a ≫ f) (Category.assoc c u q).symm).trans
        ((Category.assoc a (c ≫ u) q).symm.trans hInner)
    exact (Category.assoc e b (c ≫ (u ≫ q))).symm.trans
      ((congrArg (fun f => f ≫ (c ≫ (u ≫ q))) hN).trans
        ((Category.assoc d a (c ≫ (u ≫ q))).trans
          (congrArg (fun f => d ≫ f) hSuffix)))
  exact hAll.trans (actualThreeRelativeBoundary_eq_nat X x P).symm

/-- The original old coefficient return agrees on whole homology with its
actual native base-change return, including the original realization unit. -/
theorem originalRegularThreeOldCoefficientHomology_native :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap (originalRegularThreeOldCoefficientChainIso X x P).hom 2) ≫
        (originalRegularNativeAmbientHomologyIso X x P).hom =
      (originalRegularThreeNativeOldHomologyIso X x P 2).hom ≫
        SSet.homologyMap (nativeTwoToThreePullbackIso X x P).inv
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2 ≫
            (SSet.realizationSingularHomologyIso (singularIntegralCoefficients : AddCommGrpCat.{u})
              (LoopCellSphericalGenerators.nativeCover X x P) 2).hom := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 2
  let K := (originalRegularThreeShortComplex X x P).X₁
  let L := TopCat.localCoefficientChainComplex (CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)))
  let a := (originalRegularThreeOldCoefficientChainIso X x P).hom
  let η := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 2 U
  let b := (originalRegularNativeAmbientChainIso X x P).hom
  let c := (originalRegularThreeNativeOldChainIso X x P).hom
  let d := ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj
    (singularIntegralCoefficients : AddCommGrpCat.{u})).map (nativeTwoToThreePullbackIso X x P).inv
  let u := (SSet.realizationSingularHomologyIso (singularIntegralCoefficients : AddCommGrpCat.{u})
    (LoopCellSphericalGenerators.nativeCover X x P) 2).hom
  have hN : U.map (HomologicalComplex.homologyMap a 2) ≫ η.inv.app L =
      η.inv.app K ≫ H.map (F.map a) := η.inv.naturality a
  have hC : H.map (F.map a) ≫ H.map b = H.map c ≫ H.map d :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (originalRegularThreeOldCoefficientChainIso_native X x P)).trans
          (H.map_comp _ _))
  change U.map (HomologicalComplex.homologyMap a 2) ≫ (η.inv.app L ≫ (H.map b ≫ u)) =
    (η.inv.app K ≫ H.map c) ≫ (H.map d ≫ u)
  have hAll : U.map (HomologicalComplex.homologyMap a 2) ≫ (η.inv.app L ≫ H.map b) =
      η.inv.app K ≫ (H.map c ≫ H.map d) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ H.map b) hN).trans
        ((Category.assoc _ _ _).trans (congrArg (fun f => η.inv.app K ≫ f) hC)))
  exact (congrArg (fun k => U.map (HomologicalComplex.homologyMap a 2) ≫ k)
      (Category.assoc (η.inv.app L) (H.map b) u).symm).trans
    ((Category.assoc (U.map (HomologicalComplex.homologyMap a 2))
        (η.inv.app L ≫ H.map b) u).symm.trans
      ((congrArg (fun k => k ≫ u) hAll).trans
        ((Category.assoc (η.inv.app K) (H.map c ≫ H.map d) u).trans
          ((congrArg (fun k => η.inv.app K ≫ k) (Category.assoc (H.map c) (H.map d) u)).trans
            (Category.assoc (η.inv.app K) (H.map c) (H.map d ≫ u)).symm))))

/-- The whole ORIGINAL module-valued three-to-two LES map is carried to the
actual native map; neither quotient nor connecting morphism is replaced. -/
theorem originalRegularThreeToTwoBoundary_native :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map (originalRegularThreeToTwoBoundary X x P) ≫
      (originalRegularNativeHomologyIso X x P).hom =
        (originalRegularThreeNativeHomologyIso X x P 3).hom ≫ nativeThreeToTwoBoundary X x P := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let b := (originalRegularThreeShortExact X x P).δ 3 2 (by simp)
  let c := HomologicalComplex.homologyMap (originalRegularThreeOldCoefficientChainIso X x P).hom 2
  let q := HomologicalComplex.homologyMap
    (TopCat.originalRegularRelativeChainProjection (LoopCellAttachment.inclusion X x P)
      (LoopCellAttachment.inclusion X x P x)) 2
  let e2 := (originalRegularNativeHomologyIso X x P).hom
  let a2 := (originalRegularNativeAmbientHomologyIso X x P).hom
  let a3 := (originalRegularThreeNativeOldHomologyIso X x P 2).hom
  let e3 := (originalRegularThreeNativeHomologyIso X x P 3).hom
  let d3 := nativeThreeRelativeBoundary X x P (singularIntegralCoefficients : AddCommGrpCat.{u})
  let d := SSet.homologyMap (nativeTwoToThreePullbackIso X x P).inv
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2
  let u := (SSet.realizationSingularHomologyIso (singularIntegralCoefficients : AddCommGrpCat.{u})
    (LoopCellSphericalGenerators.nativeCover X x P) 2).hom
  let p := LoopCellSphericalGenerators.relativeProjection X x P
  have hQ : U.map q ≫ e2 = a2 ≫ p := originalRegularNativeHomologyIso_projection X x P
  have hC : U.map c ≫ a2 = a3 ≫ d ≫ u := originalRegularThreeOldCoefficientHomology_native X x P
  have hB : U.map b ≫ a3 = e3 ≫ d3 := (originalRegularThreeNativeHomologyIso_boundary X x P).symm
  change U.map (b ≫ (c ≫ q)) ≫ e2 = e3 ≫ (d3 ≫ (d ≫ (u ≫ p)))
  rw [U.map_comp, U.map_comp]
  have h1 : (U.map b ≫ (U.map c ≫ U.map q)) ≫ e2 = U.map b ≫ (U.map c ≫ (a2 ≫ p)) := by
    simpa only [Category.assoc] using congrArg (fun f => U.map b ≫ (U.map c ≫ f)) hQ
  have h2 : U.map b ≫ (U.map c ≫ (a2 ≫ p)) = (U.map b ≫ a3) ≫ (d ≫ (u ≫ p)) := by
    exact (congrArg (fun k => U.map b ≫ k) (Category.assoc (U.map c) a2 p).symm).trans
      ((congrArg (fun k => U.map b ≫ (k ≫ p)) hC).trans
        ((congrArg (fun k => U.map b ≫ k) (Category.assoc a3 (d ≫ u) p)).trans
          ((congrArg (fun k => U.map b ≫ a3 ≫ k) (Category.assoc d u p)).trans
            (Category.assoc (U.map b) a3 (d ≫ (u ≫ p))).symm)))
  exact h1.trans (h2.trans
    ((congrArg (fun f => f ≫ (d ≫ (u ≫ p))) hB).trans (Category.assoc _ _ _)))

/-- The full ORIGINAL RR3 boundary agrees with the same upstairs boundary,
including every chosen sphere and actual original RR2 quotient. -/
theorem originalRegularThreeToTwoBoundary_upstairs :
    (originalRegularThreeUpstairsHomologyIso X x P 3).hom ≫ actualThreeRelativeBoundary X x P =
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map (originalRegularThreeToTwoBoundary X x P) ≫
        (originalRegularNativeHomologyIso X x P).hom := by
  let e := relativeThreeHomologyIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) 3
  let a := originalRegularThreeNativeHomologyIso X x P 3
  have h := relativeThreeHomologyIso_threeToTwo X x P
  have hInv : e.inv ≫ actualThreeRelativeBoundary X x P = nativeThreeToTwoBoundary X x P := by
    apply (cancel_epi e.hom).mp
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ actualThreeRelativeBoundary X x P) e.hom_inv_id).trans
        ((Category.id_comp _).trans h.symm))
  change (a.hom ≫ e.inv) ≫ actualThreeRelativeBoundary X x P = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => a.hom ≫ f) hInv).trans
        (originalRegularThreeToTwoBoundary_native X x P).symm)


/-- The original quotient index is carried to the literal original singular
basepoint by its proved point equation, retaining the same loop orientation. -/
def originalThreeQuotientDeckIndex : FundamentalGroup X x ⧸ P ≃*
    End
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm
          (originalThreeBasePoint X x P))) :=
  (quotientThreeDeckIndex X x P).trans
    ((eqToIso (congrArg SSet.FundamentalGroupoid.mk (nativeThreePoint_eq_original X x P))).conj)

/-- This action on ORIGINAL relative chains is the actual inverse-precomposition
regular coefficient action on the unchanged original quotient. -/
def originalRegularThreeDeckChainMap (q : FundamentalGroup X x ⧸ P) :
    originalRegularThreeChains X x P ⟶ originalRegularThreeChains X x P :=
  TopCat.originalRegularRelativeDeckChainMap (originalThreeInclusion X x P)
    (originalThreeBasePoint X x P) (originalThreeQuotientDeckIndex X x P q)

/-- Its degree-three homology map is induced by that SAME original chain action. -/
def originalRegularThreeDeckHomologyMap (q : FundamentalGroup X x ⧸ P) :
    originalRegularThreeHomology X x P 3 ⟶ originalRegularThreeHomology X x P 3 :=
  HomologicalComplex.homologyMap (originalRegularThreeDeckChainMap X x P q) 3

/-- The actual paired native deck map uses the unchanged old pullback leg
and ambient cover map, with the original inclusion-induced quotient index. -/
def nativeThreeDeckPair (q : FundamentalGroup X x ⧸ P) : nativeThreePair X x P ⟶
    nativeThreePair X x P :=
  SSetPair.ofHom (SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P q))
    (SSet.KanComplex.nativeRegularPullbackDeckMap (TopCat.toSSet.map (originalThreeInclusion X x P))
      (nativeThreePoint X x P) (quotientThreeDeckIndex X x P q))
    (SSet.KanComplex.nativeRegularPullbackDeckMap_snd
        (TopCat.toSSet.map (originalThreeInclusion X x P))
      (nativeThreePoint X x P) (quotientThreeDeckIndex X x P q))

private theorem pairedDeck_equals_nativeThree (q : FundamentalGroup X x ⧸ P) :
    OriginalNativeRelativeBasis.pairedDeckAtVertex
        (TopCat.toSSet.map (originalThreeInclusion X x P))
      (nativeThreePoint X x P) (quotientThreeDeckIndex X x P q) = nativeThreeDeckPair X x P q := by
  apply MorphismProperty.Arrow.Hom.ext
  · rfl
  · rfl

/-- The original paired coefficient action is carried to the SAME actual
native paired action through the original point equation. -/
theorem originalRegularThreeDeckPair_to_native (q : FundamentalGroup X x ⧸ P) :
    letI : Mono (originalThreeInclusion X x P) := (TopCat.mono_iff_injective _).mpr
      (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
        (LoopCellSphericalGenerators.sphericalGenerator X x P))
    TopCat.originalRegularNativeDeckPair (originalThreeInclusion X x P)
        (originalThreeBasePoint X x P)
        (originalThreeQuotientDeckIndex X x P q) ≫
            (eqToIso (originalRegularThreePair_eq_native X x P)).hom =
      (eqToIso (originalRegularThreePair_eq_native X x P)).hom ≫ nativeThreeDeckPair X x P q := by
  let f := originalThreeInclusion X x P
  let sf := TopCat.toSSet.map f
  let : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let : Mono sf := inferInstance
  let z := nativeThreePoint X x P
  let y := TopCat.toSSetObj₀Equiv.symm (originalThreeBasePoint X x P)
  let h : z = y := nativeThreePoint_eq_original X x P
  let a := quotientThreeDeckIndex X x P q
  let e := eqToIso (congrArg (OriginalNativeRelativeBasis.pairedCoverAtVertex sf) h)
  let dZ := OriginalNativeRelativeBasis.pairedDeckAtVertex sf z a
  let dY := OriginalNativeRelativeBasis.pairedDeckAtVertex sf y
      (originalThreeQuotientDeckIndex X x P q)
  have hF : dZ ≫ e.hom = e.hom ≫ dY := OriginalNativeRelativeBasis.pairedDeck_point_transport sf h a
  have hInv : dY ≫ e.inv = e.inv ≫ dZ := by
    apply (cancel_mono e.hom).mp
    have hL : (dY ≫ e.inv) ≫ e.hom = dY :=
      (Category.assoc dY e.inv e.hom).trans
        ((congrArg (fun k => dY ≫ k) e.inv_hom_id).trans (Category.comp_id dY))
    have hR : (e.inv ≫ dZ) ≫ e.hom = dY :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => e.inv ≫ k) hF).trans (e.inv_hom_id_assoc dY))
    exact hL.trans hR.symm
  have hY := originalDeckPair_equals_atVertex f (originalThreeBasePoint X x P)
      (originalThreeQuotientDeckIndex X x P q)
  have hZ := pairedDeck_equals_nativeThree X x P q
  have hCast : e.inv = (eqToIso (originalRegularThreePair_eq_native X x P)).hom := by rfl
  exact (congrArg (fun d => d ≫ (eqToIso (originalRegularThreePair_eq_native X x P)).hom) hY).trans
    ((congrArg (fun k => dY ≫ k) hCast.symm).trans
      (hInv.trans ((congrArg (fun d => e.inv ≫ d) hZ).trans
        (congrArg (fun k => k ≫ nativeThreeDeckPair X x P q) hCast))))

/-- The whole original MODULE relative-chain comparison preserves the
actual regular action, not an action supplied or defined by a basis. -/
theorem originalRegularThreeNativeModule_deck (q : FundamentalGroup X x ⧸ P) :
    originalRegularThreeDeckChainMap X x P q ≫
        (originalRegularThreeNativeRelativeModuleChainIso X x P).hom =
      (originalRegularThreeNativeRelativeModuleChainIso X x P).hom ≫
        SSetPair.chainComplexMap (nativeThreeDeckPair X x P q) (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let f := originalThreeInclusion X x P
  let y := originalThreeBasePoint X x P
  let : Mono f := (TopCat.mono_iff_injective f).mpr
    (CellFamilyAttachment.inclusion_injective (originalTwo X x P) 2
      (LoopCellSphericalGenerators.sphericalGenerator X x P))
  let A := TopCat.originalRegularPulledCoverPair f y
  let B := nativeThreePair X x P
  let h : A = B := originalRegularThreePair_eq_native X x P
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let F := (SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj R
  let e := TopCat.originalRegularRelativeChainIso f y
  let t := eqToIso (congrArg (fun A : SSetPair.{u} => A.chainComplex R) h)
  let dA := TopCat.originalRegularNativeDeckPair f y (originalThreeQuotientDeckIndex X x P q)
  let dB := nativeThreeDeckPair X x P q
  have h0 : originalRegularThreeDeckChainMap X x P q ≫ e.hom = e.hom ≫ F.map dA :=
    TopCat.originalRegularRelativeChainIso_deck f y (originalThreeQuotientDeckIndex X x P q)
  have h1 : F.map dA ≫ t.hom = t.hom ≫ F.map dB := by
    have hPair := originalRegularThreeDeckPair_to_native X x P q
    have hMap := (F.map_comp dA (eqToIso h).hom).symm.trans
      ((congrArg F.map hPair).trans (F.map_comp (eqToIso h).hom dB))
    have hTag : F.map (eqToIso h).hom = t.hom := CategoryTheory.eqToHom_map F h
    exact (congrArg (fun k => F.map dA ≫ k) hTag.symm).trans
      (hMap.trans (congrArg (fun k => k ≫ F.map dB) hTag))
  change originalRegularThreeDeckChainMap X x P q ≫ (e.hom ≫ t.hom) =
    (e.hom ≫ t.hom) ≫ F.map dB
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ t.hom) h0).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun k => e.hom ≫ k) h1).trans
          (Category.assoc _ _ _).symm)))

/-- Scalar-category change also preserves that entire SAME original regular action. -/
theorem originalRegularThreeNativeChainIso_deck (q : FundamentalGroup X x ⧸ P) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (originalRegularThreeDeckChainMap X x P q) ≫ (originalRegularThreeNativeChainIso X x P).hom =
        (originalRegularThreeNativeChainIso X x P).hom ≫
          SSetPair.chainComplexMap (nativeThreeDeckPair X x P q)
              (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let a := originalRegularThreeDeckChainMap X x P q
  let e := originalRegularThreeNativeRelativeModuleChainIso X x P
  let b := OriginalNativeRelativeBasis.forgetRelativeChainIso (nativeThreePair X x P)
  let dM := SSetPair.chainComplexMap (nativeThreeDeckPair X x P q) (ModuleCat.of ℤ (ULift.{u} ℤ))
  let dA := SSetPair.chainComplexMap (nativeThreeDeckPair X x P q)
      (singularIntegralCoefficients : AddCommGrpCat.{u})
  have h0 : F.map a ≫ F.map e.hom = F.map e.hom ≫ F.map dM :=
    (F.map_comp _ _).symm.trans
        ((congrArg F.map (originalRegularThreeNativeModule_deck X x P q)).trans (F.map_comp _ _))
  have h1 : F.map dM ≫ b.hom = b.hom ≫ dA :=
    OriginalNativeRelativeBasis.forgetRelativeChainIso_naturality (nativeThreeDeckPair X x P q)
  change F.map a ≫ (F.map e.hom ≫ b.hom) = (F.map e.hom ≫ b.hom) ≫ dA
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ b.hom) h0).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun k => F.map e.hom ≫ k) h1).trans
          (Category.assoc _ _ _).symm)))

/-- The actual original regular homology action is preserved on every element of RR3. -/
theorem originalRegularThreeNativeHomologyIso_deck (q : FundamentalGroup X x ⧸ P) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
        (originalRegularThreeDeckHomologyMap X x P q) ≫
      (originalRegularThreeNativeHomologyIso X x P 3).hom =
        (originalRegularThreeNativeHomologyIso X x P 3).hom ≫
          SSetPair.homologyMap (nativeThreeDeckPair X x P q)
              (singularIntegralCoefficients : AddCommGrpCat.{u}) 3 := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 3
  let a := originalRegularThreeDeckChainMap X x P q
  let e := (originalRegularThreeNativeChainIso X x P).hom
  let η := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 3 U
  let K := originalRegularThreeChains X x P
  have hN : U.map (HomologicalComplex.homologyMap a 3) ≫ η.inv.app K = η.inv.app K ≫
      H.map (F.map a) := η.inv.naturality a
  have hE : H.map (F.map a) ≫ H.map e = H.map e ≫
      SSetPair.homologyMap (nativeThreeDeckPair X x P q)
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 3 :=
    (H.map_comp _ _).symm.trans
        ((congrArg H.map (originalRegularThreeNativeChainIso_deck X x P q)).trans (H.map_comp _ _))
  change U.map (originalRegularThreeDeckHomologyMap X x P q) ≫ (η.inv.app K ≫ H.map e) =
    (η.inv.app K ≫ H.map e) ≫ SSetPair.homologyMap (nativeThreeDeckPair X x P q) _ 3
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ H.map e) hN).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun k => η.inv.app K ≫ k) hE).trans
          (Category.assoc _ _ _).symm)))

section RelativeDeckCoefficients

variable {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]

/-- The whole relative comparison is equivariant for EVERY coefficient object,
using the original quotients and entire same ambient deck square. -/
theorem relativeThreeChainMap_deck (R : C) (q : FundamentalGroup X x ⧸ P) :
    (relativeSingularChainFunctor C R).map (upstairsThreeDeckPair X x P q) ≫
        relativeThreeChainMap X x P R =
      relativeThreeChainMap X x P R ≫ SSetPair.chainComplexMap (nativeThreeDeckPair X x P q) R := by
  let Q := relativeSingularChainQuotient C R (upstairsThreePair X x P)
  let qN := (nativeThreePair X x P).chainComplexπ R
  let F := (SSet.chainComplexFunctor C).obj R
  let dS := (relativeSingularChainFunctor C R).map (upstairsThreeDeckPair X x P q)
  let dN := SSetPair.chainComplexMap (nativeThreeDeckPair X x P q) R
  let a := F.map (TopCat.toSSet.map (upstairsThreeDeck X x P q))
  let b := F.map (SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P q))
  let c := F.map (singularUpstairsThreeToNative X x P)
  let r := relativeThreeChainMap X x P R
  have hS : Q ≫ dS = a ≫ Q := relativeSingularChainQuotient_naturality C R
      (upstairsThreeDeckPair X x P q)
  have hN : qN ≫ dN = b ≫ qN :=
    (((SSetPair.chainComplexFunctorπ C).app R).naturality (nativeThreeDeckPair X x P q)).symm
  have hA : a ≫ c = c ≫ b :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (singularUpstairsThreeToNative_deck X x P q)).trans
        (F.map_comp _ _))
  have hQ : Q ≫ r = c ≫ qN := relativeThreeChainMap_projection X x P R
  let : Epi Q := (singularPairShortComplex_shortExact C R (upstairsThreePair X x P)).epi_g
  apply (cancel_epi Q).mp
  have hL : Q ≫ (dS ≫ r) = c ≫ (b ≫ qN) := by
    rw [← Category.assoc Q dS, hS]
    exact (Category.assoc a Q r).trans
      ((congrArg (fun k => a ≫ k) hQ).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ qN) hA).trans (Category.assoc _ _ _))))
  have hR : Q ≫ (r ≫ dN) = c ≫ (b ≫ qN) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ dN) hQ).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => c ≫ k) hN)))
  exact hL.trans hR.symm

/-- Equivariance uses the same actual relative homology maps in every degree. -/
theorem relativeThreeHomologyIso_deck (R : C) (q : FundamentalGroup X x ⧸ P) (n : ℕ) :
    (relativeSingularHomologyFunctor C R n).map (upstairsThreeDeckPair X x P q) ≫
      (relativeThreeHomologyIso X x P R n).hom = (relativeThreeHomologyIso X x P R n).hom ≫
        SSetPair.homologyMap (nativeThreeDeckPair X x P q) R n := by
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n
  rw [relativeThreeHomologyIso_hom]
  change H.map ((relativeSingularChainFunctor C R).map (upstairsThreeDeckPair X x P q)) ≫
      H.map (relativeThreeChainMap X x P R) =
    H.map (relativeThreeChainMap X x P R) ≫
        H.map (SSetPair.chainComplexMap (nativeThreeDeckPair X x P q) R)
  exact (H.map_comp _ _).symm.trans ((congrArg H.map (relativeThreeChainMap_deck X x P R q)).trans
      (H.map_comp _ _))

end RelativeDeckCoefficients

/-- The original regular action is carried to the SAME geometric upstairs
action, on the entire homology group and every quotient label. -/
theorem originalRegularThreeUpstairsHomologyIso_deck (q : FundamentalGroup X x ⧸ P) :
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
        (originalRegularThreeDeckHomologyMap X x P q) ≫
      (originalRegularThreeUpstairsHomologyIso X x P 3).hom =
        (originalRegularThreeUpstairsHomologyIso X x P 3).hom ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{u}
              (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).map
            (upstairsThreeDeckPair X x P q) := by
  let a := originalRegularThreeNativeHomologyIso X x P 3
  let e := relativeThreeHomologyIso X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) 3
  let dO := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map
      (originalRegularThreeDeckHomologyMap X x P q)
  let dN := SSetPair.homologyMap (nativeThreeDeckPair X x P q)
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 3
  let dU :=
      (relativeSingularHomologyFunctor AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).map
    (upstairsThreeDeckPair X x P q)
  have hN : dO ≫ a.hom = a.hom ≫ dN := originalRegularThreeNativeHomologyIso_deck X x P q
  have hU : dU ≫ e.hom = e.hom ≫ dN := relativeThreeHomologyIso_deck X x P _ q 3
  have hInv : dN ≫ e.inv = e.inv ≫ dU := by
    apply (cancel_mono e.hom).mp
    have hL : (dN ≫ e.inv) ≫ e.hom = dN :=
      (Category.assoc dN e.inv e.hom).trans
        ((congrArg (fun k => dN ≫ k) e.inv_hom_id).trans (Category.comp_id dN))
    have hR : (e.inv ≫ dU) ≫ e.hom = dN :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => e.inv ≫ k) hU).trans (e.inv_hom_id_assoc dN))
    exact hL.trans hR.symm
  change dO ≫ (a.hom ≫ e.inv) = (a.hom ≫ e.inv) ≫ dU
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.inv) hN).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun k => a.hom ≫ k) hInv).trans
          (Category.assoc _ _ _).symm)))


/-- The quotient acts on the ORIGINAL RR3 module by its actual coefficient-induced homology maps. -/
def originalRegularThreeDeckRepresentation : FundamentalGroup X x ⧸ P →*
    AddMonoid.End (originalRegularThreeHomology X x P 3) := by
  let ρ := fun q : FundamentalGroup X x ⧸ P =>
      (originalRegularThreeDeckHomologyMap X x P q).hom.toAddMonoidHom
  let e := originalRegularThreeUpstairsHomologyIso X x P 3
  let E := e.addCommGroupIsoToAddEquiv
  let N := upstairsThreeDeckRepresentation X x P
  have h : ∀ q a, e.hom (ρ q a) = N q (e.hom a) :=
    fun q a => ConcreteCategory.congr_hom (originalRegularThreeUpstairsHomologyIso_deck X x P q) a
  refine { toFun := ρ, map_one' := ?_, map_mul' := ?_ }
  · ext a
    apply E.injective
    exact (h 1 a).trans (congrArg (fun r : AddMonoid.End _ => r (e.hom a)) N.map_one)
  · intro q r
    ext a
    apply E.injective
    have hL : e.hom (ρ (q*r) a) = N q (N r (e.hom a)) :=
      (h (q*r) a).trans (congrArg (fun s : AddMonoid.End _ => s (e.hom a)) (N.map_mul q r))
    have hR : e.hom (ρ q (ρ r a)) = N q (N r (e.hom a)) :=
      (h q (ρ r a)).trans (congrArg (N q) (h r a))
    exact hL.trans hR.symm

/-- Linearization uses the literal noncommutative quotient group ring and original action. -/
def originalRegularThreeDeckRingHom : quotientGroupRing X x P →+*
    AddMonoid.End (originalRegularThreeHomology X x P 3) :=
  MonoidAlgebra.liftNCRingHom (Int.castRingHom
      (AddMonoid.End (originalRegularThreeHomology X x P 3)))
    (originalRegularThreeDeckRepresentation X x P)
    (fun z q => Int.cast_commute z (originalRegularThreeDeckRepresentation X x P q))

/-- The quotient-ring module is on the unchanged ORIGINAL relative homology carrier. -/
def originalRegularThreeDeckModule : Module (quotientGroupRing X x P)
    (originalRegularThreeHomology X x P 3) :=
  Module.compHom (originalRegularThreeHomology X x P 3) (originalRegularThreeDeckRingHom X x P)

/-- Every single quotient-ring coefficient is the original regular action,
with all integer coefficients and the original inverse-precomposition convention. -/
theorem originalRegularThreeDeckModule_single (q : FundamentalGroup X x ⧸ P) (z : ℤ)
    (a : originalRegularThreeHomology X x P 3) :
    letI := originalRegularThreeDeckModule X x P
    (MonoidAlgebra.single q z : quotientGroupRing X x P) • a = z •
        originalRegularThreeDeckRepresentation X x P q a := by
  let := originalRegularThreeDeckModule X x P
  have h : originalRegularThreeDeckRingHom X x P (MonoidAlgebra.single q z) =
      (z : AddMonoid.End (originalRegularThreeHomology X x P 3)) *
          originalRegularThreeDeckRepresentation X x P q :=
    MonoidAlgebra.liftNCRingHom_single (Int.castRingHom
        (AddMonoid.End (originalRegularThreeHomology X x P 3)))
      (originalRegularThreeDeckRepresentation X x P) _ q z
  change originalRegularThreeDeckRingHom X x P (MonoidAlgebra.single q z) a = _
  exact (congrArg (fun f : AddMonoid.End (originalRegularThreeHomology X x P 3) => f a) h).trans (by
    change (z : AddMonoid.End (originalRegularThreeHomology X x P 3))
      (originalRegularThreeDeckRepresentation X x P q a) = _
    rw [AddMonoid.End.intCast_def]
    rfl)

/-- The actual original RR3/upstairs comparison is linear for the two
computed original-coefficient and geometric quotient-ring actions. -/
def originalRegularThreeLambdaComparisonMap :
    letI := originalRegularThreeDeckModule X x P
    letI := upstairsThreeDeckModule X x P
    originalRegularThreeHomology X x P 3 →ₗ[quotientGroupRing X x P]
        upstairsThreeHomology X x P := by
  letI := originalRegularThreeDeckModule X x P
  letI := upstairsThreeDeckModule X x P
  let e := originalRegularThreeUpstairsHomologyIso X x P 3
  refine { toFun := e.hom, map_add' := e.hom.hom.map_add, map_smul' := ?_ }
  intro r a
  let f : quotientGroupRing X x P →+ upstairsThreeHomology X x P :=
    { toFun := fun s => e.hom (s • a)
      map_zero' := by rw [zero_smul, map_zero]
      map_add' := by intro s t; rw [add_smul, map_add] }
  let g : quotientGroupRing X x P →+ upstairsThreeHomology X x P :=
    { toFun := fun s => s • e.hom a
      map_zero' := zero_smul _ _
      map_add' := fun s t => add_smul s t (e.hom a) }
  have h : f = g := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro q z
    have hDeck : e.hom (originalRegularThreeDeckRepresentation X x P q a) =
        upstairsThreeDeckRepresentation X x P q (e.hom a) :=
      ConcreteCategory.congr_hom (originalRegularThreeUpstairsHomologyIso_deck X x P q) a
    exact (congrArg e.hom (originalRegularThreeDeckModule_single X x P q z a)).trans
      ((e.hom.hom.map_zsmul z _).trans
        ((congrArg (fun c => z • c) hDeck).trans
          (upstairsThreeDeckModule_single X x P q z (e.hom a)).symm))
  exact congrArg (fun h => h r) h

/-- The SAME original RR3 comparison has an actual linear inverse. -/
def originalRegularThreeLambdaComparisonIso :
    letI := originalRegularThreeDeckModule X x P
    letI := upstairsThreeDeckModule X x P
    originalRegularThreeHomology X x P 3 ≃ₗ[quotientGroupRing X x P]
        upstairsThreeHomology X x P := by
  letI := originalRegularThreeDeckModule X x P
  letI := upstairsThreeDeckModule X x P
  let f := originalRegularThreeLambdaComparisonMap X x P
  exact LinearEquiv.ofBijective f
      (originalRegularThreeUpstairsHomologyIso X x P 3).addCommGroupIsoToAddEquiv.bijective

/-- The forward linear comparison is the SAME computed original homology map. -/
theorem originalRegularThreeLambdaComparisonIso_apply (a : originalRegularThreeHomology X x P 3) :
    originalRegularThreeLambdaComparisonIso X x P a =
        (originalRegularThreeUpstairsHomologyIso X x P 3).hom a := by
  rfl

/-- Its inverse is the actual inverse of that SAME original comparison. -/
theorem originalRegularThreeLambdaComparisonIso_inverse_apply (a : upstairsThreeHomology X x P) :
    (originalRegularThreeLambdaComparisonIso X x P).symm a =
        (originalRegularThreeUpstairsHomologyIso X x P 3).inv a := by
  let e := originalRegularThreeUpstairsHomologyIso X x P 3
  let c := originalRegularThreeLambdaComparisonIso X x P
  apply e.addCommGroupIsoToAddEquiv.injective
  have hL : e.hom (c.symm a) = a := c.apply_symm_apply a
  have hR : e.hom (e.inv a) = a := ConcreteCategory.congr_hom e.inv_hom_id a
  exact hL.trans hR.symm

/-- The ENTIRE actual ORIGINAL RR3 module is free over the quotient group ring,
with the exact same original chosen three-disk/sphere family and every quotient label. -/
def originalRegularThreeLambdaBasisIso :
    letI := originalRegularThreeDeckModule X x P
    (P →₀ quotientGroupRing X x P) ≃ₗ[quotientGroupRing X x P] originalRegularThreeHomology
        X x P 3 := by
  letI := originalRegularThreeDeckModule X x P
  letI := upstairsThreeDeckModule X x P
  exact (upstairsThreeLambdaBasisIso X x P).trans
      (originalRegularThreeLambdaComparisonIso X x P).symm

/-- Every original quotient/P/integer coefficient uses the SAME actual
upstairs three-disk class through the inverse original RR3 comparison. -/
theorem originalRegularThreeLambdaBasisIso_single (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    originalRegularThreeLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z)) =
      (originalRegularThreeUpstairsHomologyIso X x P 3).inv
        ((CategoryTheory.Limits.Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
          (singularIntegralCoefficients : AddCommGrpCat.{u})) (q,p) ≫
            (upstairsThreeCoefficientIso X x P).hom) (ULift.up z)) := by
  let := originalRegularThreeDeckModule X x P
  let := upstairsThreeDeckModule X x P
  exact (originalRegularThreeLambdaComparisonIso_inverse_apply X x P
    (upstairsThreeLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z)))).trans
      (congrArg (originalRegularThreeUpstairsHomologyIso X x P 3).inv
        (upstairsThreeLambdaBasisIso_single X x P q p z))

/-- The inverse recovers every coefficient of every actual original RR3 cell. -/
theorem originalRegularThreeLambdaBasisIso_inverse_single (q : FundamentalGroup X x ⧸ P)
    (p : P) (z : ℤ) :
    (originalRegularThreeLambdaBasisIso X x P).symm
      ((originalRegularThreeUpstairsHomologyIso X x P 3).inv
        ((CategoryTheory.Limits.Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
          (singularIntegralCoefficients : AddCommGrpCat.{u})) (q,p) ≫
            (upstairsThreeCoefficientIso X x P).hom) (ULift.up z))) =
      Finsupp.single p (MonoidAlgebra.single q z) := by
  exact (congrArg (originalRegularThreeLambdaBasisIso X x P).symm
    (originalRegularThreeLambdaBasisIso_single X x P q p z).symm).trans
      ((originalRegularThreeLambdaBasisIso X x P).symm_apply_apply _)

/-- The derived linear map uses the actual RR3 comparison and SAME upstairs
boundary; the next equality certifies it is the ORIGINAL module-valued LES map. -/
def originalRegularThreeToTwoLinearMap :
    letI := originalRegularThreeDeckModule X x P
    letI := originalRegularDeckModule X x P
    originalRegularThreeHomology X x P 3 →ₗ[quotientGroupRing X x P]
        originalRegularHomologyTwo X x P := by
  letI := originalRegularThreeDeckModule X x P
  letI := originalRegularDeckModule X x P
  letI := upstairsThreeDeckModule X x P
  exact (actualThreeToOriginalRegularLambdaMap X x P).comp
      (originalRegularThreeLambdaComparisonMap X x P)

private theorem originalRegularThreeToTwoLinearMap_recipe_cached
    (a : originalRegularThreeHomology X x P 3) :
    letI := originalRegularThreeDeckModule X x P
    letI := originalRegularDeckModule X x P
    originalRegularThreeToTwoLinearMap X x P a =
      actualThreeToOriginalRegularLambdaMap X x P
        ((originalRegularThreeUpstairsHomologyIso X x P 3).hom a) := by rfl

private theorem originalRegularThreeToTwoLinearMap_apply_cached
    (a : originalRegularThreeHomology X x P 3) :
    letI := originalRegularThreeDeckModule X x P
    letI := originalRegularDeckModule X x P
    originalRegularThreeToTwoLinearMap X x P a = originalRegularThreeToTwoBoundary X x P a := by
  let U : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _
  let D : AddCommGrpCat.{u} := U.obj (originalRegularThreeHomology X x P 3)
  let E : AddCommGrpCat.{u} := U.obj (originalRegularHomologyTwo X x P)
  let V : AddCommGrpCat.{u} := upstairsThreeHomology X x P
  let T : AddCommGrpCat.{u} := nativeHomologyTwo X x P
      (singularIntegralCoefficients : AddCommGrpCat.{u})
  let e2 : E ≅ T := originalRegularNativeHomologyIso X x P
  let e3 : D ≅ V := originalRegularThreeUpstairsHomologyIso X x P 3
  let b : V ⟶ T := actualThreeRelativeBoundary X x P
  let d : originalRegularThreeHomology X x P 3 ⟶ originalRegularHomologyTwo X x P :=
    originalRegularThreeToTwoBoundary X x P
  have hMap : e3.hom ≫ b = U.map d ≫ e2.hom := originalRegularThreeToTwoBoundary_upstairs X x P
  have hValue : b (e3.hom a) = e2.hom (d a) :=
    congrArg (fun f : D ⟶ T => f.hom a) hMap
  have hInv : e2.inv (e2.hom (d a)) = d a :=
    congrArg (fun f : E ⟶ E => f.hom (d a)) e2.hom_inv_id
  exact (originalRegularThreeToTwoLinearMap_recipe_cached X x P a).trans
    ((actualThreeToOriginalRegularLambdaMap_apply X x P (e3.hom a)).trans
      ((congrArg (fun z : T => e2.inv z) hValue).trans hInv))

/-- The entire linear map is the ORIGINAL connecting map, computed old
coefficient return and original RR2 quotient, on every original class. -/
theorem originalRegularThreeToTwoLinearMap_apply (a : originalRegularThreeHomology X x P 3) :
    originalRegularThreeToTwoLinearMap X x P a = originalRegularThreeToTwoBoundary X x P a := by
  exact originalRegularThreeToTwoLinearMap_apply_cached X x P a

/-- The complete matrix uses the ENTIRE ORIGINAL RR3 and RR2 quotient-ring bases. -/
def originalRR3ToRR2Matrix : (P →₀ quotientGroupRing X x P) →ₗ[quotientGroupRing X x P]
    (P →₀ quotientGroupRing X x P) := by
  letI := originalRegularThreeDeckModule X x P
  letI := originalRegularDeckModule X x P
  exact (originalRegularLambdaBasisIso X x P).symm.toLinearMap.comp
    ((originalRegularThreeToTwoLinearMap X x P).comp
        (originalRegularThreeLambdaBasisIso X x P).toLinearMap)

/-- The complete public matrix acts through the SAME original two
quotient-ring bases and the ENTIRE actual original connecting map. -/
theorem originalRR3ToRR2Matrix_apply
    (a : P →₀ quotientGroupRing X x P) :
    originalRR3ToRR2Matrix X x P a =
      (originalRegularLambdaBasisIso X x P).symm
        (originalRegularThreeToTwoLinearMap X x P
          (originalRegularThreeLambdaBasisIso X x P a)) := by
  unfold originalRR3ToRR2Matrix
  rfl

/-- The WHOLE ORIGINAL quotient-group-ring three-to-two matrix is identity,
with every quotient label and integer coefficient, not an augmentation-only equality. -/
theorem originalRR3ToRR2Matrix_eq_id : originalRR3ToRR2Matrix X x P = LinearMap.id := by
  let := originalRegularThreeDeckModule X x P
  let := originalRegularDeckModule X x P
  let := upstairsThreeDeckModule X x P
  let e2 := originalRegularLambdaBasisIso X x P
  let e3 := upstairsThreeLambdaBasisIso X x P
  let c := originalRegularThreeLambdaComparisonIso X x P
  let b := actualThreeToOriginalRegularLambdaMap X x P
  have hSame : originalRR3ToRR2Matrix X x P = actualOriginalRegularThreeToTwoMatrix X x P := by
    apply LinearMap.ext
    intro a
    change e2.symm (b (c (c.symm (e3 a)))) = e2.symm (b (e3 a))
    exact congrArg (fun z => e2.symm (b z)) (c.apply_symm_apply (e3 a))
  exact hSame.trans (actualOriginalRegularThreeToTwoMatrix_eq_id X x P)

/-- Each same selected original three-disk has its full positive quotient/P
coordinate under the ORIGINAL LES map, for EVERY integral coefficient. -/
theorem originalRegularThreeToTwoBoundary_single (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    originalRegularThreeToTwoBoundary X x P
      (originalRegularThreeLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z))) =
        originalRegularLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z)) := by
  let := originalRegularThreeDeckModule X x P
  let := originalRegularDeckModule X x P
  let e := originalRegularLambdaBasisIso X x P
  let v := Finsupp.single p (MonoidAlgebra.single q z)
  have h :
      e.symm (originalRegularThreeToTwoLinearMap X x P
        (originalRegularThreeLambdaBasisIso X x P v)) = v :=
    LinearMap.congr_fun (originalRR3ToRR2Matrix_eq_id X x P) v
  have hValue : originalRegularThreeToTwoLinearMap X x P
      (originalRegularThreeLambdaBasisIso X x P v) = e v :=
    (e.apply_symm_apply _).symm.trans (congrArg e h)
  exact (originalRegularThreeToTwoLinearMap_apply X x P _).symm.trans hValue


/-- LEFT multiplication of the original quotient label is the original
coefficient-induced RR3 deck action on the entire free basis. -/
theorem originalRegularThreeLambdaBasisIso_deck (q : FundamentalGroup X x ⧸ P)
    (v : P →₀ quotientGroupRing X x P) :
    originalRegularThreeDeckRepresentation X x P q (originalRegularThreeLambdaBasisIso X x P v) =
      originalRegularThreeLambdaBasisIso X x P ((MonoidAlgebra.single q (1 : ℤ)) • v) := by
  let := originalRegularThreeDeckModule X x P
  let e := originalRegularThreeLambdaBasisIso X x P
  have hAction : (MonoidAlgebra.single q (1 : ℤ)) • e v =
      originalRegularThreeDeckRepresentation X x P q (e v) :=
    (originalRegularThreeDeckModule_single X x P q 1 (e v)).trans (one_zsmul _)
  have hMap : e ((MonoidAlgebra.single q (1 : ℤ)) • v) = (MonoidAlgebra.single q (1 : ℤ)) • e v :=
    e.map_smul _ v
  exact hAction.symm.trans hMap.symm

/-- The SAME whole native three-disk translates by LEFT multiplication q*r,
while its original first-path choice is retained. -/
theorem nativeThreeDiskCopy_deck (q r : FundamentalGroup X x ⧸ P) (p : P) :
    nativeThreeDiskCopy X x P (q*r,p) = nativeThreeDiskCopy X x P (r,p) ≫
      SSet.KanComplex.nativeCoverDeckMap (quotientThreeDeckIndex X x P q) := by
  let L := nativeThreeDiskLift X x P p
  let e := quotientThreeDeckIndex X x P
  exact (congrArg (fun a => L ≫ SSet.KanComplex.nativeCoverDeckMap a) (e.map_mul q r)).trans
    ((congrArg (fun f => L ≫ f) (SSet.KanComplex.nativeCoverDeckMap_mul (e q) (e r))).trans
      (Category.assoc _ _ _).symm)

/-- The whole original upstairs characteristic pair is formed from the same
matched disk/boundary adjoints and the actual original old inclusion. -/
def singularUpstairsThreeCharacteristicPair (i : LoopCellQuotientCellPresentation.labels X x P) :
    SSetPair.of (SSet.boundary.{u} 3).ι ⟶ singularUpstairsThreePair X x P :=
  SSetPair.ofHom
    (sSetTopAdj.homEquiv (Δ[3] : SSet.{u}) (upstairsThreeSpace X x P)
      ((SSet.boundary.toClassicalCellDiskArrowIso 3).hom.right ≫
        CellFamilyAttachment.cell (LoopCellSphericalGenerators.liftedPair X x P).fst 2
            (chosenSphericalCopy X x P) i))
    (upstairsBoundaryMate X x P i)
    (CellFamilySimplicialModel.adjunctSquare_cell
        (LoopCellSphericalGenerators.liftedPair X x P).fst 2
      (LoopCellQuotientCellPresentation.labels X x P) (chosenSphericalCopy X x P) i)

/-- The corresponding SAME original quotient-labelled characteristic pair
in the native cover uses the complete computed lift and original old pullback. -/
def nativeThreeCharacteristicPair (i : LoopCellQuotientCellPresentation.labels X x P) :
    SSetPair.of (SSet.boundary.{u} 3).ι ⟶ nativeThreePair X x P :=
  SSetPair.ofHom (nativeThreeDiskCopy X x P i)
    (upstairsBoundaryMate X x P i ≫ oldSingularToThreePullback X x P)
    ((Category.assoc _ _ _).trans (nativeThreeDiskCopy_boundary X x P i).symm)

/-- The pair comparison preserves the WHOLE same characteristic pair in
every quotient/P copy, including its boundary and original first-path connector. -/
theorem singularUpstairsThreeCharacteristicPair_native
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    singularUpstairsThreeCharacteristicPair X x P i ≫ singularUpstairsThreePairComparison X x P =
      nativeThreeCharacteristicPair X x P i := by
  apply MorphismProperty.Arrow.Hom.ext
  · rfl
  · exact singularUpstairsThreeToNative_cell X x P i

end PulledThreeCellFamily

end AlgebraicTopology.LoopCellRegularThreeComparison

end
