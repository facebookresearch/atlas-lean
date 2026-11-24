/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRamificationReindexing
public import MathlibExt.AlgebraicGeometry.SheafTensorSections

/-!
# Actual regularized K-valued Higgs bundles

The regularizer is a native fppf G torsor and its actual equivariant map
to the regular-centralizer parameter scheme. The adjoint bundle descends
the literal Lie module with the inverse native adjoint coefficient on
the torsor relation. The centralizer subbundle pulls to the literal
universal subbundle through sigma, including the inclusion into the
adjoint bundle. The K-valued section belongs to that subbundle tensor K.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 2 and 17.1--17.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralRegularizedHiggsModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralIncidenceModels CameralRamificationReindexing
open RegularCentralizerAffineModels GroupTorsorGeometry LinearizedLineBundles
open SchemeLieJetFamilies
open ExpansionParameterModels CoherentCurveLinearSeries LineBundleTaskContracts
open AlgebraicLineBundleFamilies

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori)

@[instance_reducible] def centralizerGroupAction : ModObj G F.centralizers.scheme :=
  F.centralizerAction.action

attribute [local instance] centralizerGroupAction

abbrev Regularizer (X : Over (Spec (.of ℂ))) :=
  QuotientObject G F.centralizers.scheme X

variable {X : Over (Spec (.of ℂ))} (P : Regularizer F X)

def descentComparison (M : X.left.Modules) :
    (Scheme.Modules.pullback γ[G,P.torsor.total].left).obj
      ((Scheme.Modules.pullback P.torsor.projection.left).obj M) ≅
    (Scheme.Modules.pullback (snd G P.torsor.total).left).obj
      ((Scheme.Modules.pullback P.torsor.projection.left).obj M) :=
  (Scheme.Modules.pullbackComp γ[G,P.torsor.total].left P.torsor.projection.left).app M ≪≫
  (Scheme.Modules.pullbackCongr
    (congrArg (fun f : G ⊗ P.torsor.total ⟶ X => f.left) P.torsor.invariant)).app M ≪≫
  (Scheme.Modules.pullbackComp (snd G P.torsor.total).left P.torsor.projection.left).symm.app M

def transportedDescent (M : X.left.Modules) (N : P.torsor.total.left.Modules)
    (e : (Scheme.Modules.pullback P.torsor.projection.left).obj M ≅ N) :
    (Scheme.Modules.pullback γ[G,P.torsor.total].left).obj N ≅
      (Scheme.Modules.pullback (snd G P.torsor.total).left).obj N :=
  (Scheme.Modules.pullback γ[G,P.torsor.total].left).mapIso e.symm ≪≫
    descentComparison F P M ≪≫
    (Scheme.Modules.pullback (snd G P.torsor.total).left).mapIso e

abbrev pulledLie : P.torsor.total.left.Modules :=
  (Scheme.Modules.pullback P.map.left).obj (lieModule F.lie.carrier F.centralizers.scheme)

def adjointCoefficientMap
    (a : Linearization G P.torsor.total (pulledLie F P)) (A : CommAlgCat.{0} ℂ)
    (f : affine A ⟶ G ⊗ P.torsor.total) :
    (Scheme.Modules.pullback ((f ≫ γ[G,P.torsor.total]) ≫ P.map).left).obj
      (lieModule F.lie.carrier F.centralizers.scheme) ⟶
    (Scheme.Modules.pullback ((f ≫ snd G P.torsor.total) ≫ P.map).left).obj
      (lieModule F.lie.carrier F.centralizers.scheme) :=
  (Scheme.Modules.pullbackComp (f ≫ γ[G,P.torsor.total]).left P.map.left).inv.app _ ≫
    reindexHom f.left a.comparison.hom ≫
    (Scheme.Modules.pullbackComp (f ≫ snd G P.torsor.total).left P.map.left).hom.app _

structure AdjointBundle where
  module : X.left.Modules
  rank : CurveVectorBundles.IsVectorBundle module (Module.finrank ℂ F.lie.carrier)
  trivialization : (Scheme.Modules.pullback P.torsor.projection.left).obj module ≅ pulledLie F P
  descent : Linearization G P.torsor.total (pulledLie F P)
  descent_normalized : descent.comparison =
    transportedDescent F P module (pulledLie F P) trivialization
  coefficients : ∀ (A : CommAlgCat.{0} ℂ) (f : affine A ⟶ G ⊗ P.torsor.total)
      (s : Γ((Scheme.Modules.pullback ((f ≫ γ[G,P.torsor.total]) ≫ P.map).left).obj
        (lieModule F.lie.carrier F.centralizers.scheme), ⊤)),
    F.centralizers.lieSections A ((f ≫ snd G P.torsor.total) ≫ P.map)
      ((((adjointCoefficientMap F P descent A f).val.app (.op ⊤)).hom) s) =
    (F.adjoint.adjoint A (f ≫ fst G P.torsor.total)).symm
      (F.centralizers.lieSections A ((f ≫ γ[G,P.torsor.total]) ≫ P.map) s)

structure CentralizerBundle (A : AdjointBundle F P) where
  module : X.left.Modules
  rank : CurveVectorBundles.IsVectorBundle module F.rank
  inclusion : module ⟶ A.module
  [mono : Mono inclusion]
  trivialization : (Scheme.Modules.pullback P.torsor.projection.left).obj module ≅
    (Scheme.Modules.pullback P.map.left).obj F.centralizers.universal
  inclusion_normalized :
    (Scheme.Modules.pullback P.torsor.projection.left).map inclusion ≫ A.trivialization.hom =
    trivialization.hom ≫ (Scheme.Modules.pullback P.map.left).map F.centralizers.inclusion

structure TwistLine (Y : Over (Spec (.of ℂ))) where
  module : Y.left.Modules
  line : IsLineBundle module

structure RegularizedBundle (Y : Over (Spec (.of ℂ))) (K : TwistLine Y) where
  regularizer : Regularizer F Y
  adjoint : AdjointBundle F regularizer
  centralizer : CentralizerBundle F regularizer adjoint
  sectionMap : Section (moduleTensor Y.left centralizer.module K.module)

def ordinaryHiggsSection {Y : Over (Spec (.of ℂ))} {K : TwistLine Y}
    (H : RegularizedBundle F Y K) : Section (moduleTensor Y.left H.adjoint.module K.module) :=
  H.sectionMap ≫ tensorMap H.centralizer.inclusion (𝟙 K.module)

def baseComparison {Y : Over (Spec (.of ℂ))} {P P' : Regularizer F Y} (r : P ⟶ P')
    (M : Y.left.Modules) :
    (Scheme.Modules.pullback P.torsor.projection.left).obj M ≅
      (Scheme.Modules.pullback r.iso.hom.left).obj
        ((Scheme.Modules.pullback P'.torsor.projection.left).obj M) :=
  (Scheme.Modules.pullbackCongr
    (congrArg (fun f : P.torsor.total ⟶ Y => f.left) r.over.symm)).app M ≪≫
      (Scheme.Modules.pullbackComp r.iso.hom.left P'.torsor.projection.left).symm.app M

def targetComparison {Y : Over (Spec (.of ℂ))} {P P' : Regularizer F Y} (r : P ⟶ P')
    (M : F.centralizers.scheme.left.Modules) :
    (Scheme.Modules.pullback P.map.left).obj M ≅
      (Scheme.Modules.pullback r.iso.hom.left).obj ((Scheme.Modules.pullback P'.map.left).obj M) :=
  (Scheme.Modules.pullbackCongr
    (congrArg (fun f : P.torsor.total ⟶ F.centralizers.scheme => f.left) r.target.symm)).app M ≪≫
      (Scheme.Modules.pullbackComp r.iso.hom.left P'.map.left).symm.app M

structure Hom {Y : Over (Spec (.of ℂ))} {K : TwistLine Y}
    (H H' : RegularizedBundle F Y K) where
  regularizer : H.regularizer ⟶ H'.regularizer
  adjoint : H.adjoint.module ≅ H'.adjoint.module
  centralizer : H.centralizer.module ≅ H'.centralizer.module
  adjoint_normalized :
    (Scheme.Modules.pullback H.regularizer.torsor.projection.left).map adjoint.hom ≫
      (baseComparison F regularizer H'.adjoint.module).hom ≫
      (Scheme.Modules.pullback regularizer.iso.hom.left).map H'.adjoint.trivialization.hom =
    H.adjoint.trivialization.hom ≫
      (targetComparison F regularizer (lieModule F.lie.carrier F.centralizers.scheme)).hom
  centralizer_normalized :
    (Scheme.Modules.pullback H.regularizer.torsor.projection.left).map centralizer.hom ≫
      (baseComparison F regularizer H'.centralizer.module).hom ≫
      (Scheme.Modules.pullback regularizer.iso.hom.left).map H'.centralizer.trivialization.hom =
    H.centralizer.trivialization.hom ≫
      (targetComparison F regularizer F.centralizers.universal).hom
  inclusion : centralizer.hom ≫ H'.centralizer.inclusion = H.centralizer.inclusion ≫ adjoint.hom
  sectionMap : H.sectionMap ≫ tensorMap centralizer.hom (𝟙 K.module) = H'.sectionMap

end MathlibExt.AlgebraicGeometry.CameralRegularizedHiggsModels
