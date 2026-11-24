/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticCoefficientPeriodScalars
public import MathlibExt.CategoryTheory.ResolvedFiniteInverseImages
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Full integral coefficient towers and native finite-image realization

Finite levels are actual locally constant, finitely generated module
sheaves on the original etale site. Compatibility is required only up to
the actual formal pro-isomorphism, as in Scholze Definition 8.1; the
higher finite direct-image tower is not forced to have strict reduction
compatibility.

The original inverse image is applied at every finite level BEFORE the
native whole-diagram resolution and derived Milnor fibre. Rational
local systems remain separately available as native finite locally free
`Qhat` modules without a global integral lattice.

Reference: Scholze, arXiv:1205.3463v2, Definitions 8.1--8.3 and the
footnote to Proposition 8.2; native Mathlib sheaf, module, cokernel and
ind-presheaf constructions, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProEtaleIntegralTowers

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProEtaleCoefficientSources AnalyticProObjectSites
open MathlibExt.CategoryTheory.ResolvedFiniteInverseImages
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (X : AnalyticAdicSpace p) (P : PointRealization p X)

abbrev EtaleCoefficients := Sheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p X)
  (ModuleCat.{1} ℤ_[p])
abbrev ProCoefficients := Sheaf (proTopology p X P) (ModuleCat.{1} ℤ_[p])

section LocalModels

variable [∀ U : AnalyticProObjectSites.Etale p X,
  (Over.forget U).IsContinuous ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X).over U)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X)]
  [∀ U : AnalyticProObjectSites.Etale p X,
    HasSheafify ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X).over U) (ModuleCat.{1} ℤ_[p])]

def restricted (L : EtaleCoefficients p X) (U : AnalyticProObjectSites.Etale p X) :=
  ((Over.forget U).sheafPushforwardContinuous (ModuleCat.{1} ℤ_[p])
    ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X).over U)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X)).obj L

def constantLocal (U : AnalyticProObjectSites.Etale p X) (M : ModuleCat.{1} ℤ_[p]) :=
  (presheafToSheaf ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X).over U)
    (ModuleCat.{1} ℤ_[p])).obj ((Functor.const (Over U)ᵒᵖ).obj M)

def IsFiniteLocallyConstant (L : EtaleCoefficients p X) : Prop :=
  ∀ U : AnalyticProObjectSites.Etale p X,
    ∃ S : Sieve U, S ∈ AnalyticDiamondEtaleSites.analyticEtaleTopology p X U ∧
      ∀ (V : AnalyticProObjectSites.Etale p X) (f : V ⟶ U), S f →
        ∃ M : ModuleCat.{1} ℤ_[p], Module.Finite ℤ_[p] M ∧
          Nonempty (restricted p X L V ≅ constantLocal p X V M)

end LocalModels

/-- The literal formal pro-isomorphism, retaining all natural-transformation pro-morphisms. -/
def ProIsomorphic {A : Type*} [Category* A] (T U : ℕᵒᵖ ⥤ A) : Prop :=
  Nonempty (colimit (T.op ⋙ yoneda) ≅ colimit (U.op ⋙ yoneda))

def transition (T : ℕᵒᵖ ⥤ EtaleCoefficients p X) (n : ℕ) :=
  T.map (homOfLE (Nat.le_succ n)).op

/-- Every reduction is the actual universal cokernel of multiplication by p^(n+1). -/
structure CompatibleReduction (T : ℕᵒᵖ ⥤ EtaleCoefficients p X) where
  zero : ∀ n : ℕ, (p ^ (n + 1) • 𝟙 (T.obj (op (n + 1)))) ≫ transition p X T n = 0
  cokernel : ∀ n : ℕ, IsColimit (CokernelCofork.ofπ (transition p X T n) (zero n))

variable [∀ U : AnalyticProObjectSites.Etale p X,
  (Over.forget U).IsContinuous ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X).over U)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X)]
  [∀ U : AnalyticProObjectSites.Etale p X,
    HasSheafify ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X).over U) (ModuleCat.{1} ℤ_[p])]

structure LisseIntegralTower where
  tower : ℕᵒᵖ ⥤ EtaleCoefficients p X
  finite : ∀ n : ℕ, IsFiniteLocallyConstant p X (tower.obj (op n))
  annihilated : ∀ (n : ℕ) (U : (AnalyticProObjectSites.Etale p X)ᵒᵖ)
    (m : (tower.obj (op n)).obj.obj U), (p ^ (n + 1) : ℤ_[p]) • m = 0
  compatible : ℕᵒᵖ ⥤ EtaleCoefficients p X
  proIso : ProIsomorphic tower compatible
  reduction : CompatibleReduction p X compatible

variable [(etaleEmbedding p X).IsContinuous
  (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)]
  [((etaleEmbedding p X).sheafPushforwardContinuous (ModuleCat.{1} ℤ_[p])
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)).IsRightAdjoint]

/-- Original finite inverse image, not an inverse image of an already completed limit. -/
def finiteInverseImage : EtaleCoefficients p X ⥤ ProCoefficients p X P :=
  (etaleEmbedding p X).sheafPullback (ModuleCat.{1} ℤ_[p])
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)

variable [Abelian (ProCoefficients p X P)]
  [EnoughInjectives (ℕᵒᵖ ⥤ ProCoefficients p X P)]
  [HasLimitsOfShape (Discrete ℕ) (ProCoefficients p X P)]
  (L : LisseIntegralTower p X)

def finiteResolution := nativeResolution (finiteInverseImage p X P) L.tower

def derivedRealization (Q : Qualification (finiteInverseImage p X P) L.tower) :=
  derivedLimit (finiteInverseImage p X P) L.tower Q

def finiteProjection (Q : Qualification (finiteInverseImage p X P) L.tower) (n : ℕ) :=
  MathlibExt.CategoryTheory.ResolvedFiniteInverseImages.finiteProjection
    (finiteInverseImage p X P) L.tower Q n

/-- Projection on actual native degree-zero cohomology, before forgetting the Z_p action. -/
def nativeDegreeZeroProjection (Q : Qualification (finiteInverseImage p X P) L.tower) (n : ℕ) :=
  (DerivedCategory.homologyFunctor (ProCoefficients p X P) 0).map
    (finiteProjection p X P L Q n)

variable [HasSheafify (proTopology p X P) CommRingCat.{1}]

local instance moduleAdditiveSheafCompose : (proTopology p X P).HasSheafCompose
    (forget₂ (ModuleCat.{1} ℤ_[p]) AddCommGrpCat.{1}) :=
  hasSheafCompose_of_preservesLimitsOfSize _

/-- The integral local system is a SOURCE output on the actual native degree-zero finite-image
limit. Its additive carrier is fixed; naturality and p^n-annihilated finite projections determine
the continuous Zhat action locally. This also permits finitely generated torsion coefficients. -/
structure IntegralRealizationSource (Q : Qualification (finiteInverseImage p X P) L.tower) where
  module : Modules (Zhat p X P)
  nativeCarrier : (SheafOfModules.toSheaf (moduleRing (Zhat p X P))).obj module ≅
    (sheafCompose (proTopology p X P) (forget₂ (ModuleCat.{1} ℤ_[p]) AddCommGrpCat.{1})).obj
      ((DerivedCategory.homologyFunctor (ProCoefficients p X P) 0).obj (derivedRealization p X P L Q))
  finite_action_source : ∀ (U : (ProEtaleSite p X)ᵒᵖ)
    (a : C(P.functor.obj U.unop, ℤ_[p])) (n : ℕ)
    (V : ProEtaleSite p X) (f : V ⟶ U.unop) (c : ℤ_[p]),
    (∀ x, PadicInt.toZModPow (n + 1) (a (P.functor.map f x)) =
      PadicInt.toZModPow (n + 1) c) → ∀ m : module.val.obj (op V),
    (((nativeDegreeZeroProjection p X P L Q n).hom.app (op V)).hom)
      (show (((DerivedCategory.homologyFunctor (ProCoefficients p X P) 0).obj
        (derivedRealization p X P L Q)).obj.obj (op V)) from
        ((nativeCarrier.hom.hom.app (op V)).hom)
          ((((toSheafify (proTopology p X P)
            (AnalyticCoefficientPeriodScalars.rawIntegral p X P)).app (op V)).hom
              (ULift.up (a.comp (P.functor.map f).hom))) • m)) =
    c • (((nativeDegreeZeroProjection p X P L Q n).hom.app (op V)).hom)
      (show (((DerivedCategory.homologyFunctor (ProCoefficients p X P) 0).obj
        (derivedRealization p X P L Q)).obj.obj (op V)) from
        ((nativeCarrier.hom.hom.app (op V)).hom) m)

end MathlibExt.AlgebraicGeometry.ProEtaleIntegralTowers
