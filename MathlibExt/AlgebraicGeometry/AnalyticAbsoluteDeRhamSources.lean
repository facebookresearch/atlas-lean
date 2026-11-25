/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProEtaleDeRhamSources
public import MathlibExt.CategoryTheory.NativeConnectionProperties

/-!
# Source-qualified absolute cochains and original K scalars

The scalar is the original map from the actual K base through native
Gamma and the original etale inverse image. Absolute forms and
coefficients are the native inverse images of their actual continuous
affinoid models. Every cochain differential is fixed on all original
affinoid native extended-connection units. This is the absolute source
used by the normalized Gauss--Manin cofactor, before any higher output.

Sources: Scholze, arXiv:1205.3463v2, Definitions 6.8 and 7.4,
Proposition 8.5 and Theorem 8.8; complete PR2245 native connection port,
Apache 2.0, `76de3f2665f9c44b06932f9861ee9aae65e04395`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticAbsoluteDeRhamSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources
open AnalyticRelativeDeRhamSources
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs
open MathlibExt.CategoryTheory.RingSheafModuleTensors
open MathlibExt.CategoryTheory.SheafScalarQuotients
open MathlibExt.RingTheory.ContinuousDeRhamQuotients
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)
  (X : Over B.analytic) (P : AnalyticProObjectSites.PointRealization p X.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left P) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).IsRightAdjoint]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
    (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) AddCommGrpCat.{1}]
  [(AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify (proTopology p X.left P) AddCommGrpCat.{1}]
  [(proTopology p X.left P).WEqualsLocallyBijective AddCommGrpCat.{1}]
  (S : Source p K B X P)
  [(modulePushforward (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
    S.regular (AnalyticPerfectoidPeriodCharts.originalRingUnit p K B X P S)).IsRightAdjoint]

abbrev constantK := constantRing (J := proTopology p X.left P) (BaseField.carrier p K)
abbrev constantKEtale := constantRing (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
  (BaseField.carrier p K)

/-- Original K scalars are fixed on all native constant units by the actual map to the base. -/
structure EtaleKScalarSource where
  map : constantKEtale p K B X ⟶ regularEtale p X.left S.regularSheaf
  source : ∀ (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ) (a : BaseField.carrier p K),
    (((map.hom.app U).hom)
      (((toSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
        ((Functor.const (AnalyticProObjectSites.Etale p X.left)ᵒᵖ).obj
          (CommRingCat.of (ULift.{1} (BaseField.carrier p K))))).app U).hom (ULift.up a))).down =
      ((_root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map
        ((U.unop.obj.hom ≫ X.hom).hom.val).op).hom)
          (AnalyticBaseWittScalarSources.baseCoordinates p K B a)

variable [IsIso (constantInverseMap
  (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
  (etaleInclusion p X.left) (BaseField.carrier p K))]

def proKScalar (s : EtaleKScalarSource p K B X P S) : constantK p K B X P ⟶ S.regular :=
  inv (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
    (etaleInclusion p X.left) (BaseField.carrier p K)) ≫
      ((etaleInclusion p X.left).sheafPullback CommRingCat.{1}
        (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).map s.map

variable (Ω : AnalyticRelativeDeRhamSources.DifferentialSource p X.hom S.regularSheaf)
  (M : AnalyticRelativeDeRhamSources.BaseCoefficientInput p X.hom S.regularSheaf Ω)

abbrev forms := AnalyticPerfectoidPeriodCharts.absoluteForms p K B X P S Ω
def coefficient : Modules S.regular :=
  (modulePullback (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
    S.regular (AnalyticPerfectoidPeriodCharts.originalRingUnit p K B X P S)).obj M.module

abbrev originalUnit := AnalyticPerfectoidPeriodCharts.originalRingUnit p K B X P S

local instance (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ) :
    CommRing ((moduleRing (regularEtale p X.left S.regularSheaf)).obj.obj U) :=
  inferInstanceAs (CommRing ((regularEtale p X.left S.regularSheaf).obj.obj U))
local instance (U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ) :
    CommRing ((moduleRing S.regular).obj.obj U) := inferInstanceAs (CommRing (S.regular.obj.obj U))

def inverseUnitSemilinear (M₀ : Modules (regularEtale p X.left S.regularSheaf))
    (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ) :
    M₀.val.obj U →ₛₗ[((originalUnit p K B X P S).hom.app U).hom]
      (((modulePullback (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
        S.regular (originalUnit p K B X P S)).obj M₀).val.obj ((etaleInclusion p X.left).op.obj U)) where
  toFun m := (((moduleAdjunction (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
    S.regular (originalUnit p K B X P S)).unit.app M₀).val.app U).hom m
  map_add' _m _n := map_add _ _ _
  map_smul' r m := (((moduleAdjunction (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
    S.regular (originalUnit p K B X P S)).unit.app M₀).val.app U).hom.map_smul r m

variable (k : EtaleKScalarSource p K B X P S)

/-- The degree-one form differential is the ORIGINAL continuous quotient differential on
every affinoid unit, glued on the actual pro inverse-image sheaf. -/
structure OneFormSource (AΩ : AnalyticPerfectoidPeriodCharts.AbsoluteFormSource p K B X P S Ω) where
  native : MathlibExt.CategoryTheory.NativeConnectionProperties.FormDifferentialSource
    (constantK p K B X P) S.regular (proKScalar p K B X P S k)
    (forms p K B X P S Ω) AΩ.differential
  original_source : ∀ (U : AnalyticProObjectSites.Etale p X.left)
    (A : RelativeAffinoid p X.hom U),
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    letI : RingHomCompTriple A.coordinates.toRingHom ((originalUnit p K B X P S).hom.app (op U)).hom
      (((originalUnit p K B X P S).hom.app (op U)).hom.comp A.coordinates.toRingHom) := ⟨rfl⟩
    ∀ w : (Ω.affinoid U A).omega,
      MathlibExt.CategoryTheory.NativeConnectionProperties.FormDifferentialSource.sections
        (constantK p K B X P) S.regular (proKScalar p K B X P S k)
        (forms p K B X P S Ω) AΩ.differential native ((etaleInclusion p X.left).op.obj (op U))
        (inverseUnitSemilinear p K B X P S Ω.oneForms (op U) (Ω.omega U A w)) =
      exteriorUnit S.regular (forms p K B X P S Ω) 2 ((etaleInclusion p X.left).op.obj (op U))
        (ExteriorAlgebra.powMapₛₗ 2
          (((originalUnit p K B X P S).hom.app (op U)).hom.comp A.coordinates.toRingHom)
          ((inverseUnitSemilinear p K B X P S Ω.oneForms (op U)).comp (Ω.omega U A))
          (RestrictScalars.addEquiv (ULift.{1} A.target.pair.ring) (ULift.{1} A.source.pair.ring) _
            ((Ω.affinoid U A).differential 1
              ((_root_.exteriorPower.oneEquiv (ULift.{1} A.source.pair.ring) (Ω.affinoid U A).omega).symm w))))

def filteredCoefficientMap (j : ℤ) :=
  (modulePullback (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
    S.regular (originalUnit p K B X P S)).map (M.filtration.pieces j).ι

/-- The BASE pro filtration is fixed to the native images of the original etale filtration. -/
structure FiltrationSource where
  filtration : CoefficientFiltration S.regular (coefficient p K B X P S Ω M)
  image_source : ∀ (j : ℤ) (U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ)
    (m : (coefficient p K B X P S Ω M).val.obj U),
    m ∈ (filtration.pieces j).toSubmodule.obj U ↔
      m ∈ LinearMap.range ((image.ι (filteredCoefficientMap p K B X P S Ω M j)).val.app U).hom

/-- All terms and all differential values are normalized before constructing higher outputs. -/
structure AbsoluteComplexSource where
  native : CochainComplex.Plus (Modules (constantK p K B X P))
  terms : ∀ n : ℕ, native.obj.X (n : ℤ) ≅
    term (constantK p K B X P) S.regular (proKScalar p K B X P S k)
      (coefficient p K B X P S Ω M) (forms p K B X P S Ω) n
  negative_zero : ∀ i : ℤ, i < 0 → IsZero (native.obj.X i)
  localTerm : ∀ (U : AnalyticProObjectSites.Etale p X.left)
    (A : RelativeAffinoid p X.hom U) (n : ℕ),
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    letI := Module.compHom (M.module.val.obj (op U)) A.coordinates.toRingHom
    (M.module.val.obj (op U) ⊗[ULift.{1} A.source.pair.ring]
      (⋀[ULift.{1} A.source.pair.ring]^n (M.localModel U A).quotient.omega)) →+
      (tensor S.regular (coefficient p K B X P S Ω M)
        (exterior S.regular (forms p K B X P S Ω) n)).val.obj ((etaleInclusion p X.left).op.obj (op U))
  local_source : ∀ (U : AnalyticProObjectSites.Etale p X.left)
    (A : RelativeAffinoid p X.hom U) (n : ℕ),
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    letI := Module.compHom (M.module.val.obj (op U)) A.coordinates.toRingHom
    letI : RingHomCompTriple A.coordinates.toRingHom ((originalUnit p K B X P S).hom.app (op U)).hom
      (((originalUnit p K B X P S).hom.app (op U)).hom.comp A.coordinates.toRingHom) := ⟨rfl⟩
    ∀ (m : M.module.val.obj (op U)) (w : ⋀[ULift.{1} A.source.pair.ring]^n (M.localModel U A).quotient.omega),
      localTerm U A n (m ⊗ₜ[ULift.{1} A.source.pair.ring] w) =
        generator S.regular (coefficient p K B X P S Ω M) (exterior S.regular (forms p K B X P S Ω) n)
          ((etaleInclusion p X.left).op.obj (op U))
          (inverseUnitSemilinear p K B X P S M.module (op U) m)
          (exteriorUnit S.regular (forms p K B X P S Ω) n ((etaleInclusion p X.left).op.obj (op U))
            (ExteriorAlgebra.powMapₛₗ n
              (((originalUnit p K B X P S).hom.app (op U)).hom.comp A.coordinates.toRingHom)
              ((inverseUnitSemilinear p K B X P S Ω.oneForms (op U)).comp (M.localModel U A).omega) w))
  differential_source : ∀ (U : AnalyticProObjectSites.Etale p X.left)
    (A : RelativeAffinoid p X.hom U),
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    letI := Module.compHom (M.module.val.obj (op U)) A.coordinates.toRingHom
    ∀ (n : ℕ) (x : M.module.val.obj (op U) ⊗[ULift.{1} A.source.pair.ring]
      (⋀[ULift.{1} A.source.pair.ring]^n (M.localModel U A).quotient.omega)),
      (((terms (n + 1)).hom.val.app ((etaleInclusion p X.left).op.obj (op U))).hom)
        (((native.obj.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).val.app ((etaleInclusion p X.left).op.obj (op U))).hom
          (((terms n).inv.val.app ((etaleInclusion p X.left).op.obj (op U))).hom
            (localTerm U A n x))) =
      localTerm U A (n + 1)
        (RestrictScalars.addEquiv (ULift.{1} A.target.pair.ring) (ULift.{1} A.source.pair.ring) _
          (((M.localModel U A).quotient.extended (M.module.val.obj (op U))
            (M.localModel U A).connection).toLinearMap n x))
  zero : (restrict (constantK p K B X P) S.regular (proKScalar p K B X P S k)).obj
      (coefficient p K B X P S Ω M) ≅ native.obj.X 0
  one : native.obj.X 1 ≅ (restrict (constantK p K B X P) S.regular (proKScalar p K B X P S k)).obj
    (tensor S.regular (coefficient p K B X P S Ω M) (forms p K B X P S Ω))
  zero_source : ∀ U m, ((terms 0).hom.val.app U).hom ((zero.hom.val.app U).hom m) =
    generator S.regular (coefficient p K B X P S Ω M) (exterior S.regular (forms p K B X P S Ω) 0) U m
      (exteriorUnit S.regular (forms p K B X P S Ω) 0 U
        (_root_.exteriorPower.ιMulti (S.regular.obj.obj U) 0 (fun i => i.elim0)))
  one_source : ∀ U m w,
    (one.hom.val.app U).hom ((terms 1).inv.val.app U
      (generator S.regular (coefficient p K B X P S Ω M) (exterior S.regular (forms p K B X P S Ω) 1) U m
        (exteriorUnit S.regular (forms p K B X P S Ω) 1 U
          ((_root_.exteriorPower.oneEquiv (S.regular.obj.obj U) ((forms p K B X P S Ω).val.obj U)).symm w)))) =
    generator S.regular (coefficient p K B X P S Ω M) (forms p K B X P S Ω) U m w

def AbsoluteComplexSource.connectionMap (A : AbsoluteComplexSource p K B X P S Ω M k) :
    (restrict (constantK p K B X P) S.regular (proKScalar p K B X P S k)).obj
      (coefficient p K B X P S Ω M) ⟶
    (restrict (constantK p K B X P) S.regular (proKScalar p K B X P S k)).obj
      (tensor S.regular (coefficient p K B X P S Ω M) (forms p K B X P S Ω)) :=
  A.zero.hom ≫ A.native.obj.d 0 1 ≫ A.one.hom

def AbsoluteComplexSource.connection (A : AbsoluteComplexSource p K B X P S Ω M k)
    (U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ) :
    (coefficient p K B X P S Ω M).val.obj U →+
      (tensor S.regular (coefficient p K B X P S Ω M) (forms p K B X P S Ω)).val.obj U :=
  (((A.one.hom.val.app U).hom.comp ((A.native.obj.d 0 1).val.app U).hom).comp
    (A.zero.hom.val.app U).hom).toAddMonoidHom

end MathlibExt.AlgebraicGeometry.AnalyticAbsoluteDeRhamSources
