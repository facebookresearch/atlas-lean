/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts
public import MathlibExt.CategoryTheory.PeriodCoefficientComplexSources

/-!
# Actual pro-etale transfer of the original relative de Rham coefficient

The relative complex is the NATIVE COCHAIN inverse image of the
original affinoid-normalized etale complex. Its coefficients and forms
are the original native module inverse images. Degree identifications
are fixed on every original inverse-image, tensor and exterior unit.
The base connection on pro coefficients is computed from the native
degree-zero/one differential and those fixed identifications.

No higher bundle, filtration, Gauss--Manin connection or comparison
is an input. Native higher objects are computed after this transfer.

References: Scholze, arXiv:1205.3463v2, Definition 6.8, Remark 7.12 and
Theorem 8.8; completed Stacks 07I0 source; native Mathlib, Apache 2.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProEtaleDeRhamSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources AnalyticPeriodPullbackSources
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs
open MathlibExt.CategoryTheory.RingedComplexInverseImageSources
open MathlibExt.CategoryTheory.RingSheafModuleTensors

variable (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)
  (X Y : Over B.analytic) (f : X ⟶ Y)
  (PX : AnalyticProObjectSites.PointRealization p X.left) (PY : AnalyticProObjectSites.PointRealization p Y.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left PX) CommRingCat.{1}] [HasSheafify (proTopology p Y.left PY) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)]
  [(etaleInclusion p Y.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (proTopology p Y.left PY)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)).IsRightAdjoint]
  [((etaleInclusion p Y.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (proTopology p Y.left PY)).IsRightAdjoint]
  [IsIso (constantInverseMap (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (T := proTopology p X.left PX) (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
  [IsIso (constantInverseMap (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T := proTopology p Y.left PY) (etaleInclusion p Y.left) (WittVector p (BaseField.residueField p K)))]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) AddCommGrpCat.{1}]
  [(AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify (proTopology p X.left PX) AddCommGrpCat.{1}]
  [(proTopology p X.left PX).WEqualsLocallyBijective AddCommGrpCat.{1}]
  (SX : QualifiedStructuralPeriodSites.Source p K B X PX) (SY : QualifiedStructuralPeriodSites.Source p K B Y PY)
  (E : EtaleBaseChangeSource p f.left) (Q : ProBaseChangeSource p f.left E)
  [E.functor.IsContinuous (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)]
  [(E.functor.sheafPushforwardContinuous CommRingCat.{1} (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)).IsRightAdjoint]
  [Q.functor.IsContinuous (proTopology p Y.left PY) (proTopology p X.left PX)]
  [(Q.functor.sheafPushforwardContinuous CommRingCat.{1} (proTopology p Y.left PY) (proTopology p X.left PX)).IsRightAdjoint]
  (N : RingSquare (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
    E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left))

def relativeRing := inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular
def relativeScalar : relativeRing p K B X Y f PX PY SY E Q ⟶ SX.regular :=
  inverseScalar (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular SX.regular (originalMap p K B X Y f PX PY SX SY E Q N)

def originalUnit := AnalyticPerfectoidPeriodCharts.originalRingUnit p K B X PX SX

variable [(modulePushforward (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
  SX.regular (originalUnit p K B X PX SX)).IsRightAdjoint]
  (Ω : AnalyticRelativeDeRhamSources.DifferentialSource p f.left SX.regularSheaf)
  (M : AnalyticRelativeDeRhamSources.BaseCoefficientInput p f.left SX.regularSheaf Ω)
  (D : AnalyticRelativeDeRhamSources.FilteredDeRhamSource p f.left E SX.regularSheaf SY.regularSheaf Ω M)

local instance (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ) :
    CommRing ((moduleRing (regularEtale p X.left SX.regularSheaf)).obj.obj U) :=
  inferInstanceAs (CommRing ((regularEtale p X.left SX.regularSheaf).obj.obj U))

local instance (U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ) :
    CommRing ((moduleRing SX.regular).obj.obj U) :=
  inferInstanceAs (CommRing (SX.regular.obj.obj U))

def coefficient := (modulePullback (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
  SX.regular (originalUnit p K B X PX SX)).obj M.module
def forms := (modulePullback (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
  SX.regular (originalUnit p K B X PX SX)).obj Ω.oneForms

def inverseUnitSemilinear (M₀ : Modules (regularEtale p X.left SX.regularSheaf))
    (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ) : M₀.val.obj U →ₛₗ[((originalUnit p K B X PX SX).hom.app U).hom]
    (((modulePullback (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
      SX.regular (originalUnit p K B X PX SX)).obj M₀).val.obj ((etaleInclusion p X.left).op.obj U)) where
  toFun m := (((moduleAdjunction (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
    SX.regular (originalUnit p K B X PX SX)).unit.app M₀).val.app U).hom m
  map_add' m n := map_add _ _ _
  map_smul' r m := (((moduleAdjunction (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
    SX.regular (originalUnit p K B X PX SX)).unit.app M₀).val.app U).hom.map_smul r m

/-- The relative differential is the original continuous etale derivation carried through the
native original ring/module inverse-image units. No global raw Kaehler identification is used. -/
structure FormSource where
  differential : ∀ U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ,
    SX.regular.obj.obj U →+ (forms p K B X Y f PX SX Ω).val.obj U
  natural : ∀ {U V : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ} (a : U ⟶ V) r,
    differential V ((SX.regular.obj.map a).hom r) =
      (forms p K B X Y f PX SX Ω).val.map a (differential U r)
  leibniz : ∀ U a b, differential U (a * b) = a • differential U b + b • differential U a
  original_source : ∀ (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ)
    (a : (regularEtale p X.left SX.regularSheaf).obj.obj U),
    differential ((etaleInclusion p X.left).op.obj U) (((originalUnit p K B X PX SX).hom.app U).hom a) =
      inverseUnitSemilinear p K B X PX SX Ω.oneForms U (Ω.differential U a)

variable [(modulePushforward (etaleInclusion p X.left)
  (inverseRing (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) E.functor (regularEtale p Y.left SY.regularSheaf))
  (inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor
    (inverseRing (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T := proTopology p Y.left PY)
      (etaleInclusion p Y.left) (regularEtale p Y.left SY.regularSheaf)))
  (transferScalar (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX) E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left) N
    (regularEtale p Y.left SY.regularSheaf))).IsRightAdjoint]
  [(cochainTransfer (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX) E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left) N
    (regularEtale p Y.left SY.regularSheaf)).PreservesMonomorphisms]

def native : FilteredComplex (relativeRing p K B X Y f PX PY SY E Q) :=
  filteredTransfer (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX) E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left) N
    (regularEtale p Y.left SY.regularSheaf) D.native

def originalCoefficientUnit (n : ℕ) (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ)
    (m : M.module.val.obj U)
    (w : ⋀[(regularEtale p X.left SX.regularSheaf).obj.obj U]^n (Ω.oneForms.val.obj U)) :
    ((native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
      (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)).total.obj.X (n : ℤ)).val.obj
        ((etaleInclusion p X.left).op.obj U) :=
  (((moduleAdjunction (etaleInclusion p X.left)
    (inverseRing (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
      (T := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) E.functor (regularEtale p Y.left SY.regularSheaf))
    (inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor
      (inverseRing (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T := proTopology p Y.left PY)
        (etaleInclusion p Y.left) (regularEtale p Y.left SY.regularSheaf)))
    (transferScalar (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
      (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
      (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
      E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left) N
        (regularEtale p Y.left SY.regularSheaf))).unit.app (D.native.total.obj.X (n : ℤ))).val.app U).hom
    (((D.terms n).inv.val.app U).hom
      (show ((restrict (AnalyticRelativeDeRhamSources.relativeRing p f.left E SY.regularSheaf)
        (regularEtale p X.left SX.regularSheaf) (AnalyticRelativeDeRhamSources.relativeScalar p f.left E SX.regularSheaf SY.regularSheaf)).obj
          (tensor (regularEtale p X.left SX.regularSheaf) M.module
            (exterior (regularEtale p X.left SX.regularSheaf) Ω.oneForms n))).val.obj U from
        generator (regularEtale p X.left SX.regularSheaf) M.module
          (exterior (regularEtale p X.left SX.regularSheaf) Ω.oneForms n) U m
            (exteriorUnit (regularEtale p X.left SX.regularSheaf) Ω.oneForms n U w)))

/-- All term maps refer to the actual transferred original complex and original inverse images. -/
structure Source where
  terms : ∀ n : ℕ, (native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)).total.obj.X (n : ℤ) ≅
    (restrict (relativeRing p K B X Y f PX PY SY E Q) SX.regular
      (relativeScalar p K B X Y f PX PY SX SY E Q N)).obj
        (tensor SX.regular (coefficient p K B X Y f PX SX Ω M) (exterior SX.regular (forms p K B X Y f PX SX Ω) n))
  original_source : ∀ (n : ℕ) (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ)
    (m : M.module.val.obj U)
    (w : ⋀[(regularEtale p X.left SX.regularSheaf).obj.obj U]^n (Ω.oneForms.val.obj U)),
    ((terms n).hom.val.app ((etaleInclusion p X.left).op.obj U)).hom
      (originalCoefficientUnit p K B X Y f PX PY SX SY E Q N Ω M D n U m w) =
    (show ((restrict (relativeRing p K B X Y f PX PY SY E Q) SX.regular
      (relativeScalar p K B X Y f PX PY SX SY E Q N)).obj
        (tensor SX.regular (coefficient p K B X Y f PX SX Ω M)
          (exterior SX.regular (forms p K B X Y f PX SX Ω) n))).val.obj ((etaleInclusion p X.left).op.obj U) from
      generator SX.regular (coefficient p K B X Y f PX SX Ω M)
        (exterior SX.regular (forms p K B X Y f PX SX Ω) n) ((etaleInclusion p X.left).op.obj U)
          (inverseUnitSemilinear p K B X PX SX M.module U m)
          (exteriorUnit SX.regular (forms p K B X Y f PX SX Ω) n ((etaleInclusion p X.left).op.obj U)
            (ExteriorAlgebra.powMapₛₗ n ((originalUnit p K B X PX SX).hom.app U).hom
              (inverseUnitSemilinear p K B X PX SX Ω.oneForms U) w)))
  zero : (restrict (relativeRing p K B X Y f PX PY SY E Q) SX.regular
    (relativeScalar p K B X Y f PX PY SX SY E Q N)).obj (coefficient p K B X Y f PX SX Ω M) ≅
      (native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)).total.obj.X 0
  zero_source : ∀ (U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ)
    (m : (coefficient p K B X Y f PX SX Ω M).val.obj U),
    ((terms 0).hom.val.app U).hom ((zero.hom.val.app U).hom m) =
    (show ((restrict (relativeRing p K B X Y f PX PY SY E Q) SX.regular
      (relativeScalar p K B X Y f PX PY SX SY E Q N)).obj
        (tensor SX.regular (coefficient p K B X Y f PX SX Ω M) (exterior SX.regular (forms p K B X Y f PX SX Ω) 0))).val.obj U from
      generator SX.regular (coefficient p K B X Y f PX SX Ω M) (exterior SX.regular (forms p K B X Y f PX SX Ω) 0) U m
        (exteriorUnit SX.regular (forms p K B X Y f PX SX Ω) 0 U (_root_.exteriorPower.ιMulti (SX.regular.obj.obj U) 0 (fun i => i.elim0))))
  one : (native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)).total.obj.X 1 ≅
    (restrict (relativeRing p K B X Y f PX PY SY E Q) SX.regular
      (relativeScalar p K B X Y f PX PY SX SY E Q N)).obj
        (tensor SX.regular (coefficient p K B X Y f PX SX Ω M) (forms p K B X Y f PX SX Ω))
  one_source : ∀ (U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ)
    (m : (coefficient p K B X Y f PX SX Ω M).val.obj U) (w : (forms p K B X Y f PX SX Ω).val.obj U),
    (one.hom.val.app U).hom
      (((terms 1).inv.val.app U).hom
        (show ((restrict (relativeRing p K B X Y f PX PY SY E Q) SX.regular
          (relativeScalar p K B X Y f PX PY SX SY E Q N)).obj
            (tensor SX.regular (coefficient p K B X Y f PX SX Ω M) (exterior SX.regular (forms p K B X Y f PX SX Ω) 1))).val.obj U from
          generator SX.regular (coefficient p K B X Y f PX SX Ω M)
            (exterior SX.regular (forms p K B X Y f PX SX Ω) 1) U m
              (exteriorUnit SX.regular (forms p K B X Y f PX SX Ω) 1 U
                ((_root_.exteriorPower.oneEquiv (SX.regular.obj.obj U) ((forms p K B X Y f PX SX Ω).val.obj U)).symm w)))) =
    (show ((restrict (relativeRing p K B X Y f PX PY SY E Q) SX.regular
      (relativeScalar p K B X Y f PX PY SX SY E Q N)).obj
        (tensor SX.regular (coefficient p K B X Y f PX SX Ω M) (forms p K B X Y f PX SX Ω))).val.obj U from
      generator SX.regular (coefficient p K B X Y f PX SX Ω M) (forms p K B X Y f PX SX Ω) U m w)

namespace Source

variable (S : Source p K B X Y f PX PY SX SY E Q N Ω M D)

/-- The pro base connection is OUTPUT from the actual native transferred degree-zero differential. -/
def connection (U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ) :
    (coefficient p K B X Y f PX SX Ω M).val.obj U →+
      (tensor SX.regular (coefficient p K B X Y f PX SX Ω M) (forms p K B X Y f PX SX Ω)).val.obj U :=
  (((S.one.hom.val.app U).hom.comp
    (((native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)).total.obj.d 0 1).val.app U).hom).comp
      (S.zero.hom.val.app U).hom).toAddMonoidHom

end Source

section HigherOutputs

variable [HasSheafify (proTopology p Y.left PY) AddCommGrpCat.{1}]
  [(proTopology p Y.left PY).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [EnoughInjectives (Modules SY.regular)]
  [EnoughInjectives (Modules (relativeRing p K B X Y f PX PY SY E Q))]
  [(pushforward Q.functor SY.regular (relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)).IsRightAdjoint]

def derivedDeRham := MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs.derivedDeRham Q.functor SY.regular
  (relativeRing p K B X Y f PX PY SY E Q)
  (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
  (native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D))

def higherDeRham (i : ℤ) := MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs.higherDeRham Q.functor SY.regular
  (relativeRing p K B X Y f PX PY SY E Q)
  (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
  (native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)) i

def higherHodge (i j : ℤ) := MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs.higherHodge Q.functor SY.regular
  (relativeRing p K B X Y f PX PY SY E Q)
  (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
  (native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)) i j

def higherFiltration (i j : ℤ) := MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs.higherFiltration Q.functor SY.regular
  (relativeRing p K B X Y f PX PY SY E Q)
  (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
  (native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)) i j

def higherGraded (i j : ℤ) := MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs.higherGraded Q.functor SY.regular
  (relativeRing p K B X Y f PX PY SY E Q)
  (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
  (native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)) i j

end HigherOutputs

end MathlibExt.AlgebraicGeometry.ProEtaleDeRhamSources
