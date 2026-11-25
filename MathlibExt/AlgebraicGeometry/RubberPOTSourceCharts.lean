/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FramedRubberQuotientCharts
public import MathlibExt.AlgebraicGeometry.LiLiftedSourceCechModels

/-!
# Actual affine rubber points with the full Li construction

The source point is an actual framed lift of the specified rubber point,
on an actual affine presentation of its scheme. Its marked curve, map,
parameters, source classification, universal extension, all local lifted
maps, coefficient Cech complex and torus Lie quotient are retained.
Source: Jun Li arXiv:math/0110113v1, Section1; JPPZ
arXiv:1602.04705v2, Section0.2.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RubberPOTSourceCharts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels ExpansionParameterModels RubberMapFamilies RubberModuliStackModels
open StackCycleGeometry

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  {g n : ℕ} (a : Fin n → ℤ) (B : RubberModuliModel O P D R S (g := g) a)

def familyAt {m : ℕ} (H : FramedRubberModuliModels.Model O P D R S m (g := g) a)
    (T : Over (Spec (.of k))) (x : H.stack.Fibre T) := ((H.family T).obj x).obj

structure Chart (U : Over (Spec (.of k))) (y : B.stack.Fibre U) where
  ring : Type
  [commRing : CommRing ring]
  [algebra : Algebra k ring]
  [finiteType : _root_.Algebra.FiniteType k ring]
  presentation : Over.mk (Spec.algebraMap k ring) ≅ U
  length : ℕ
  torus : TorusTheory k (length + 1)
  scaling : RubberStandardScalingModels.StandardAction O P D R S length torus
  framed : FramedRubberModuliModels.Model O P D R S length (g := g) a
  forget : FramedRubberModuliModels.Forget O P D R S length a framed B
  quotient : FramedRubberQuotientCharts.Model O P D R S length torus scaling a framed B forget
  point : framed.stack.Fibre (Over.mk (Spec.algebraMap k ring))
  rubber : (component forget.map (Over.mk (Spec.algebraMap k ring))).obj point ≅
    (pull B.stack presentation.hom).obj y
  source : LiMarkedCurveExtensions.Classification
    (familyAt O P D R S a framed (Over.mk (Spec.algebraMap k ring)) point).rubber.curve
  universal : LiUniversalSourceExtensions.Data
    (familyAt O P D R S a framed (Over.mk (Spec.algebraMap k ring)) point).rubber.curve source
  cover : LiGeometricCechModels.Cover
    (p := (familyAt O P D R S a framed (Over.mk (Spec.algebraMap k ring)) point).rubber.curve.π)
    (q := (S.chart length).scheme.hom)
    (f := FramedRubberFamilies.totalMap O P D R S length a
      (familyAt O P D R S a framed (Over.mk (Spec.algebraMap k ring)) point))
  geometry : LiGeometricCechModels.Geometry (S.chart length).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S length)
    (RubberLieQuotientComplexes.parameters P R S length) cover
  coefficients : LiCechCoefficientModels.Model (S.chart length).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S length)
    (RubberLieQuotientComplexes.parameters P R S length) cover geometry
  lifts : ∀ i : Fin cover.count, LiLiftedSourceCechModels.Lift O P D R S length a
    (familyAt O P D R S a framed (Over.mk (Spec.algebraMap k ring)) point).rubber.curve
    (FramedRubberFamilies.totalMap O P D R S length a
      (familyAt O P D R S a framed (Over.mk (Spec.algebraMap k ring)) point)) cover source universal i
  system : LiLiftedSourceCechModels.System O P D R S length a
    (familyAt O P D R S a framed (Over.mk (Spec.algebraMap k ring)) point).rubber.curve
    (FramedRubberFamilies.totalMap O P D R S length a
      (familyAt O P D R S a framed (Over.mk (Spec.algebraMap k ring)) point))
    cover geometry coefficients source universal lifts
  lie : RubberLieQuotientComplexes.LieAction O P D R S length torus scaling cover geometry
    (coefficients.localModel (ModuleCat.of ring ring)) (system.complex (ModuleCat.of ring ring))
  log_eq : lie.log = system.log (ModuleCat.of ring ring)

attribute [instance] Chart.commRing Chart.algebra Chart.finiteType

def complex {U : Over (Spec (.of k))} {y : B.stack.Fibre U} (C : Chart O P D R S a B U y) :
    CochainComplex (ModuleCat.{0} C.ring) ℤ :=
  RubberLieQuotientComplexes.quotientComplex O P D R S C.length C.torus C.scaling
    C.cover C.geometry (C.coefficients.localModel (ModuleCat.of C.ring C.ring))
    (C.system.complex (ModuleCat.of C.ring C.ring)) C.lie

def ringMap {U : Over (Spec (.of k))} {y : B.stack.Fibre U} (C : Chart O P D R S a B U y) :
    Γ(U.left, ⊤) →+* C.ring :=
  ((Scheme.ΓSpecIso (.of C.ring)).hom.hom).comp C.presentation.hom.left.appTop.hom

structure Refinement (U : Over (Spec (.of k))) (y : B.stack.Fibre U) where
  scheme : Over (Spec (.of k))
  map : scheme ⟶ U
  etale : Etale map.left
  covering : Function.Surjective map.left
  source : Chart O P D R S a B scheme ((pull B.stack map).obj y)

end MathlibExt.AlgebraicGeometry.RubberPOTSourceCharts
