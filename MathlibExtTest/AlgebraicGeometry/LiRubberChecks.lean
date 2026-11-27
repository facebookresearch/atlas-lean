/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.ExpandedTargetChainGeometry
import MathlibExt.AlgebraicGeometry.LiCechChartModules
import MathlibExt.AlgebraicGeometry.LiLiftedSourceCechModels

/-!
# Regression checks for expanded targets and Li charts

* The first ruled component of an expansion is attached to the original target along its
  infinity section, whose normal there is `Nᵛ` (dual to the target-side normal `N`).
* A boundary-mode Li chart meets no other boundary divisor.
* The overlap lift data measure differences in the universal extension's coefficients: the
  universal element `inr x` has coefficient `1 ⊗ x`, not a rescaled multiple.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry

namespace LiRubberChecksTest

section Expansion

open ExpandedTargetChainGeometry RelativeProjectiveLineModels

variable {k : Type} [Field k] (P : RelativePair (k := k))
  (R : ProjectiveLine P.divisor.left (normalLineModule P))

/-- The original target is glued to the first ruled component at its infinity section. -/
example {m : ℕ} (E : ExpandedSpecialFibre P R m) (h : 0 < m) :
    P.inclusion ≫ E.original = ruledInfinity P R ≫ E.ruled ⟨0, h⟩ := E.first h

/-- At that section the ruled side has normal `Nᵛ`, dual to the target-side normal `N`, so the
two normals multiply to the trivial bundle (the zero section, with normal `N`, would not). -/
example : NativeLineDuals.dualModule P.divisor.left R.infinityNormal.conormal ≅
    NativeLineDuals.dualModule P.divisor.left (normalLineModule P) := R.infinity_normal

/-- The exposed boundary of a nonempty expansion is the zero section of the last component. -/
example {m : ℕ} (E : ExpandedSpecialFibre P R m) (h : 0 < m) :
    E.boundary = ruledZero P R ≫ E.ruled ⟨m - 1, by omega⟩ := E.last h

end Expansion

section Charts

open LiCechChartModules LiAffineMapCharts

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
  {C X : Scheme.{0}} {p : C ⟶ Spec (.of A)} {q : X ⟶ Spec (.of k)} {f : C ⟶ X}
  {Z : Scheme.{0}} (g : X ⟶ Z) {b m : ℕ} (J : Fin b → X.IdealSheafData) (t : Fin m → Γ(X, ⊤))

/-- Two-end regression: a chart in boundary mode for the end `i` meets no other end `j`, so
directions moving the other end are not admitted on it. -/
example {a : Chart p q f} (i : Fin b) (o : Boundary a (J i) m)
    (pr : ProjectionBinding g o.ordinary.targetProjection) (pt : PrimeSpectrum a.source)
    (hp : algebraMap a.target a.source o.coordinate ∈ pt.asIdeal)
    (hpar : o.ordinary.targetParameter = parameterValue t a)
    (h : Mode.AvoidsUnselected g J t (Mode.boundary i o pr pt hp hpar)) (j : Fin b) (hj : j ≠ i) :
    ((J j).comap a.targetMap).comap (Spec.algebraMap a.target a.source) = ⊤ :=
  h j hj

end Charts

section Overlaps

open ExpandedTargetChainGeometry StandardRelativeExpansionModels RelativeProjectiveLineModels
open CoherentCurveLinearSeries MarkedCurveStabilization
open LiLiftedSourceCechModels LiUniversalSourceExtensions LiMarkedCurveExtensions
open scoped Simplicial TensorProduct

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm
  LiMarkedCurveExtensions.oppositeTower

variable {k : Type} [Field k]
  {O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k)))}
  {P : RelativePair (k := k)} {D : RubberMapFamilies.OriginalRubberPair O P}
  {R : ProjectiveLine P.divisor.left (normalLineModule P)} {S : StandardSystem P R} {m : ℕ}
  {A : Type} [CommRing A] [Algebra k A] {n genus : ℕ}
  {a : Fin n → ℤ} {F : MarkedFamily (Spec (.of A)) n genus}
  {f : F.X ⟶ (S.chart m).scheme.left}
  {L : LiGeometricCechModels.Cover (p := F.π) (q := (S.chart m).scheme.hom) (f := f)}
  {G : LiGeometricCechModels.Geometry (S.chart m).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S m)
    (RubberLieQuotientComplexes.parameters P R S m) L}
  {C : LiMarkedCurveExtensions.Classification F}
  {U : LiUniversalSourceExtensions.Data F C}
  {lift : ∀ i : Fin L.count, Lift O P D R S m a F f L C U i}

/-- A nonzero lift difference coming from a universal coefficient `v` is measured as exactly
`1 ⊗ v` on the overlap (the overlap's base is the pulled-back universal split base), not as a
rescaled multiple. -/
example {t : Fin 2 → Fin L.count} (o : Overlap O P D R S m a F f L G C U lift t)
    (s : (G.chart ⦋1⦌ t).target) (v : rightDual C.matrix)
    (hv : o.pair.first s - o.pair.second s = o.globalBase (TrivSqZeroExt.inr v)) :
    LiLocalLiftDifferences.differenceValue (RubberLieQuotientComplexes.parameters P R S m)
        (G.chart ⦋1⦌ t) (rightDual C.matrix) o.extensionData o.pair s =
      LiAffineMapCharts.baseCoefficientMap (G.chart ⦋1⦌ t) (rightDual C.matrix) (1 ⊗ₜ[A] v) := by
  rw [← o.extensionData.base_coefficient (1 ⊗ₜ[A] v)]
  unfold LiLocalLiftDifferences.differenceValue
  congr 2
  exact Subtype.ext (hv.trans (o.global_coefficient v))

end Overlaps

end LiRubberChecksTest
