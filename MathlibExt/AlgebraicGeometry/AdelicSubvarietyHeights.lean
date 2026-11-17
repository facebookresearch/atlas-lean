/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NumericalAdelicIntersections
public import MathlibExt.AlgebraicGeometry.AdelicClosedCycleHeights

/-!
# Heights on actual closed images and generic-forgetful degree sources

An image is a genuine closed integral scheme with the kernel of the actual
source scheme map on EVERY regular-function open. A different field
presentation cannot create a new height generator. Projective vector height
is the class of the actual metric Deligne line on this same closed image,
divided by (dimension+1) times its actual coherent degree.

Numerical/Moriwaki height allows a nonproper closed subvariety. Its numerator
is the native limit of actual arithmetic/geometric model intersections with
the actual pulled-back base polarizations. Its denominator is the SAME
generic-forgetful model degree of the original restricted adelic line,
with genuine convergence. No independent open degree or height is supplied.

Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 5.3.1--5.3.3,
printed pp152--154. Norms and field/base normalizations retain the original
source classes, scalar maps, finite degrees and model denominators.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicSubvarietyHeights

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open AdelicPicardVectors AdelicSemipositiveClosures PlacewiseMetrizedLineModels
open MetricDelignePairingModels GlobalBoundedDeterminantModels RelativeDeterminantPairings
open ModelIntersectionDegrees AdelicChernLimits

variable {K : Type} [Field K] {A : AdelicField K} {X T : Over (Spec (.of K))}

/-- The actual closed subvariety is retained even when it is nonproper. -/
structure ClosedSubvariety (X : Over (Spec (.of K))) (n : ℕ) where
  scheme : Over (Spec (.of K))
  inclusion : scheme ⟶ X
  [closed : IsClosedImmersion inclusion.left]
  [integral : IsIntegral scheme.left]
  [finiteType : LocallyOfFiniteType scheme.hom]
  dimension : Order.krullDim scheme.left = n

/-- The same scheme-theoretic image fixes all regular-function kernels. -/
structure ClosedImage (u : T ⟶ X) (n : ℕ) extends ClosedSubvariety X n where
  factor : T ⟶ scheme
  factorization : factor ≫ inclusion = u
  image : Set.range inclusion.left = Set.range u.left
  kernel : ∀ U : X.left.Opens,
    RingHom.ker (inclusion.left.app U).hom = RingHom.ker (u.left.app U).hom
  [proper : IsProper scheme.hom]
  projective : IsProjectiveOver scheme.hom

def fieldStructure (Z : Over (Spec (.of K))) : Z ⟶ MeasuredLinePointHeights.BasePoint (K := K) :=
  Over.homMk Z.hom (by simp)

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

variable (G : GroundBase (K := K)) {n : ℕ} {u : T ⟶ X}
  (C : ClosedImage u n) (M : LineObject (A := A) (X := X) G)

/-- The algebraic degree and metric pairing are both on the actual SAME closed image. -/
structure VectorSources where
  restriction : PullbackObject G C.inclusion M
  degree : DegreeData C.scheme n (fun _ : Fin n ↦ restriction.asObject.line)
  determinant : DeterminantSources
  presentations : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Spec (.of K)),
    Presentations C.scheme.hom (fun _ : Fin (n+1) ↦ restriction.asObject.line) R a
  deligne : DeligneLine determinant C.scheme.hom n
    (fun _ : Fin (n+1) ↦ restriction.asObject.line) presentations
  symbols : SymbolAtlas G (fieldStructure C.scheme) n (fun _ ↦ restriction.asObject)
    determinant presentations deligne
  recursion : RecursionSources symbols
  metric : MetricResult symbols recursion

variable {G C M} (S : VectorSources G C M)

def closedDegree : ℤ := mixedDegree S.degree

/-- The numerator is the actual metric Deligne class, on the original field point. -/
def deligneClass : PicardVector (A := A) (X := MeasuredLinePointHeights.BasePoint (K := K)) (G := G) :=
  lineClass S.metric.asObject

/-- Projective vector height uses (dimension+1) times the SAME nonzero coherent degree. -/
def vectorHeight (_nonzero : closedDegree S ≠ 0) :
    PicardVector (A := A) (X := MeasuredLinePointHeights.BasePoint (K := K)) (G := G) :=
  (((n+1 : ℕ) : ℚ) * (closedDegree S : ℚ))⁻¹ • deligneClass S

variable (G : GroundBase (K := K)) (Z : ClosedSubvariety X n)
  (M : LineObject (A := A) (X := X) G) (b : ℕ+)
  (H : Fin (b-1) → LineObject (A := A) (X := MeasuredLinePointHeights.BasePoint (K := K)) G)

/-- Nonproper numerical sources retain genuine model limits and actual base pullbacks. -/
structure NumericalSources where
  restriction : PullbackObject G Z.inclusion M
  polarization : ∀ i, PullbackObject G (fieldStructure Z.scheme) (H i)
  degree : GenericModelSources G (fun _ : Fin n ↦ restriction.asObject)
  degreeConverges : GenericDegreeConvergence degree
  numerator : NumericalAdelicIntersections.Sources G
    (Fin.addCases (fun _ : Fin (n+1) ↦ restriction.asObject) (fun i : Fin (b-1) ↦ (polarization i).asObject))
  numeratorConverges : NumericalAdelicIntersections.Convergence numerator
  baseDimension : ∀ k, Order.krullDim (numerator.common k).base.scheme = (b : ℕ)

variable {G Z M b H} (N : NumericalSources G Z M b H)

def numericalDegree : ℝ := genericDegree N.degree

/-- The numerical height is the literal source intersection limit with the SAME degree. -/
def numericalHeight (_nonzero : numericalDegree N ≠ 0) : ℝ :=
  NumericalAdelicIntersections.intersection N.numerator /
    (((n+1 : ℕ) : ℝ) * numericalDegree N)

end MathlibExt.AlgebraicGeometry.AdelicSubvarietyHeights
