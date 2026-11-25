/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicFinitePointNormModels

/-!
# Norm classes and heights of actual closed-point cycles

Cycles are finitely supported integer coefficients on the actual closed
scheme points of X. A second presentation of the same residue field cannot
create a second cycle generator. The residue scalar map is the native
global-section/evaluation composite of the original structure morphism.

Every norm source uses Spec of that exact residue field, the canonical
fromSpecResidueField map, the actual line fibre, complete Artinian tensor
factors and source-normalized norm models. The cycle intersection is the
coefficient sum of these norm-line classes; its degree is the coefficient
sum of the actual residue-field degrees. Normalized height requires the
degree to be nonzero, and uses this same degree.

Source: Yuan--Zhang, arXiv:2105.13587v9, Section 5.3.1, printed p152.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicClosedCycleHeights

open CategoryTheory _root_.AlgebraicGeometry Module
open PlacewiseMetrizedLineModels AdelicSemipositiveClosures
open AdelicPicardVectors FinitePointNormLines AdelicFinitePointNormModels
open MeasuredLinePointHeights

variable {K : Type} [Field K] (X : Over (Spec (.of K)))

/-- Cycle generators are the actual closed scheme points. -/
abbrev ClosedSchemePoint := {p : X.left | IsClosed ({p} : Set X.left)}

/-- The original scalar map into the actual residue field of this point. -/
def residueScalars (p : ClosedSchemePoint X) : K →+* X.left.residueField p.val :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation p.val).hom

@[instance_reducible] def residueAlgebra (p : ClosedSchemePoint X) :
    Algebra K (X.left.residueField p.val) := (residueScalars X p).toAlgebra

attribute [local instance] residueAlgebra

/-- A finite dictionary for the canonical closed point, with its literal residue field. -/
structure NativeClosedPoint (p : ClosedSchemePoint X) where
  [finite : FiniteDimensional K (X.left.residueField p.val)]
  point : ClosedPoint (K := K) (E := X.left.residueField p.val) X
  normalized : point.map.left = X.left.fromSpecResidueField p.val

/-- All closed points retain these same canonical residue maps and finite-degree witnesses. -/
structure ClosedPointSources where
  point : ∀ p : ClosedSchemePoint X, NativeClosedPoint X p

variable {X} (S : ClosedPointSources X)

/-- The residue-field degree is computed over the original base field. -/
def closedDegree (_S : ClosedPointSources X) (p : ClosedSchemePoint X) : ℕ := by
  letI := (_S.point p).finite
  exact Module.finrank K (X.left.residueField p.val)

/-- Integer zero-cycles on actual points, including negative and zero coefficients. -/
abbrev ZeroCycle (X : Over (Spec (.of K))) := ClosedSchemePoint X →₀ ℤ

/-- The degree uses the original closed residue field once per source point. -/
def cycleDegree (z : ZeroCycle X) : ℤ :=
  z.sum (fun p n ↦ n * (closedDegree S p : ℤ))

variable {A : AdelicField K} (G : GroundBase (K := K))
  (M : LineObject (A := A) (X := X) G)

/-- Native finite-point norm models at the entire canonical closed-point family. -/
structure ClosedPointNormSources where
  factors : ∀ p : ClosedSchemePoint X,
    letI := (S.point p).finite
    PlaceFactors (E := X.left.residueField p.val) A
  basis : ∀ p : ClosedSchemePoint X,
    Basis Unit (X.left.residueField p.val) (pointFibre M.line (S.point p).point.map)
  norm : ∀ p : ClosedSchemePoint X,
    letI := (S.point p).finite
    NormResult (factors p) (S.point p).point G M (basis p)

variable {G M} (N : ClosedPointNormSources S G M)

/-- The actual integrable norm line, with its source model metric. -/
def normObject (p : ClosedSchemePoint X) :
    LineObject (A := A) (X := BasePoint (K := K)) G := by
  letI := (S.point p).finite
  exact NormResult.asObject (N.factors p) (S.point p).point G M (N.basis p) (N.norm p)

/-- Unnormalized cycle intersection is the coefficient sum of the actual norm classes. -/
def cycleNormClass (z : ZeroCycle X) :
    PicardVector (A := A) (X := BasePoint (K := K)) (G := G) :=
  z.sum (fun p n ↦ (n : ℚ) • lineClass (normObject S N p))

/-- Normalization uses the same nonzero degree as the source cycle. -/
def vectorHeight (z : ZeroCycle X) (_nonzero : cycleDegree S z ≠ 0) :
    PicardVector (A := A) (X := BasePoint (K := K)) (G := G) :=
  (cycleDegree S z : ℚ)⁻¹ • cycleNormClass S N z

@[simp] theorem cycleDegree_zero : cycleDegree S (0 : ZeroCycle X) = 0 := by
  simp [cycleDegree]

@[simp] theorem cycleNormClass_zero :
    cycleNormClass S N (0 : ZeroCycle X) = 0 := by
  simp [cycleNormClass]

end MathlibExt.AlgebraicGeometry.AdelicClosedCycleHeights
