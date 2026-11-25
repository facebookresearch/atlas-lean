/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Chow/ProjectiveBundleFormula/Formula.lean`
(AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b), through the
ATLAS `MathlibExt/AlgebraicGeometry/AlgebraicBundleGeometry.lean` interface:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modification: the tautological quotient interface is specialized to polynomial Proj over a
number field, keeps the quotient compatibility on every test scheme, and pins K-point
coordinates by homogeneous-polynomial vanishing.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Group.Torsion
public import MathlibExt.NumberTheory.ProjectiveNorthcott
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes

/-!
# Normalized arithmetic heights of actual abelian-variety points

The projective target is the actual polynomial `Proj` scheme. Its
tautological line is characterized by its universal invertible-quotient
property, and the projective coordinate map is pinned by every homogeneous
polynomial's vanishing at the actual scheme point. A closed embedding gives
the very ample line on the abelian variety; symmetry is the actual inverse
pullback isomorphism of that line.

The naïve height is Mathlib's projective height in those coordinates,
divided by the number-field degree. The sequence defining the Néron–Tate
height is complete code below. Its convergence, quadraticity and positivity
are a separate Wanted construction, not assumed duplication bounds.

References: Gregory S. Call–Joseph H. Silverman, *Canonical heights on
varieties with morphisms*, Theorem 1.1, Example 1, Proposition 1.2,
Compositio Mathematica 89 (1993), pp. 166–169.
https://www.numdam.org/item/CM_1993__89_2_163_0.pdf
Hindry–Silverman, *Diophantine Geometry*, §B.5.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AbelianArithmeticHeights

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj _root_.AlgebraicGeometry
open CoherentCurveLinearSeries AlgebraicBundleGeometry SurfaceHilbertSchemes
open Filter
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K]

/-- The actual field-rational point object. -/
abbrev fieldPointObject : Over (Spec (CommRingCat.of.{0} K)) :=
  Over.mk (𝟙 _)

/-- The unique point of the actual spectrum of the field. -/
def fieldPoint : Spec (CommRingCat.of.{0} K) :=
  Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of K)))

/-- The tautological quotient line on the actual projective scheme, with
the quotient's universal property retained on every test scheme. -/
structure TautologicalLine (n : ℕ) where
  line : (projectiveSpace K n).left.Modules
  isLine : IsLineBundle line
  sections : Fin (n + 1) →
    (structureModule (projectiveSpace K n).left ⟶ line)
  [generating : Epi (Sigma.desc sections)]
  universal : ∀ (T : Over (Spec (CommRingCat.of K))) (M : T.left.Modules),
    IsLineBundle M →
      ∀ s : Fin (n + 1) → (structureModule T.left ⟶ M),
        Epi (Sigma.desc s) → ∃! f : T ⟶ projectiveSpace K n,
          ∃ e : (Scheme.Modules.pullback f.left).obj line ≅ M,
            ∀ j, pullbackSection f.left line (sections j) ≫ e.hom = s j

/-- Coordinates are tied to the actual image in polynomial Proj by all
homogeneous vanishing equations. This is not a free map to a vector space. -/
structure ProjectiveCoordinates (n : ℕ) where
  map : (fieldPointObject K ⟶ projectiveSpace K n) →
    Projectivization K (Fin (n + 1) → K)
  vanishing : ∀ (q : fieldPointObject K ⟶ projectiveSpace K n)
    (d : ℕ) (f : MvPolynomial (Fin (n + 1)) K),
    f.IsHomogeneous d →
      (f ∈ (q.left (fieldPoint K)).asHomogeneousIdeal ↔ f.eval (map q).rep = 0)

variable {K} (A : Over (Spec (CommRingCat.of.{0} K)))
  [GrpObj A] [IsCommMonObj A]

/-- Actual K-valued scheme points, with their internal additive group law. -/
abbrev RationalPoint := Additive (fieldPointObject K ⟶ A)

/-- A genuine symmetric very ample realization of the abelian variety. -/
structure SymmetricProjectiveModel where
  ambientDimension : ℕ
  tautological : TautologicalLine K ambientDimension
  coordinates : ProjectiveCoordinates K ambientDimension
  embedding : A ⟶ projectiveSpace K ambientDimension
  [closedEmbedding : IsClosedImmersion embedding.left]
  symmetric : Nonempty
    ((Scheme.Modules.pullback (ι[A]).left).obj
        ((Scheme.Modules.pullback embedding.left).obj tautological.line) ≅
      (Scheme.Modules.pullback embedding.left).obj tautological.line)

attribute [instance] SymmetricProjectiveModel.closedEmbedding

namespace SymmetricProjectiveModel

variable {A}
variable (M : SymmetricProjectiveModel A) [NumberField K]

/-- The actual projective point obtained from the fixed closed embedding. -/
def projectivePoint (P : RationalPoint A) :
    Projectivization K (Fin (M.ambientDimension + 1) → K) :=
  M.coordinates.map (P.toMul ≫ M.embedding)

/-- Absolute logarithmic Weil height of the actual embedded scheme point. -/
def naiveHeight (P : RationalPoint A) : ℝ :=
  Projectivization.logHeight (M.projectivePoint P) / (Module.finrank ℚ K : ℝ)

/-- The geometric multiplication-by-two sequence defining Néron–Tate height. -/
def heightSequence (P : RationalPoint A) (n : ℕ) : ℝ :=
  M.naiveHeight ((2 ^ n) • P) / 4 ^ n

/-- A normalized canonical (Néron–Tate) height: at every point it is the limit of the
multiplication-by-two height sequence, and it is nonnegative and satisfies the parallelogram
law, quadratic scaling and the torsion criterion (`height P = 0` exactly for torsion points). -/
structure CanonicalHeight where
  height : RationalPoint A → ℝ
  convergence : ∀ P, Tendsto (M.heightSequence P) atTop (𝓝 (height P))
  nonnegative : ∀ P, 0 ≤ height P
  parallelogram : ∀ P Q,
    height (P + Q) + height (P - Q) = 2 * height P + 2 * height Q
  scaling : ∀ (m : ℤ) P, height (m • P) = (m : ℝ) ^ 2 * height P
  torsion : ∀ P, height P = 0 ↔ IsOfFinAddOrder P

omit [IsCommMonObj A] in
/-- The defining limit fixes the height function uniquely. -/
theorem height_unique (H J : M.CanonicalHeight) : H.height = J.height := by
  funext P
  exact tendsto_nhds_unique (H.convergence P) (J.convergence P)

end SymmetricProjectiveModel

end MathlibExt.AlgebraicGeometry.AbelianArithmeticHeights
