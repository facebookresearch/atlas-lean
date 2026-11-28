/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFramedLambdaFamilies
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The actual general linear frame scheme

GL_n is the native Spec of the actual matrix-coordinate polynomial ring
localized at its determinant. The displayed coordinate sections are its
literal localized matrix entries. A frame automorphism of O_T^n is tested
by its native coproduct inclusion/projection matrix entries on O_T(T).
The group and frame-point construction targets must match those entries
on every complex scheme T, including nonaffine and nonreduced schemes.

Ordinary pullback of a frame is conjugation by the existing normalized
free-bundle pullback comparison. No freely selected GL_n carrier or
pointwise group action is used.

Source: Simpson, alg-geom/9604005v1, Proposition 4.1 (change of frame);
Stacks Project, general linear group and frame bundles. Native polynomial,
determinant, localization, Spec and module primitives are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0; imported
relative-frame modules retain their Stacks/Mathlib attribution.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralLinearFrameSchemes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open PerverseSheaves RelativeFramedLambdaFamilies CurveVectorBundles CoherentCurveLinearSeries

abbrev MatrixPolynomial (n : ℕ) := MvPolynomial (Fin n × Fin n) ℂ

def genericDeterminant (n : ℕ) : MatrixPolynomial n :=
  Matrix.det (fun i j : Fin n ↦ MvPolynomial.X (i, j))

abbrev MatrixFrameRing (n : ℕ) := Localization.Away (genericDeterminant n)

def frameScheme (n : ℕ) : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MatrixFrameRing n))))

def coordinate (n : ℕ) (i j : Fin n) : Γ((frameScheme n).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MatrixFrameRing n))).inv.hom
    (algebraMap (MatrixPolynomial n) (MatrixFrameRing n) (MvPolynomial.X (i, j)))

def coordinateProjection (T : ComplexScheme) (n : ℕ) (i : Fin n) :
    trivialBundle T.left n ⟶ structureModule T.left :=
  Sigma.desc (fun j : Fin n ↦ if j = i then 𝟙 (structureModule T.left) else 0)

def frameCoordinate (T : ComplexScheme) (n : ℕ) (g : Aut (trivialBundle T.left n))
    (i j : Fin n) : Γ(T.left, ⊤) := by
  let f := Sigma.ι (fun _ : Fin n ↦ structureModule T.left) j ≫ g.asIso.hom ≫
    coordinateProjection T n i
  exact (f.val.app (op (⊤ : T.left.Opens))).hom (1 : Γ(T.left, ⊤))

def frameMatrix (T : ComplexScheme) (n : ℕ) (g : Aut (trivialBundle T.left n)) :
    Matrix (Fin n) (Fin n) Γ(T.left, ⊤) := fun i j ↦ frameCoordinate T n g i j

def pullFrame {S T : ComplexScheme} (f : S ⟶ T) (n : ℕ)
    (I : FreePullbackComparison f n) (g : Aut (trivialBundle T.left n)) :
    Aut (trivialBundle S.left n) :=
  Aut.of (I.iso.symm ≪≫ (Scheme.Modules.pullback f.left).mapIso g.asIso ≪≫ I.iso)

/-- The scheme is fixed; only its normalized native group/frame providers
remain construction targets. All test schemes and frame matrices are actual. -/
class FrameTheory (n : ℕ) where
  [group : GrpObj (frameScheme n)]
  points : ∀ T : ComplexScheme, (T ⟶ frameScheme n) ≃ Aut (trivialBundle T.left n)
  identity : ∀ T, points T (toUnit T ≫ η[frameScheme n]) = 1
  multiply : ∀ (T : ComplexScheme) (f g : T ⟶ frameScheme n),
    points T (CartesianMonoidalCategory.lift f g ≫ μ[frameScheme n]) = points T f * points T g
  coordinates : ∀ (T : ComplexScheme) (f : T ⟶ frameScheme n) (i j : Fin n),
    f.left.appTop.hom (coordinate n i j) = frameCoordinate T n (points T f) i j
  naturality : ∀ {S T : ComplexScheme} (f : S ⟶ T) (I : FreePullbackComparison f n)
      (g : T ⟶ frameScheme n), points S (f ≫ g) = pullFrame f n I (points T g)

attribute [instance_reducible, instance] FrameTheory.group

end MathlibExt.AlgebraicGeometry.GeneralLinearFrameSchemes
