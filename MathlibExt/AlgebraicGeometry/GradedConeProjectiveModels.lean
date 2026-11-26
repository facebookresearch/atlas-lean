/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralChowChernModels
public import MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Actual graded cones, projective completions and their O(1)

An affine cone is the actual Spec of a nonnegatively graded algebra
with degree zero its base ring and generation in degree one. The
completion is the literal Proj of A[z], where z has degree one and
the degree-n part is the span of z^j A_(n−j).

O(1) is normalized on every degree-one basic open D_+(a): the
homogeneous coordinate b becomes the actual regular function b/a.
The opens cover, so an unrelated line bundle cannot satisfy the
contract. No smoothness of the base or of the completion is required.

References: Fulton, Intersection Theory, §4.1 (cone Segre classes);
Behrend, arXiv:math/0507523v2, equation (3). Native Proj and homogeneous
localization use Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679.
This file defines the objects and normalization contracts; their
construction proofs are requested separately.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GradedConeProjectiveModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GlobalPerfectObstructionTheory LineBundleTaskContracts CoherentCurveLinearSeries
open IntegralChowChernModels

/-- The actual coordinate algebra of a cone, including its genuine grading. -/
structure AffineGradedCone (B : CommRingCat.{0}) where
  algebra : CommAlgCat.{0} B
  grade : ℕ → Submodule B algebra
  [grading : GradedRing grade]
  coefficient_injective : Function.Injective (algebraMap B algebra)
  degreeZero : ∀ a : algebra, a ∈ grade 0 ↔ ∃ b : B, algebraMap B algebra b = a
  generated : Algebra.adjoin B (grade 1 : Set algebra) = ⊤

attribute [instance] AffineGradedCone.grading

/-- A cone reindexing has its actual ring map, scalar map and degree preservation. -/
structure ConeReindex {B D : CommRingCat.{0}} (phi : B →+* D)
    (C : AffineGradedCone B) (E : AffineGradedCone D) where
  map : C.algebra →+* E.algebra
  coefficient : ∀ b : B, map (algebraMap B C.algebra b) =
    algebraMap D E.algebra (phi b)
  graded : ∀ (n : ℕ) (a : C.algebra), a ∈ C.grade n → map a ∈ E.grade n

/-- The cone's carrier and projection are actual affine schemes. -/
def affineCone {B : CommRingCat.{0}} (C : AffineGradedCone B) : Scheme :=
  Spec (.of C.algebra)

def affineProjection {B : CommRingCat.{0}} (C : AffineGradedCone B) :
    affineCone C ⟶ Spec B := Spec.algebraMap B C.algebra

/-- The literal degree n part of A[z], with z of degree one. -/
def completionGrade {B : CommRingCat.{0}} (C : AffineGradedCone B) (n : ℕ) :
    Submodule B (Polynomial C.algebra) :=
  Submodule.span B {p | ∃ (j : ℕ) (_hj : j≤n) (a : C.grade (n-j)),
    p = Polynomial.monomial j a.val}

/-- Only the native grading and the normalized degree-zero identification remain to construct. -/
structure CompletionGrading {B : CommRingCat.{0}} (C : AffineGradedCone B) where
  [grading : GradedRing (completionGrade C)]
  zeroEquiv : B ≃+* completionGrade C 0
  zero_normalized : ∀ b : B, (zeroEquiv b : Polynomial C.algebra) =
    Polynomial.C (algebraMap B C.algebra b)

/-- The genuine projective completion P(C⊕1), as native Proj(A[z]). -/
def completionProj {B : CommRingCat.{0}} {C : AffineGradedCone B}
    (G : CompletionGrading C) : Scheme := by
  letI := G.grading
  exact Proj (completionGrade C)

/-- Its structural map is native Proj→Spec(degree zero) followed by the fixed base map. -/
def completionProjection {B : CommRingCat.{0}} {C : AffineGradedCone B}
    (G : CompletionGrading C) : completionProj G ⟶ Spec B := by
  letI := G.grading
  exact Proj.toSpecZero (completionGrade C) ≫ Spec.map (CommRingCat.ofHom G.zeroEquiv.toRingHom)

/-- The standard degree-one affine open. -/
def degreeOneOpen {B : CommRingCat.{0}} {C : AffineGradedCone B}
    (G : CompletionGrading C) (a : completionGrade C 1) : (completionProj G).Opens := by
  letI := G.grading
  exact Proj.basicOpen (completionGrade C) a.val

/-- The actual regular function b/a in its homogeneous localization chart. -/
def coordinateRatio {B : CommRingCat.{0}} {C : AffineGradedCone B}
    (G : CompletionGrading C) (a b : completionGrade C 1) :
    Γ((degreeOneOpen G a).toScheme, ⊤) := by
  letI := G.grading
  exact (degreeOneOpen G a).topIso.inv
    ((Proj.awayToSection (completionGrade C) a.val).hom
      (HomogeneousLocalization.Away.mk (completionGrade C) a.property 1 b.val
        (by simp)))

/-- The line is fixed on all standard opens by the quotient convention b↦b/a. -/
structure CompletionLineModel {B : CommRingCat.{0}} {C : AffineGradedCone B}
    (G : CompletionGrading C) where
  module : (completionProj G).Modules
  isLine : AlgebraicBundleGeometry.IsLine module
  coordinate : completionGrade C 1 → Section module
  trivialization : ∀ a : completionGrade C 1,
    (Scheme.Modules.pullback (degreeOneOpen G a).ι).obj module ≅
      structureModule (degreeOneOpen G a).toScheme
  cover : ∀ x : completionProj G, ∃ a : completionGrade C 1, x ∈ degreeOneOpen G a
  normalized : ∀ a b : completionGrade C 1,
    (pullbackSection (degreeOneOpen G a).ι (coordinate b) ≫
      (trivialization a).hom).val.app (op ⊤)
        (1 : Γ((degreeOneOpen G a).toScheme, ⊤)) = coordinateRatio G a b

/-- Proj reindexing is fixed by the polynomial map of the same cone ring map. -/
structure CompletionReindex {B D : CommRingCat.{0}} {phi : B →+* D}
    {C : AffineGradedCone B} {E : AffineGradedCone D} (F : ConeReindex phi C E)
    (G : CompletionGrading C) (K : CompletionGrading E) where
  map : completionGrade C →+*ᵍ completionGrade E
  normalized : map.toRingHom = Polynomial.mapRingHom F.map
  irrelevant : letI := G.grading; letI := K.grading
    HomogeneousIdeal.irrelevant (completionGrade E) ≤
      (HomogeneousIdeal.irrelevant (completionGrade C)).map map

def completionMap {B D : CommRingCat.{0}} {phi : B →+* D}
    {C : AffineGradedCone B} {E : AffineGradedCone D} {F : ConeReindex phi C E}
    {G : CompletionGrading C} {K : CompletionGrading E} (R : CompletionReindex F G K) :
    completionProj K ⟶ completionProj G := by
  letI := G.grading
  letI := K.grading
  exact Proj.map R.map R.irrelevant

/-- The O(1) reindexing is pinned on every actual homogeneous coordinate. -/
structure CompletionLineReindex {B D : CommRingCat.{0}} {phi : B →+* D}
    {C : AffineGradedCone B} {E : AffineGradedCone D} {F : ConeReindex phi C E}
    {G : CompletionGrading C} {K : CompletionGrading E} (R : CompletionReindex F G K)
    (U : CompletionLineModel G) (V : CompletionLineModel K) where
  map : (Scheme.Modules.pullback (completionMap R)).obj U.module ≅ V.module
  normalized : ∀ a : completionGrade C 1,
    pullbackSection (completionMap R) (U.coordinate a) ≫ map.hom =
      V.coordinate ⟨R.map a.val,R.map.2 a.property⟩

/-- A global cone has actual affine graded-algebra views on every affine base map. -/
structure GlobalGradedCone (X : SchemeData) where
  total : SchemeData
  projection : total.scheme ⟶ X.scheme
  chart : ∀ (B : CommRingCat.{0}) (_f : Spec B ⟶ X.scheme.left), AffineGradedCone B
  comparison : ∀ (B : CommRingCat.{0}) (f : Spec B ⟶ X.scheme.left),
    pullback projection.left f ≅ affineCone (chart B f)
  overBase : ∀ (B : CommRingCat.{0}) (f : Spec B ⟶ X.scheme.left),
    (comparison B f).hom ≫ affineProjection (chart B f) = pullback.snd projection.left f
  reindex : ∀ (B D : CommRingCat.{0}) (phi : B →+* D)
    (f : Spec B ⟶ X.scheme.left) (g : Spec D ⟶ X.scheme.left)
    (_h : Spec.map (CommRingCat.ofHom phi) ≫ f = g), ConeReindex phi (chart B f) (chart D g)
  reindex_normalized : ∀ (B D : CommRingCat.{0}) (phi : B →+* D)
    (f : Spec B ⟶ X.scheme.left) (g : Spec D ⟶ X.scheme.left)
    (h : Spec.map (CommRingCat.ofHom phi) ≫ f = g),
    Spec.map (CommRingCat.ofHom (reindex B D phi f g h).map) ≫
      (comparison B f).inv ≫ pullback.fst projection.left f =
    (comparison D g).inv ≫ pullback.fst projection.left g

/-- A global completion is normalized to these actual Proj charts and the same O(1). -/
structure GlobalCompletionData {X : SchemeData} (C : GlobalGradedCone X) where
  total : SchemeData
  projection : total.scheme ⟶ X.scheme
  [proper : IsProper projection.left]
  hyperplane : total.scheme.left.Modules
  isLine : AlgebraicBundleGeometry.IsLine hyperplane
  grading : ∀ (B : CommRingCat.{0}) (f : Spec B ⟶ X.scheme.left),
    CompletionGrading (C.chart B f)
  localLine : ∀ (B : CommRingCat.{0}) (f : Spec B ⟶ X.scheme.left),
    CompletionLineModel (grading B f)
  comparison : ∀ (B : CommRingCat.{0}) (f : Spec B ⟶ X.scheme.left),
    pullback projection.left f ≅ completionProj (grading B f)
  overBase : ∀ (B : CommRingCat.{0}) (f : Spec B ⟶ X.scheme.left),
    (comparison B f).hom ≫ completionProjection (grading B f) = pullback.snd projection.left f
  lineComparison : ∀ (B : CommRingCat.{0}) (f : Spec B ⟶ X.scheme.left),
    (Scheme.Modules.pullback
      ((comparison B f).inv ≫ pullback.fst projection.left f)).obj hyperplane ≅
        (localLine B f).module

/-- Ring-normalized completion transitions and coordinate-normalized O(1) maps. -/
structure GlobalCompletionReindex {X : SchemeData} (C : GlobalGradedCone X)
    extends GlobalCompletionData C where
  reindex : ∀ (B D : CommRingCat.{0}) (phi : B →+* D)
    (f : Spec B ⟶ X.scheme.left) (g : Spec D ⟶ X.scheme.left)
    (h : Spec.map (CommRingCat.ofHom phi) ≫ f = g),
    CompletionReindex (C.reindex B D phi f g h) (grading B f) (grading D g)
  overlap : ∀ (B D : CommRingCat.{0}) (phi : B →+* D)
    (f : Spec B ⟶ X.scheme.left) (g : Spec D ⟶ X.scheme.left)
    (h : Spec.map (CommRingCat.ofHom phi) ≫ f = g),
    completionMap (reindex B D phi f g h) ≫
      ((comparison B f).inv ≫ pullback.fst projection.left f) =
    (comparison D g).inv ≫ pullback.fst projection.left g
  lineReindex : ∀ (B D : CommRingCat.{0}) (phi : B →+* D)
    (f : Spec B ⟶ X.scheme.left) (g : Spec D ⟶ X.scheme.left)
    (h : Spec.map (CommRingCat.ofHom phi) ≫ f = g),
    CompletionLineReindex (reindex B D phi f g h) (localLine B f) (localLine D g)

/-- The exact native pullback-comp/congruence diagram for the descended O(1). -/
def GlobalCompletionReindex.LineCoherence {X : SchemeData} {C : GlobalGradedCone X}
    (P : GlobalCompletionReindex C) (B D : CommRingCat.{0}) (phi : B →+* D)
    (f : Spec B ⟶ X.scheme.left) (g : Spec D ⟶ X.scheme.left)
    (h : Spec.map (CommRingCat.ofHom phi) ≫ f = g) : Prop :=
  (P.lineComparison D g).hom =
  (Scheme.Modules.pullbackCongr (P.overlap B D phi f g h).symm).hom.app P.hyperplane ≫
    (Scheme.Modules.pullbackComp (completionMap (P.reindex B D phi f g h))
      ((P.comparison B f).inv ≫ pullback.fst P.projection.left f)).inv.app P.hyperplane ≫
    (Scheme.Modules.pullback (completionMap (P.reindex B D phi f g h))).map
      (P.lineComparison B f).hom ≫ (P.lineReindex B D phi f g h).map.hom

/-- The full global completion retains its native O(1) descent diagram on every base map. -/
structure GlobalCompletion {X : SchemeData} (C : GlobalGradedCone X)
    extends GlobalCompletionReindex C where
  lineOverlap : ∀ (B D : CommRingCat.{0}) (phi : B →+* D)
    (f : Spec B ⟶ X.scheme.left) (g : Spec D ⟶ X.scheme.left)
    (h : Spec.map (CommRingCat.ofHom phi) ≫ f = g),
    toGlobalCompletionReindex.LineCoherence B D phi f g h

instance globalCompletionProper {X : SchemeData} {C : GlobalGradedCone X}
    (P : GlobalCompletion C) : IsProper P.projection.left :=
  P.toGlobalCompletionReindex.toGlobalCompletionData.proper

end MathlibExt.AlgebraicGeometry.GradedConeProjectiveModels
