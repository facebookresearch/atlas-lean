/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

@[expose] public noncomputable section

/-!
# Hilbert schemes of points on actual surfaces

A family is an actual closed subscheme of X times the parameter scheme,
finite and flat over the parameter. Its length is the actual dimension
of fiber global functions. The representing property is a cartesian
universal-family condition, and contains no smoothness conclusion.

Sources: Stacks Project, Hilbert functor, Tags 0D01 and 0DPA;
Fogarty, Algebraic Families on an Algebraic Surface.
-/

namespace MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- The graded projective-spectrum structure morphism. -/
def gradedProjToSpec {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

/-- Actual projective space over the field. -/
def projectiveSpace (k : Type u) [Field k] (n : ℕ) : Over (Spec (.of k)) :=
  letI := @MvPolynomial.gradedAlgebra
  Over.mk (gradedProjToSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

/-- Projectivity is a genuine closed immersion over the field. -/
def IsProjective {k : Type u} [Field k] (X : Over (Spec (.of k))) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ projectiveSpace k n, IsClosedImmersion i.left

/-- A finite flat length-n closed subscheme family in an actual relative product. -/
structure PointSubscheme {k : Type u} [Field k]
    (X T : Over (Spec (.of k))) (n : ℕ) where
  Z : Scheme.{u}
  i : Z ⟶ (prod X T).left
  [closed : IsClosedImmersion i]
  [finite : IsFinite (i ≫ (prod.snd : prod X T ⟶ T).left)]
  [flat : Flat (i ≫ (prod.snd : prod X T ⟶ T).left)]
  length : ∀ p : Spec (.of k) ⟶ T.left, p ≫ T.hom = 𝟙 _ →
    Module.finrank k
      (cohomology
        (pullback.snd (i ≫ (prod.snd : prod X T ⟶ T).left) p)
        (structureModule (pullback (i ≫ (prod.snd : prod X T ⟶ T).left) p)) 0) = n

/-- The proper Hilbert representative and its actual universal family. -/
structure HilbertPointsModel {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (n : ℕ) where
  H : Over (Spec (.of k))
  [proper : IsProper H.hom]
  universalFamily : PointSubscheme X H n
  universal : ∀ (T : Over (Spec (.of k))),
    LocallyOfFiniteType T.hom → QuasiCompact T.hom →
      ∀ Z : PointSubscheme X T n,
        ∃! f : T ⟶ H,
          ∃ a : Z.Z ⟶ universalFamily.Z,
            IsPullback a Z.i universalFamily.i (prod.map (𝟙 X) f).left

end MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes
