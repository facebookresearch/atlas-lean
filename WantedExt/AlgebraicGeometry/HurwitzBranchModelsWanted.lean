/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HurwitzBranchModels
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import Batteries.Util.ProofWanted

/-!
# Actual branch-complex and Cartier-origin construction requests

The branch ideal is tied to the native Rf_* two-term complex and its
finite-free torsion determinant. Fixed-degree stack normalization is
chosen with its Cartesian base changes. The branch morphism covers
every scheme parameter, and its full cotangent differential is the
actual derivative of that same source-fixed morphism.
References: Fantechi–Pandharipande math/9905104v1, §§1–3, Theorem 1;
Graber–Harris–Starr math/0109220v1, §2. The genus of the smooth projective
geometrically connected target curve `D` is `h¹(D, 𝒪_D)` (here `H⁰(D, 𝒪_D) = k`).
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.HurwitzBranchModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.PerfectTorsionCartierOrigins
open MathlibExt.AlgebraicGeometry.HurwitzBranchComplexes
open MathlibExt.Algebra.Homology.PerfectTorsionDeterminants
attribute [local instance] HasDerivedCategory.standard

universe u

theorem_wanted actualTorsionDeterminantUnit (R : Type u) [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (P : TorsionPresentation C)
    (e : OddIndex P ≃ EvenIndex P) : IsUnit (torsionDeterminant P e)

theorem_wanted actualCartierOriginUnique {Y S : Scheme.{0}} (q : Y ⟶ S) (r : ℕ)
    (D E : EffectiveCartierFamily q r) (C : FourierMukai.D Y)
    (A : CartierOrigin D C) (B : CartierOrigin E C) : D.idealSubobject = E.idealSubobject

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

def_wanted actualBranchComplexData (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D T : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 D.hom]
    (projective : ProjectiveSpace.IsProjective D) (n g : ℕ)
    (F : Family D.hom n g T.left T.hom) : BranchComplexData D F

def_wanted actualSymmetricDivisorScheme (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 D.hom]
    (projective : ProjectiveSpace.IsProjective D) (r : ℕ) : DivisorScheme D r

def_wanted actualFixedDegreeModuli (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D : Over (Spec (.of k))) [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    [SmoothOfRelativeDimension 1 D.hom] (projective : ProjectiveSpace.IsProjective D) (n g d : ℕ) :
    (M : DegreeModuli D n g d) × DegreeBaseChange D M

def_wanted actualBranchDivisorOrigin (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D T : Over (Spec (.of k))) [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    [SmoothOfRelativeDimension 1 D.hom] [GeometricallyConnected D.hom]
    (projective : ProjectiveSpace.IsProjective D) (n g d r : ℕ) (positive : 0 < d)
    (degree : (r : ℤ) = 2 * (g : ℤ) - 2 -
      (d : ℤ) * (2 * (Module.finrank k (cohomology D.hom (structureModule D.left) 1) : ℤ) - 2))
    (F : Family D.hom n g T.left T.hom) (stable : IsGeometricallyStable F)
    (curveClass : HasCurveClass D T F (targetClass D d)) (C : BranchComplexData D F) :
    (B : EffectiveCartierFamily (pullback.snd D.hom T.hom) r) ×
      CartierOrigin B (BranchComplexData.object D C)

def_wanted actualBranchMorphism (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D : Over (Spec (.of k))) [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    [SmoothOfRelativeDimension 1 D.hom] [GeometricallyConnected D.hom]
    (projective : ProjectiveSpace.IsProjective D) (n g d r : ℕ) (positive : 0 < d)
    (degree : (r : ℤ) = 2 * (g : ℤ) - 2 -
      (d : ℤ) * (2 * (Module.finrank k (cohomology D.hom (structureModule D.left) 1) : ℤ) - 2))
    (M : DegreeModuli D n g d) (base : DegreeBaseChange D M) (S : DivisorScheme D r) :
    BranchModel D M S

def_wanted actualBranchCotangentDifferential (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D : Over (Spec (.of k))) [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    (n g d r : ℕ) (M : DegreeModuli D n g d) (S : DivisorScheme D r)
    (B : BranchModel D M S) (T : Over (Spec (.of k))) (x : M.stack.Fibre T) :
    BranchDifferentialData D B T x

end MathlibExt.AlgebraicGeometry.HurwitzBranchModels
