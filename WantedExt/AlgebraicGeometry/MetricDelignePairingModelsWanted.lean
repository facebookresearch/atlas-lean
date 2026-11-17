/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NumericalAdelicIntersections
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Direct metric Deligne construction and normalization requests

The actual global bounded determinant line, all affine/cochain source
transitions, rational Cartier/Koszul symbols, finite nonreduced Gamma norm
and divisor-integral model completion are retained. The normalized Picard
map is an output on native quotients; no pairing oracle is an input.
Sources: Yuan--Zhang, arXiv:2105.13587v9, Theorem 4.1.3 and pp109--120.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MetricDelignePairingModels

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PlacewiseMetrizedLineModels AdelicSemipositiveClosures AdelicPicardVectors
open MetricDelignePairingModels DeligneSymbolModels GlobalBoundedDeterminantModels
open RelativeDeterminantPairings NumericalAdelicIntersections

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

/-- Finite-fibre symbols agree with the full determinant norm of the actual Gamma algebra. -/
public def_wanted finiteNormComparison (K : Type) [Field K]
    (X : Over (Spec (.of K))) [IsFinite X.hom] [Flat X.hom] (L : X.left.Modules)
    (F : FiniteFlatDeligneNormModels.Sources X L)
    (I : DeterminantSources)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Spec (.of K)),
      Presentations X.hom (fun _ : Fin 1 ↦ L) R a)
    (D : DeligneLine I X.hom 0 (fun _ : Fin 1 ↦ L) P) :
    {e : D.line ≅ FiniteFlatDeligneNormModels.normLine (K := K) X L //
      ∀ (s : RegularTuple X.hom 0 (fun _ : Fin 1 ↦ L)) (S : SymbolSources I X.hom 0 (fun _ ↦ L) P D s),
        e.hom.app ⊤ S.sectionValue =
          FiniteFlatDeligneNormModels.normSection (K := K) X L F (s.sectionValue 0)}

variable {K : Type} [Field K] {A : AdelicField K} {X Y : Over (Spec (.of K))}

/-- Actual norms on the SAME native line, with rational symbols and actual model limits. -/
public def_wanted metricPairing (G : GroundBase (K := K)) (f : X ⟶ Y) (n : ℕ)
    (scope : RelativeScope f.left n)
    (M : Fin (n+1) → LineObject (A := A) (X := X) G)
    (I : DeterminantSources)
    (cubical : DeligneCubicalModels.CubicalSources I f.left n)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y.left), Presentations f.left (fun i ↦ (M i).line) R a)
    (D : DeligneLine I f.left n (fun i ↦ (M i).line) P)
    (B : AdelicArithmeticModelFrames.ArithmeticBase A) (b : ℕ+) (ground : GroundModel G B b)
    (sourceScope : QuasiProjectiveScope X) (targetScope : QuasiProjectiveScope Y) :
    Σ S : SymbolAtlas G f n M I P D, Σ R : RecursionSources S, MetricResult S R

/-- Descend the actual metric Deligne construction to the SAME native rational Picard quotients. -/
public def_wanted pairingOnPicard (G : GroundBase (K := K)) (f : X ⟶ Y) (n : ℕ)
    (scope : RelativeScope f.left n) :
    {F : MultilinearMap ℚ (fun _ : Fin (n+1) ↦ PicardVector (A := A) (X := X) (G := G))
        (PicardVector (A := A) (X := Y) (G := G)) //
      ∀ (M : Fin (n+1) → LineObject (A := A) (X := X) G)
        (I : DeterminantSources)
        (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y.left), Presentations f.left (fun i ↦ (M i).line) R a)
        (D : DeligneLine I f.left n (fun i ↦ (M i).line) P)
        (S : SymbolAtlas G f n M I P D) (R : RecursionSources S) (T : MetricResult S R),
        F (fun i ↦ lineClass (M i)) = lineClass T.asObject}

end WantedExt.AlgebraicGeometry.MetricDelignePairingModels
