/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PlurigenusFamilies
public import MathlibExt.AlgebraicGeometry.MoriContractionModels

/-!
# Numerical MMP foundations, Mori contractions and flips

The numerical space and cone are built from actual curve degrees. Canonical
lines, ample systems, contracted curves and small birational maps have fixed
geometric meanings. These requests are in the smooth projective
characteristic-zero scope; no general termination or abundance statement is
used as established background.

References: Kollár–Mori, *Birational Geometry of Algebraic Varieties*,
Chapter 3; Birkar–Cascini–Hacon–McKernan, *Existence of minimal models for
varieties of log general type*, for existence of flips.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MoriConeContractionWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry (ProjectiveSpace.IsProjective)
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.NumericalCurveCones
open MathlibExt.AlgebraicGeometry.MoriContractionModels
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open scoped BigOperators

universe u

/-- Finite dimensionality of the actual real numerical curve space. -/
theorem_wanted numerical_finiteDimensional (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    : FiniteDimensional ℝ (N1 X)

/-- The finite cone decomposition after a genuine positive ample perturbation. -/
theorem_wanted cone (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (K H : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n) (hH : IsAmpleLine H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∃ C : Fin m → Curve X,
      (∀ i, genus (C i).source.hom = 0 ∧
        0 < -curveDegrees (C i) K ∧ -curveDegrees (C i) K ≤ n + 1 ∧
        IsExtremalRay (curveClass (C i))) ∧
      ∀ v ∈ moriCone X, ∃ w ∈ moriCone X,
        0 ≤ w.val K + ε * w.val H ∧
        ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i) ∧
          v = w + ∑ i, a i • curveClass (C i)

/-- Rationality of the actual nef threshold, with the smooth canonical denominator bound. -/
theorem_wanted rationality (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (K H : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n) (hH : IsAmpleLine H)
    (negative : ∃ C : Curve X, curveDegrees C K < 0) :
    ∃ r : ℚ, 0 < r ∧ r.den ≤ n + 1 ∧
      ∀ t : ℝ, 0 ≤ t → (nefPencil H K t ↔ t ≤ (r : ℝ))

/-- Base-point-freeness with a genuinely ample anti-canonical perturbation. -/
theorem_wanted basepointFree (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (K L : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n) (Kinv : InverseLine K)
    (nef : IsNefLine L) (a : ℕ) (ha : 0 < a)
    (hLine : IsLineBundle
      (moduleTensor X.left (power L.val a) Kinv.inverse.val))
    (ample : IsAmpleLine
      ⟨moduleTensor X.left (power L.val a) Kinv.inverse.val, hLine⟩) :
    IsSemiample L.val L.property

/-- Contraction of an actual K-negative extremal ray. -/
def_wanted contraction (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (K : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n)
    (v : N1 X) (ray : IsExtremalRay v) (negative : v.val K < 0) :
    Contraction X v

/-- Existence of a geometrically specified canonical flip for a small contraction. -/
def_wanted flip (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (hn : 3 ≤ n) (K : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n)
    (v : N1 X) (ray : IsExtremalRay v) (negative : v.val K < 0)
    (C : Contraction X v) (small : IsSmall C.map.left n)
    (Kinv : InverseLine K)
    (antiCanonical : IsRelativelyAmple C.map Kinv.inverse) : Flip C n

end WantedExt.AlgebraicGeometry.MoriConeContractionWanted
