/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeProjectivity
public import MathlibExt.AlgebraicGeometry.RelativeMoriContracts

/-!
# Minimal general relative log-Mori proof contracts

The source is a normal real-boundary log pair with actual K+Delta Cartier
data. Its numerical cone uses genuine curves contracted over the given
base. Relative generation is the native pullback/pushforward counit.
Outputs are actual scheme maps, connected fibres and strict-transform
boundary/canonical flip data. Shared model calculus and representative
comparisons are explicit dependencies; smooth absolute statements are
preserved separately.

References: Kollár--Mori, *Birational Geometry of Algebraic Varieties*,
Chapter3 (relative cone, base-point-free and contraction theorems);
Birkar--Cascini--Hacon--McKernan, *Existence of minimal models for varieties
of log general type*, Corollary1.4.1 (klt flips).
No unrestricted termination, abundance or conjectural model constructor
is asserted.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeMoriContractionWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RelativeMoriContracts
open MathlibExt.AlgebraicGeometry.MoriContractionModels
open MathlibExt.AlgebraicGeometry.NumericalCurveCones
open MathlibExt.AlgebraicGeometry.RelativeProjectivity
open scoped BigOperators

universe u

/-- Equivalent genuine Cartier representatives give the same curve degree. -/
public theorem_wanted representative_curve_degree (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (V : NormalVariety k n) (D E : CartierCombination V)
    (same : D.divisor = E.divisor) (C : Curve V.X) :
    combinationOnCurve D C = combinationOnCurve E C

/-- Finite-dimensional relative numerical curve space for a projective map. -/
public theorem_wanted relative_numerical_finite (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (S : Over (Spec (.of k)))
    (base : IsQuasiProjectiveBase S) (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q) :
    FiniteDimensional ℝ (RelativeN1 q)

/-- Relative klt base-point-freeness with an actual ample adjoint difference. -/
public theorem_wanted relative_basepoint_free (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (klt : IsKlt P)
    (S : Over (Spec (.of k))) (base : IsQuasiProjectiveBase S)
    (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q)
    (L : CartierLine P.variety) (nef : ∀ C : Curve P.variety.X, IsContracted q C →
      0 ≤ curveDegrees C L.line)
    (a : ℕ) (positive : 0 < a) (D : CartierCombination P.variety)
    (normalized : D.divisor = (a : ℝ) • realCast L.divisor - P.adjoint.divisor)
    (ample : IsRelativelyAmpleR q D) : IsRelativelySemiample q L.line

/-- Contraction of an actual K+Delta-negative relative extremal ray. -/
public def_wanted relative_contraction (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (klt : IsKlt P)
    (qfactorial : IsQFactorial P.variety) (S : Over (Spec (.of k)))
    (base : IsQuasiProjectiveBase S) (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q)
    (v : RelativeN1 q) (extremal : IsExtremal v)
    (negative : combinationOnClass q P.adjoint v < 0) : RelativeContraction P q v

/-- A genuine small klt flipping contraction has the normalized log flip. -/
public def_wanted relative_flip (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (dimension : 3 ≤ n) (P : LogPair k n)
    (klt : IsKlt P) (qfactorial : IsQFactorial P.variety)
    (S : Over (Spec (.of k))) (base : IsQuasiProjectiveBase S)
    (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q)
    (v : RelativeN1 q) (extremal : IsExtremal v)
    (negative : combinationOnClass q P.adjoint v < 0) (C : RelativeContraction P q v)
    (small : IsSmall C.map.left n)
    (antiAdjoint : IsRelativelyAmpleR C.map (negativeCombination P.adjoint)) : RelativeFlip C

end WantedExt.AlgebraicGeometry.RelativeMoriContractionWanted
