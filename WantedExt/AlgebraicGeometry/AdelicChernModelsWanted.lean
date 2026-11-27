/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NonarchimedeanChernModels

/-!
# Valuation residue, divisorial point and model intersection requests

The requests retain the native models and original scalars. Divisorial
points have a discrete valuation guard. These are direct unfinished
construction requests, not completed providers.

The local and global Chern measures, the numerical intersections and the mass
formula are not requested here: they need nef approximations and a
model-boundary class finer than the placewise one, and are left to a separate
development.
Source: Yuan--Zhang, arXiv:2105.13587v9, Section 3.6 and Appendix A.6.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AdelicChernModels

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open ModelIntersectionDegrees RelativeDeterminantPairings

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

public def_wanted valuationResidue (K : Type) [NormedField K]
    (h : ∀ a b : K, ‖a+b‖ ≤ max ‖a‖ ‖b‖) :
    NonarchimedeanChernModels.ValuationResidue K h

/-- **Divisorial points of a normal model.** Let $K$ be a complete nonarchimedean normed field,
$X$ an integral $K$-scheme, $L_1, \dots, L_d$ sheaves of modules on $X$, and $M$ a model of $X$ and
of powers of the $L_i$ over the ring of integers of $K$ (`ModelTuple`) whose local rings are all
integrally closed domains; assume that derived pullbacks and pushforwards of module sheaves and
derived extensions of scalars along ring maps exist, that `tilde` preserves finite limits, and
that determinant modules of finite projective modules over commutative rings are invertible.
Given the residue-field datum $V$ of $K$, special-fibre component data $S$ (`SpecialComponents`)
and a uniformizer $\varpi$ ($0 < \lVert \varpi \rVert < 1$, and $\lVert a \rVert$ an integer power
of $\lVert \varpi \rVert$ for every nonzero $a \in K$), witnessing that the norm of $K$ is discrete
(`DiscreteValuation`): a divisorial point (`DivisorialPoint`) attached to every irreducible
component $C$ of the special fibre of $M$. -/
public def_wanted divisorialPoints (K : Type) [NormedField K] [CompleteSpace K]
    (X : Over (Spec (.of K))) [IsIntegral X.left]
    (h : ∀ a b : K, ‖a+b‖ ≤ max ‖a‖ ‖b‖) (d : ℕ) (L : Fin d → X.left.Modules)
    (M : NonarchimedeanChernModels.ModelTuple K X h d L)
    (normal : ∀ y : M.scheme, IsDomain (M.scheme.presheaf.stalk y) ∧
      IsIntegrallyClosed (M.scheme.presheaf.stalk y))
    (V : NonarchimedeanChernModels.ValuationResidue K h)
    (S : NonarchimedeanChernModels.SpecialComponents M V)
    (v : NonarchimedeanChernModels.DiscreteValuation K) :
    ∀ C, NonarchimedeanChernModels.DivisorialPoint M V S v C

public def_wanted modelIntersection (K : Type) [NormedField K] [CompleteSpace K]
    (X : Over (Spec (.of K))) (h : ∀ a b : K, ‖a+b‖ ≤ max ‖a‖ ‖b‖)
    (d : ℕ) (L : Fin d → X.left.Modules)
    (M : NonarchimedeanChernModels.ModelTuple K X h (d+1)
      (Fin.cons (CoherentCurveLinearSeries.structureModule X.left) L)) :
    NonarchimedeanChernModels.ModelIntersectionSource M

end WantedExt.AlgebraicGeometry.AdelicChernModels
