/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PerfectoidUntiltingSites

/-!
# Fixed relative tilting and rational/site comparison requests

All carriers, local ring maps, rational coefficient maps and sheaf
units/counits are already prescribed publicly. The source is a fixed
perfectoid field untilt for the equivalence statements. In particular,
no equivalence of sites or inverse global functor is assumed as input.

Sources: Scholze, arXiv:1111.4914v1, Theorems 1.7--1.11, 6.3 and 7.12;
arXiv:1709.07343v4, Theorem 3.12 and Definition 8.1.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PerfectoidGlobalTilting

open CategoryTheory
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.AlgebraicGeometry.PerfectoidRationalTilting
open MathlibExt.AlgebraicGeometry.PerfectoidUntiltingSites
open MathlibExt.AlgebraicGeometry.IntegralTiltModels
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite

/-- Construct the rational comparison at the prescribed sharp numerator and denominator. -/
public def_wanted rationalTiltComparison (p : ℕ) [Fact p.Prime]
    (P : AffineUntilting p) (D : OriginalRationalModel p P)
    (T : Finset (IntegralRing p P.pair)) (s : IntegralRing p P.pair)
    (hT : (D.numerators : Set P.pair.ring) =
      sharp p P.pair '' (T : Set (IntegralRing p P.pair)))
    (hs : D.denominator = sharp p P.pair s) : RationalTiltComparison p P D T s

/-- The actual relative affine tilting functor is an equivalence over the fixed field. -/
public def_wanted relativeTiltingEquivalence (p : ℕ) [Fact p.Prime]
    (K : AffineUntilting p) (_hK : IsField K.pair.ring) :
    {e : RelativeAffine p K ≌ Over K.tilt.pair // e.functor = relativeTilting p K}

/-- Continuity uses the original compact-open cover rule before tilting. -/
public theorem_wanted relativeTiltingContinuous (p : ℕ) [Fact p.Prime]
    (K : AffineUntilting p) (_hK : IsField K.pair.ring) :
    (relativeTilting p K).IsContinuous (relativeVTopology p K)
      ((topology p).over K.tilt.pair)

/-- The actual original-ring etale property is preserved by the fixed tilt maps. -/
public theorem_wanted tiltingPreservesEtale (p : ℕ) [Fact p.Prime] : PreservesEtale p

/-- The actual original cofiltered pro-etale presentations tilt to pro-etale maps. -/
public theorem_wanted tiltingPreservesProEtale (p : ℕ) [Fact p.Prime] :
    PreservesProEtale p

/-- The native global tilting unit is invertible on every actual source sheaf. -/
public theorem_wanted globalTiltingUnitIsIso (p : ℕ) [Fact p.Prime]
    (K : AffineUntilting p) (_hK : IsField K.pair.ring)
    [(relativeTilting p K).IsContinuous (relativeVTopology p K)
      ((topology p).over K.tilt.pair)]
    [(untiltSheaves p K).IsRightAdjoint]
    (F : Sheaf (relativeVTopology p K) (Type 1)) : IsIso ((tiltingUnit p K).app F)

/-- The native global tilting counit is invertible on every actual tilted sheaf. -/
public theorem_wanted globalTiltingCounitIsIso (p : ℕ) [Fact p.Prime]
    (K : AffineUntilting p) (_hK : IsField K.pair.ring)
    [(relativeTilting p K).IsContinuous (relativeVTopology p K)
      ((topology p).over K.tilt.pair)]
    [(untiltSheaves p K).IsRightAdjoint]
    (F : Sheaf ((topology p).over K.tilt.pair) (Type 1)) :
    IsIso ((tiltingCounit p K).app F)

end WantedExt.AlgebraicGeometry.PerfectoidGlobalTilting
