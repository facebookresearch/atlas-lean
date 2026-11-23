/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticTropicalSupport

/-!
# Analytic support and genuine valued-extension comparisons

Gubler, 1108.6126, sections 3--5; Osserman--Payne, 1007.1314v3, Appendix A.4.
The original ground field may have trivial valuation or be incomplete. The
working extension and its norm/valuation are actual specified fields. No
ground-field-point closure is asserted invariant for a trivial valuation.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticTropicalSupportWanted

open MathlibExt.AlgebraicGeometry.ValuativeTropicalization
open MathlibExt.AlgebraicGeometry.TropicalCycleIntersections
open MathlibExt.AlgebraicGeometry.AnalyticTropicalSupport

theorem_wanted analytic_support_comparison (K : Type) [NormedField K]
    [IsUltrametricDist K] [Valued K NNReal] [IsAlgClosed K] [CompleteSpace K]
    (_norm : ValuationNormCompatibility K) (_nontrivial : NontrivialValuation K)
    (n : ℕ) (I : Ideal (CoordinateRing K n)) :
    tropicalization K n I = tropicalizationOver (L := K) I

theorem_wanted scalar_extension_support (K L : Type) [NormedField K] [NormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [Algebra K L]
    (_norm : NormExtension K L) (n : ℕ) (I : Ideal (CoordinateRing K n)) :
    tropicalization K n I = tropicalization L n (baseChangeIdeal (L := L) I)

def_wanted extended_weighted_presentation (K L : Type) [NormedField K] [NormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [Algebra K L]
    [Valued L NNReal] [IsAlgClosed L] [CompleteSpace L]
    (_norm_extension : NormExtension K L) (_valuation_norm : ValuationNormCompatibility L)
    (_nontrivial : NontrivialValuation L) (n d : ℕ) (_dimension_le : d ≤ n)
    (I : Ideal (CoordinateRing K n))
    (_pure : PureDimension L n (baseChangeIdeal (L := L) I) d) :
    {P : Presentation L n (baseChangeIdeal (L := L) I) //
      P.cycle.dimension = d ∧ P.cycle.support = tropicalization K n I}

end WantedExt.AlgebraicGeometry.AnalyticTropicalSupportWanted
