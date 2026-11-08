/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
public import Mathlib.Algebra.CharP.Basic

/-!
# Dual matrix-multiplication exponent: source-bound requests

All declarations below are private unproved `ProofWanted` data. The optimizer uses
actual field-input arithmetic circuits, not a supplied complexity function. The
zero-aspect value two and output-cost lower bound are proved upstream.

The stronger strict statements imply the catalogue's corresponding weak table
rows; the Coppersmith exponent equality implies the weak `0.172` row. None of
these consequences is claimed without the requested premise. The retained WXXZ
introduction also allows divisions; its transfer to the selected division-free
model is not proved. Exact tensor-rank and floor/ceiling transfers remain gaps.
-/

set_option autoImplicit false

namespace Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted

open Cslib.Complexity.Algebraic

universe u v

/-- Source: C15b, CLLZ2025 Figure 2, the general upper bound, not a method-specific barrier. -/
theorem_wanted upperBoundOne :
    ∀ (F : Type u) [Field F], dualCircuitExponent F ≤ 1

/-- Source: C15b/LGU2018 Section 1.1, Coppersmith's 1982 exponent equality. -/
theorem_wanted coppersmith1982Exponent :
    ∀ (F : Type u) [Field F], rectangularCircuitExponent F ((172 : ℝ) / 1000) = 2

/-- Source: C15b/LG2012 abstract, the previous Coppersmith 1997 record is strict. -/
theorem_wanted coppersmith1997StrictLower :
    ∀ (F : Type u) [Field F], ENNReal.ofReal ((29462 : ℝ) / 100000) < dualCircuitExponent F

/-- Source: C15b/LG2012 abstract, Le Gall's 2012 improvement is strict. -/
theorem_wanted leGall2012StrictLower :
    ∀ (F : Type u) [Field F], ENNReal.ofReal ((30298 : ℝ) / 100000) < dualCircuitExponent F

/-- Source: C15b/LGU2018 Section 1.2, the fourth-power lower bound is weak. -/
theorem_wanted leGallUrrutia2018Lower :
    ∀ (F : Type u) [Field F], ENNReal.ofReal ((31389 : ℝ) / 100000) ≤ dualCircuitExponent F

/-- Source: C15b/WXXZ2024 introduction, the best displayed lower bound is strict. -/
theorem_wanted williamsXuXuZhou2024StrictLower :
    ∀ (F : Type u) [Field F], ENNReal.ofReal ((321334 : ℝ) / 1000000) < dualCircuitExponent F

/-- Source: CLLZ rectangular naive upper bound; a general finite circuit construction is missing. -/
theorem_wanted rectangularNaiveUpper :
    ∀ (F : Type u) [Field F] (k : ℝ), 0 ≤ k →
      rectangularCircuitExponent F k ≤ ENNReal.ofReal (2 + k)

/-- Source: LG2012 exact bilinear-rank characterization; the operation/rank transfer is missing. -/
theorem_wanted rectangularOperationRankBridge :
    ∀ (F : Type u) [Field F] (k : ℝ), 0 ≤ k →
      rectangularCircuitExponent F k =
        MatrixMultiplicationExponent.rectangularMatrixMultiplicationExponent F k

/-- Source: LG2012 Section 1, characteristic dependence; this circuit-model transfer is missing. -/
theorem_wanted characteristicInvariance :
    ∀ (F : Type u) (K : Type v) [Field F] [Field K], ringChar F = ringChar K →
      ∀ k : ℝ, 0 ≤ k → rectangularCircuitExponent F k = rectangularCircuitExponent K k

end Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted
