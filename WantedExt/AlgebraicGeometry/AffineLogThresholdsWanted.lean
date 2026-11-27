/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AffineLogThresholds

/-!
# Local hypersurface threshold bounds

These are bounds on the actual local integrability supremum, with actual
Taylor-order multiplicity. The ambient dimension is the complex dimension;
the exponent -2c and the native real Lebesgue measure are fixed.

Reference: Mustaţă, *IMPANGA lecture notes on log canonical thresholds*,
https://arxiv.org/abs/1107.2676, bounds by order of vanishing.
General Q-divisor discrepancies and multiplier/test-ideal comparisons are
further interfaces, beyond these concrete characteristic-zero hypersurfaces.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AffineLogThresholdsWanted

open MathlibExt.AlgebraicGeometry.AffineLogThresholds

theorem_wanted localThreshold_lower_order (n : ℕ) (hn : 0 < n)
    (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0) (p : Fin n → ℂ)
    (zero : MvPolynomial.eval p f = 0) (positive : 0 < orderAt f p) :
    ENNReal.ofReal (1 / (orderAt f p : ℝ)) ≤ localThreshold f p

theorem_wanted localThreshold_upper_order (n : ℕ) (hn : 0 < n)
    (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0) (p : Fin n → ℂ)
    (zero : MvPolynomial.eval p f = 0) (positive : 0 < orderAt f p) :
    localThreshold f p ≤ ENNReal.ofReal ((n : ℝ) / orderAt f p)

end WantedExt.AlgebraicGeometry.AffineLogThresholdsWanted
