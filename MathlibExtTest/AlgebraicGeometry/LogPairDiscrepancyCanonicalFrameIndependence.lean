/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.LogPairDiscrepancyCanonicalFrameIndependence

/-! Tests for canonical divisor independence of frames. -/

noncomputable section

open MathlibExt.AlgebraicGeometry.LogPairs
open WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted

namespace MathlibExtTest.AlgebraicGeometry.LogPairDiscrepancyCanonicalFrameIndependence

universe u

/-- Two canonical data with the same rational top form assign the same coefficient to every prime
point. -/
theorem canonicalDivisor_apply_eq_of_form_eq (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (V : NormalVariety k n) (C D : CanonicalData V) (same : C.form = D.form)
    (p : PrimePoint V) : canonicalDivisor C p = canonicalDivisor D p := by
  rw [canonical_frame_independence k n V C D same]

/-- Canonical divisors agree along a chain of canonical data with equal rational top forms. -/
theorem canonicalDivisor_eq_of_form_eq_trans (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (V : NormalVariety k n) (C D E : CanonicalData V)
    (h1 : C.form = D.form) (h2 : D.form = E.form) :
    canonicalDivisor C = canonicalDivisor E :=
  (canonical_frame_independence k n V C D h1).trans
    (canonical_frame_independence k n V D E h2)

end MathlibExtTest.AlgebraicGeometry.LogPairDiscrepancyCanonicalFrameIndependence
