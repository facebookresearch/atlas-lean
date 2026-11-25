/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Diagnostics.BinaryObservation
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Tests for PPV coverage transfer: full coverage of the whole space,
and the singleton `(1, 1, 1)` PPV value. -/

namespace MathlibExtTest.Biology.Diagnostics.BinaryObservation

open MeasureTheory Set MathlibExt.Biology.Diagnostics.BinaryObservation

/-- With `S ω` everything and `T ω` everything, both coverage events
are the whole space and the inequality is equality of `1 ≤ 1` on a
one-point probability space. -/
example : (Measure.dirac ((): Unit)).real Set.univ ≤
    (Measure.dirac ((): Unit)).real Set.univ := by
  have h := ppv_coverage_transfer (Measure.dirac ())
    (fun _ => Set.univ) (fun _ => Set.univ) (fun _ => ((1 : ℝ), 1, 1))
    (by simp) (by simp) (fun _ _ _ => Set.mem_univ _) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num)
  simp at h ⊢

/-- The singleton `(1, 1, 1)` has PPV `1`. -/
example : ppv (1, 1, 1) = 1 ∧ (1 - (1 : ℝ)) * 1 + 1 * (1 - 1) = 0 :=
  ppv_one_one_one

/-- Boundary: at `θ = (0, 1, 1)` the PPV denominator vanishes, so the
coverage theorem's denominator hypothesis cannot be supplied. -/
example : ¬ ((0 : ℝ) * 1 + (1 - 0) * (1 - 1) ≠ 0) := by norm_num

end MathlibExtTest.Biology.Diagnostics.BinaryObservation
