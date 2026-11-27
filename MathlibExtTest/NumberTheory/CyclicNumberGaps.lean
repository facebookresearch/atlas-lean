/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CyclicNumberGaps

open Asymptotics Filter
open MetaMathlibExt

namespace MetaMathlibExt.CyclicNumberGapsTest

local instance cyclicNumberDecidable : DecidablePred IsCyclicNumber := fun n => by
  unfold IsCyclicNumber
  infer_instance

-- The eighth cyclic number is composite, and its predecessor is the seventh cyclic number.
example :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    c 8 - c 7 = 2 := by
  have h₁ : Nat.nth IsCyclicNumber 6 = 13 := by
    have h : Nat.count IsCyclicNumber 13 = 6 := by decide
    rw [← h]
    exact Nat.nth_count (by decide)
  have h₂ : Nat.nth IsCyclicNumber 7 = 15 := by
    have h : Nat.count IsCyclicNumber 15 = 7 := by decide
    rw [← h]
    exact Nat.nth_count (by decide)
  norm_num [h₁, h₂]

example (hRH : RiemannHypothesis) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let p : ℕ → ℝ := fun n => (Nat.nth Nat.Prime (n - 1) : ℝ)
    (fun n => c (n + 1) - c n) =o[atTop] (fun n => Real.sqrt (p n) * Real.log (p n)) :=
  cyclicNumber_gap_isLittleO_of_riemannHypothesis (hRH := hRH)

end MetaMathlibExt.CyclicNumberGapsTest
