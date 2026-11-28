/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Order
import MathlibExt.NumberTheory.HataEulerMascheroniFareyTotal

namespace MetaMathlibExt

-- The root intervals [1/2, 1] and [1/3, 1/2] both contribute to the same total sum.
example : (11 : ℝ) / 20 ≤ Real.eulerMascheroniConstant := by
  classical
  let Q := {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | b * c = a * d + 1 ∧ 0 < a ∧ c ≤ d}
  let q₁ : Q := ⟨(1, 2, 1, 1), by decide⟩
  let q₂ : Q := ⟨(1, 3, 1, 2), by decide⟩
  let f (q : Q) : ℝ := match q.1 with
    | (a, b, c, d) => 1 / (a * b * c * d * (a + c) * (b + d))
  obtain ⟨hs, hγ⟩ := euler_mascheroni_eq_hata_farey_sum
  change Summable f at hs
  simp only [Nat.cast_one, Nat.cast_ofNat] at hγ
  change Real.eulerMascheroniConstant = (1 : ℝ) / 2 + (1 : ℝ) / 2 * ∑' q, f q at hγ
  have hnonneg (q : Q) : 0 ≤ f q := by
    obtain ⟨⟨a, b, c, d⟩, _⟩ := q
    dsimp [f]
    positivity
  have hne : q₁ ≠ q₂ := by decide
  have h := hs.sum_le_tsum ({q₁, q₂} : Finset Q) (fun q _ ↦ hnonneg q)
  rw [Finset.sum_pair hne] at h
  have h' : (1 : ℝ) / 10 ≤ ∑' q, f q := by
    convert h using 1
    norm_num [f, q₁, q₂]
  linarith only [hγ, h']

end MetaMathlibExt
