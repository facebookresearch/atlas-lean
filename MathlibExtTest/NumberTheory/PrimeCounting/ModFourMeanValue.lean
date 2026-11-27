/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ModFourMeanValue

open Filter
open scoped Topology

open MetaMathlibExt

namespace MetaMathlibExtTest.ModFourMeanValue

-- The same leading constant occurs in both estimates, with a factor of two.
example (f : ℕ →*₀ ℝ) (h₀ : ∀ n, 0 ≤ f n) (h₁ : ∀ n, f n ≤ 1) (a : ZMod 4)
    (ha : IsUnit a) (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → f p = if (p : ZMod 4) = a then 1 else 0) :
    Tendsto (fun x : ℝ =>
      ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n) * √(Real.log x) / x) /
        ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n / (n : ℝ)) / √(Real.log x))) atTop (𝓝 (1 / 2)) := by
  obtain ⟨α, hα, hrecip, hsum⟩ :=
    exists_tendsto_sum_of_prime_mod_four f h₀ h₁ a ha hp
  convert hsum.div hrecip hα.ne' using 1
  congr 1
  field_simp

end MetaMathlibExtTest.ModFourMeanValue
