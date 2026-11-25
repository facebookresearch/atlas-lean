/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSetDerived

namespace MetaMathlibExt.isSelfSimilarCompactSet_derivedSet_enum

open Ordinal

private theorem omega_le_endpoint : ω ≤ (ω ^ ω : Ordinal.{0}) := by
  calc
    ω = ω ^ (1 : Ordinal) := (opow_one _).symm
    _ ≤ ω ^ ω := opow_le_opow_right omega0_pos one_lt_omega0.le

variable {K : Set ℝ} {μ : ℕ} {ρ : ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
  {f g : Ordinal.{0} → ℝ}
  (hf : StrictAntiOn f (Set.Iic (ω ^ ω))) (hfK : f '' Set.Iic (ω ^ ω) = K)
  (hg : StrictAntiOn g (Set.Iic (ω ^ ω)))

-- The first point of the second derived set occurs at index ω².
example (hgK : g '' Set.Iic (ω ^ ω) = derivedSet^[2] K) :
    g 0 = f (ω ^ (2 : Ordinal)) := by
  simpa using isSelfSimilarCompactSet_derivedSet_enum hK (n := 2) (by decide) hf hfK hg hgK
    (α := 0) zero_le

-- At the first infinite index, adding one on the left fixes ω.
example (hgK : g '' Set.Iic (ω ^ ω) = derivedSet K) :
    g ω = f (ω * ω) := by
  simpa only [Nat.cast_one, opow_one, one_add_omega0] using
    isSelfSimilarCompactSet_derivedSet_enum hK (n := 1) le_rfl hf hfK hg
      (by simpa only [Function.iterate_one] using hgK) omega_le_endpoint

-- Every positive finite iterate retains the last point.
example {n : ℕ} (hn : 1 ≤ n) (hgK : g '' Set.Iic (ω ^ ω) = derivedSet^[n] K) :
    g (ω ^ ω) = f (ω ^ ω) := by
  simpa only [one_add_of_omega0_le omega_le_endpoint, ← opow_add, natCast_add_omega0] using
    isSelfSimilarCompactSet_derivedSet_enum hK hn hf hfK hg hgK (α := ω ^ ω) le_rfl

end MetaMathlibExt.isSelfSimilarCompactSet_derivedSet_enum
