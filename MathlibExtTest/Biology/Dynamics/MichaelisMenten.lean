/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.MichaelisMenten

/-! Tests for Michaelis–Menten kinetics: concrete constants and rates, the junk value at
`k₁ = 0`, the enzyme-free solution as a non-vacuity witness of `IsSolution`, and the fast
transient. -/

open Filter Topology Real

namespace MathlibExtTest.Biology.Dynamics.MichaelisMenten

open MathlibExt.Biology.Dynamics.MichaelisMenten

example : michaelisConstant 1 1 1 = 2 := by norm_num [michaelisConstant]

/-- Junk value outside the domain `k₁ > 0`. -/
example : michaelisConstant 0 1 1 = 0 := by simp [michaelisConstant]

example : mmRate 2 1 1 = 1 := by norm_num [mmRate]

example : mmRate 2 1 1 = 2 / 2 := mmRate_michaelisConstant one_ne_zero

example : mmRate 2 1 3 < 2 := mmRate_lt two_pos one_pos (by norm_num)

example : qssComplex 1 1 1 1 2 = 1 / 2 := by norm_num [qssComplex, michaelisConstant]

/-- **Non-vacuity witness.** Without enzyme nothing happens: `s ≡ 3`, `c ≡ e ≡ 0`, `p ≡ 1`. -/
theorem enzymeFree : IsSolution 1 1 1 (fun _ ↦ 3) (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1) where
  hasDerivAt_substrate t _ := by
    convert hasDerivAt_const t (3 : ℝ) using 1; simp [substrateRate]
  hasDerivAt_complex t _ := by
    convert hasDerivAt_const t (0 : ℝ) using 1; simp [complexRate]
  hasDerivAt_enzyme t _ := by
    convert hasDerivAt_const t (0 : ℝ) using 1; simp [complexRate]
  hasDerivAt_product t _ := by
    convert hasDerivAt_const t (1 : ℝ) using 1; simp

example (t : ℝ) (ht : 0 ≤ t) :
    (fun _ : ℝ ↦ (3 : ℝ)) t + (fun _ : ℝ ↦ (0 : ℝ)) t + (fun _ : ℝ ↦ (1 : ℝ)) t = 4 := by
  rw [enzymeFree.substrate_conservation ht]; norm_num

/-- Starting on the quasi-steady-state manifold the fast transient stays there. -/
example (t : ℝ) : fastTransient 1 1 1 1 2 (1 / 2) t = 1 / 2 := by
  simp [fastTransient, qssComplex, michaelisConstant]; norm_num

example : Tendsto (fastTransient 1 1 1 1 2 0) atTop (𝓝 (qssComplex 1 1 1 1 2)) :=
  tendsto_fastTransient one_pos (by norm_num [michaelisConstant]) 0

end MathlibExtTest.Biology.Dynamics.MichaelisMenten
