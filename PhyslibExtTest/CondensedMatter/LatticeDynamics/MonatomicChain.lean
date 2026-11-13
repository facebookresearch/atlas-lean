/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.LatticeDynamics.MonatomicChain
public import PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open PhyslibExt.CondensedMatter.LatticeDynamics.MonatomicChain
open PhyslibExt.ClassicalMechanics.WaveEquation.WaveConventions

namespace PhyslibExtTest.CondensedMatter.LatticeDynamics.MonatomicChain

/-! ### Monatomic chain normal modes, `N = 6`, `K = m = 1` -/

example (K m : ℝ) (hm : 0 < m) (hK : 0 ≤ K) :
    chainNormalModeAngularFrequency K m hm hK 6 0 = 0 :=
  chainNormalModeAngularFrequency_zero K m hm hK 6

example : chainNormalModeAngularFrequency 1 1 (by norm_num) (by norm_num) 6 4 =
    chainNormalModeAngularFrequency 1 1 (by norm_num) (by norm_num) 6 2 :=
  chainNormalModeAngularFrequency_symm 1 1 (by norm_num) (by norm_num) (j := 2) (hj := by norm_num)

example : 0 ≤ chainNormalModeAngularFrequency 1 1 (by norm_num) (by norm_num) 6 2 :=
  chainNormalModeAngularFrequency_nonneg 1 1 (by norm_num) (by norm_num) 6 2

example : chainNormalModeAngularFrequency 1 1 (by norm_num) (by norm_num) 6 3 = 2 := by
  have harg : Real.pi * ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = Real.pi / 2 := by
    push_cast
    ring
  simp only [chainNormalModeAngularFrequency, harg, Real.sin_pi_div_two, div_one,
    Real.sqrt_one, abs_one, mul_one]

/-- The ordinary frequency of the `j = 3` mode is `1 / π`: the angular frequency is `2` and
`frequency 2 = 1 / π`, pinning the angular-versus-ordinary distinction. -/
example : frequency (chainNormalModeAngularFrequency 1 1 (by norm_num) (by norm_num) 6 3) =
    1 / Real.pi := by
  have hchain :
      chainNormalModeAngularFrequency 1 1 (by norm_num) (by norm_num) 6 3 = 2 := by
    have harg : Real.pi * ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = Real.pi / 2 := by
      push_cast
      ring
    simp only [chainNormalModeAngularFrequency, harg, Real.sin_pi_div_two, div_one,
      Real.sqrt_one, abs_one, mul_one]
  rw [hchain]
  unfold frequency
  field_simp

end PhyslibExtTest.CondensedMatter.LatticeDynamics.MonatomicChain

#print axioms chainNormalModeAngularFrequency_zero
#print axioms chainNormalModeAngularFrequency_nonneg
#print axioms chainNormalModeAngularFrequency_symm
