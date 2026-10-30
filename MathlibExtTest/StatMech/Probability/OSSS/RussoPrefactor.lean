/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.RussoPrefactor
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.RussoPrefactor`

* `rp_denom_pos`, `rp_prefactor_pos` at `J = β = 1`; `rp_prefactor_antitone_beta`.
* `rp_minPrefactor`, `rp_differential_lower`, `rp_differential_lower_weighted`,
  `rp_differential_lower_weighted_beta` and `rp_differential_lower_weighted_beta_uniform` on a
  one-edge set with unit covariance, where `hderiv` holds by definition of `θ'`.
-/

@[expose] public section

open StatMech.OSSS.RussoPrefactor

namespace MathlibExtTest.StatMech.Probability.OSSS.RussoPrefactor

example : 0 < Real.exp (1 * 1) - 1 := rp_denom_pos one_pos one_pos

example : (1 : ℝ) / (Real.exp (2 * 1) - 1) ≤ 1 / (Real.exp (1 * 1) - 1) :=
  rp_prefactor_antitone_beta one_pos one_pos (by norm_num)

example : ∃ cR : ℝ, 0 < cR ∧ ∀ e : Fin 3, cR ≤ (e : ℝ) + 1 :=
  rp_minPrefactor (fun e : Fin 3 => (e : ℝ) + 1) (fun _ => by positivity)

example : ∃ cR : ℝ, 0 < cR ∧ cR * ∑ _e : Unit, (1 : ℝ) ≤ 2 :=
  rp_differential_lower (fun _ => 2) (fun _ => 1) 2 (fun _ => by norm_num) (fun _ => zero_le_one)
    (by simp)

example : ∃ cR : ℝ, 0 < cR ∧ cR * ∑ _e : Unit, (1 : ℝ) ≤ 1 / (Real.exp (1 * 1) - 1) :=
  rp_differential_lower_weighted (fun _ => 1) (fun _ => 1) 1 _ (fun _ => one_pos) one_pos
    (fun _ => zero_le_one) (by simp)

example : ∃ cR : ℝ, 0 < cR ∧ cR * ∑ _e : Unit, (1 : ℝ) ≤ 1 / (1 - Real.exp (-(1 * 1))) :=
  rp_differential_lower_weighted_beta (fun _ => 1) (fun _ => 1) 1 _ (fun _ => one_pos) one_pos
    (fun _ => zero_le_one) (by simp)

example : ∃ cR : ℝ, 0 < cR ∧ (∀ _e : Unit, cR ≤ 1 / (1 - Real.exp (-(2 * 1)))) ∧
    cR * ∑ _e : Unit, (1 : ℝ) ≤ 1 / (1 - Real.exp (-(1 * 1))) :=
  rp_differential_lower_weighted_beta_uniform (fun _ => 1) (fun _ => 1) 1 2 _ (fun _ => one_pos)
    one_pos (by norm_num) (fun _ => zero_le_one) (by simp)

end MathlibExtTest.StatMech.Probability.OSSS.RussoPrefactor
