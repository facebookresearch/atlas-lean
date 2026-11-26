/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.SubcriticalCrossingDecay

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.SubcriticalCrossingDecay`

* `theta_mul_one_sub_ge_of_bounded` at `θ = 1/4`, `κ = 1/2`;
* non-vacuity of `osss_subcritical_decay_of_bounds`: all hypotheses discharged for the zero
  profile `θn = θn' = S = 0` on `[0, 1]`;
* `osss_subcritical_decay_of_bounds` in its conditional form;
* `cov_crossbox_uncond` and `osss_crossing_decay_of_connComparison` stated by name.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.SubcriticalCrossingDecay

open Set
open _root_.StatMech _root_.StatMech.OSSS

-- The elementary bound `θ κ ≤ θ (1 - θ)` at explicit values.
example : (1 / 4 : ℝ) * (1 / 2) ≤ 1 / 4 * (1 - 1 / 4) :=
  theta_mul_one_sub_ge_of_bounded (by norm_num) (by norm_num)

-- Non-vacuity: the zero profile satisfies every hypothesis of the decay lemma.
example : (0 : ℝ) ≤ Real.exp (-(((1 : ℕ) : ℝ) * 1 * 1 / 1 * (1 / 2) * (1 - 0))) :=
  osss_subcritical_decay_of_bounds 1 1 1 1 (1 / 2) 0 1 one_pos one_pos one_pos one_pos le_rfl
    (by norm_num) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun x _ => hasDerivAt_const x 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => le_rfl) (fun _ _ => by norm_num)
    le_rfl (by norm_num)

-- The decay lemma, conditional on its hypotheses.
example (n : ℕ) (c₀ cR D κ a b : ℝ) (hab : a < b) (hD : 0 < D) (hcR : 0 < cR) (hc₀ : 0 < c₀)
    (hn : 1 ≤ n) (hκ : 0 < κ) (θn θn' S : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
    (hcov : ∀ x ∈ Icc a b, (n : ℝ) * c₀ * (θn x * (1 - θn x)) ≤ D * S x)
    (hRusso : ∀ x ∈ Icc a b, θn' x = cR * S x) (hθnn : ∀ x ∈ Icc a b, 0 ≤ θn x)
    (hθub : ∀ x ∈ Icc a b, θn x ≤ 1 - κ) (hθa : 0 ≤ θn a) (hθb : θn b ≤ 1) :
    θn a ≤ Real.exp (-((n : ℝ) * c₀ * cR / D * κ * (b - a))) :=
  osss_subcritical_decay_of_bounds n c₀ cR D κ a b hab hD hcR hc₀ hn hκ θn θn' S hd hcov hRusso
    hθnn hθub hθa hθb

-- The geometric headline lemmas exist with the expected names.
example := @cov_crossbox_uncond
example := @osss_crossing_decay_of_connComparison

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.SubcriticalCrossingDecay
