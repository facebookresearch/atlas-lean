/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.ContinuedFractions.MobiusContinuedFractions

open Filter Topology

-- Equality in the coefficient bound can give a limit on the unit circle.
example :
    Tendsto (fun n ↦ (⟨0, Stream'.Seq.ofStream fun _ ↦ ⟨-1, 2⟩⟩ : GenContFract ℂ).convs' n)
      atTop (𝓝 (-1)) := by
  let g : GenContFract ℂ := ⟨0, Stream'.Seq.ofStream fun _ ↦ ⟨-1, 2⟩⟩
  obtain ⟨v, hv, hlim⟩ := MetaMathlibExt.contFract_tendsto_of_pringsheim
    (fun _ ↦ -1) (fun _ ↦ 2) (by intro k; norm_num)
  change Tendsto g.convs' atTop (𝓝 v) at hlim
  have hden : 2 + v ≠ 0 := by
    intro h
    have : v = -2 := by linear_combination h
    norm_num [this] at hv
  have hrec (n : ℕ) : g.convs' (n + 1) = -1 / (2 + g.convs' n) := by
    simp only [g, GenContFract.convs', zero_add]
    rfl
  have hnext : Tendsto (fun n ↦ g.convs' (n + 1)) atTop (𝓝 v) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  simp only [hrec] at hnext
  have hfix := tendsto_nhds_unique hnext (tendsto_const_nhds.div (tendsto_const_nhds.add hlim) hden)
  have hsquare : (v + 1) ^ 2 = 0 := by linear_combination (eq_div_iff hden).mp hfix
  have hroot : v + 1 = 0 := eq_zero_of_pow_eq_zero hsquare
  have : v = -1 := by linear_combination hroot
  simpa only [this] using hlim

-- A zero second numerator cuts off all deeper terms and preserves the first approximant.
example (n : ℕ) :
    (⟨0, Stream'.Seq.ofStream fun k ↦ ⟨if k = 1 then 0 else Complex.I, 2⟩⟩ :
      GenContFract ℂ).convs' (n + 1) = Complex.I / 2 := by
  cases n with
  | zero =>
    change 0 + Complex.I / (2 + 0) = _
    simp
  | succ n =>
    change 0 + Complex.I / (2 + 0 / (2 + _)) = _
    simp
