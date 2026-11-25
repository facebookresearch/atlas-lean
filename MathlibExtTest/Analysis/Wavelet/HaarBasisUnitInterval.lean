/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Wavelet.HaarBasisUnitInterval

open MeasureTheory Set
open MathlibExt.Analysis.Wavelet.Haar
open MathlibExt.Analysis.Wavelet.HaarBasisWanted

local notation "unitVol" => volume.restrict (Ico (0 : ℝ) 1)

-- At the coarsest split, the constant plus the wavelet is twice the left-half indicator.
example : ∃ b : HilbertBasis (Option (Σ k : ℕ, Fin (2 ^ k))) ℝ (Lp ℝ 2 unitVol),
    b none + b (some ⟨0, 0⟩) =
      indicatorConstLp 2 (measurableSet_Ico (a := (0 : ℝ)) (b := 1 / 2))
        (measure_ne_top unitVol _) (2 : ℝ) := by
  obtain ⟨b, h1, hH⟩ := exists_hilbertBasis_haar_unitInterval
  refine ⟨b, Lp.ext ?_⟩
  filter_upwards [Lp.coeFn_add (b none) (b (some ⟨0, 0⟩)), h1, hH 0 0,
    indicatorConstLp_coeFn (p := 2) (μ := unitVol) (s := Ico (0 : ℝ) (1 / 2))
      (hs := measurableSet_Ico) (hμs := measure_ne_top _ _) (c := (2 : ℝ)),
    ae_restrict_mem (μ := volume) (s := Ico (0 : ℝ) 1) measurableSet_Ico]
    with x hadd hc hw hi hx
  simp only [Pi.add_apply, hc, hw] at hadd
  rw [hadd, hi]
  by_cases hl : x ∈ Ico (0 : ℝ) (1 / 2)
  · rw [indicator_of_mem hl]
    norm_num [haarSystem, haarFunction_eq_one hl]
  · have hr : x ∈ Ico (1 / 2 : ℝ) 1 := ⟨le_of_not_gt fun h => hl ⟨hx.1, h⟩, hx.2⟩
    rw [indicator_of_notMem hl]
    norm_num [haarSystem, haarFunction_eq_neg_one hr]
