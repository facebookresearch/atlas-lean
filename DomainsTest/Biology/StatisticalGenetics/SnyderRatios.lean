/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.SnyderRatios
import Mathlib.Tactic.NormNum

/-!
# Tests for Snyder's ratios

At allele frequency `q = 1 / 2`, Snyder's `S = q / (1 + q)` is `1 / 3`, Snyder's
`R = (q / (1 + q))²` is `1 / 9`, `R = S²` holds, and `√B = q` recovers the allele frequency.
-/

@[expose] public section

open WantedExt.Biology.StatisticalGenetics.SnyderRatiosWanted

namespace DomainsTest.Biology.StatisticalGenetics.SnyderRatios

/-- At `q = 1 / 2`, Snyder's `S` is `1 / 3`. -/
example : ratioDominantRecessive (1 / 2) = 1 / 3 := by
  rw [(snyder_ratios (1 / 2) (by norm_num) (by norm_num)).1]
  norm_num

/-- At `q = 1 / 2`, Snyder's `R` is `1 / 9`. -/
example : ratioDominantDominant (1 / 2) = 1 / 9 := by
  rw [(snyder_ratios (1 / 2) (by norm_num) (by norm_num)).2.1]
  norm_num

/-- At `q = 1 / 2`, Snyder's `R = S²` identity holds. -/
example : ratioDominantDominant (1 / 2) = (ratioDominantRecessive (1 / 2)) ^ 2 :=
  (snyder_ratios (1 / 2) (by norm_num) (by norm_num)).2.2.1

/-- At `q = 1 / 2`, `√B` recovers the allele frequency. -/
example : Real.sqrt (recessiveFreq (1 / 2)) = 1 / 2 :=
  (snyder_ratios (1 / 2) (by norm_num) (by norm_num)).2.2.2

end DomainsTest.Biology.StatisticalGenetics.SnyderRatios
