/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluencePBiased

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluencePBiased`

On `ConfigSpace (Fin 2)` with the event `A = {ω | ω 0 = true}`:
* `pBiasedCorrection (1/2) = 0`, and `pBiasedCorrection_le_one_sixteenth` at `p = 1/3`;
* `maxInfluence_pbiased_corrected` at `p = 1/3` (unconditional);
* `maxInfluence_pbiased_of_hypercontractive` in conditional form, given hypercontractivity.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluencePBiased

open _root_.StatMech _root_.StatMech.BeffaraDC

/-- The event "coordinate `0` is open". -/
def A : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

-- The correction vanishes at `p = 1/2`.
example : pBiasedCorrection (1 / 2) = 0 := by norm_num [pBiasedCorrection]

-- The correction is at most `1/16`.
example : pBiasedCorrection (1 / 3) ≤ 1 / 16 :=
  pBiasedCorrection_le_one_sixteenth (by norm_num) (by norm_num)

-- The corrected KKL bound at `p = 1/3`.
example := maxInfluence_pbiased_corrected (E := Fin 2) (p := 1 / 3) (by norm_num) (by norm_num) A

-- The sharp bound, given `p`-biased hypercontractivity.
example (H : Probability.KKLHypercontractive (1 / 3) 2) :=
  maxInfluence_pbiased_of_hypercontractive (E := Fin 2) (by norm_num) (by norm_num) H A

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluencePBiased
