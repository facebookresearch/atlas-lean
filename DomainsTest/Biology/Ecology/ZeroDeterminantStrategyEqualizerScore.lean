/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.ZeroDeterminantStrategyEqualizerScore
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for equalizer strategies

For payoffs `R = 3`, `S = 0`, `T = 5`, `P = 1`, the strategy
`p = (3/4, 1/4, 1/2, 1/4)` gives Y score `2` in every stationary distribution.

## References

* W. H. Press and F. J. Dyson, "Iterated Prisoner's Dilemma contains strategies that
  dominate any evolutionary opponent", Proc. Natl. Acad. Sci. USA 109 (2012) 10409–10413,
  "X unilaterally sets Y's score", eqs. (8)–(9).
-/

open WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted

namespace DomainsTest.Biology.Ecology.ZeroDeterminantStrategyEqualizerScore

private noncomputable def pEx : Fin 4 → ℝ := ![3 / 4, 1 / 4, 1 / 2, 1 / 4]

private theorem isStrategy_pEx : IsStrategy pEx := by
  intro i
  fin_cases i <;> norm_num [pEx, Set.mem_Icc]

private theorem hp2_pEx :
    pEx 1 = (pEx 0 * (5 - 1) - (1 + pEx 3) * (5 - 3)) / (3 - 1) := by
  norm_num [pEx]

private theorem hp3_pEx :
    pEx 2 = ((1 - pEx 0) * (1 - 0) + pEx 3 * (3 - 0)) / (3 - 1) := by
  norm_num [pEx]

private theorem hden_pEx : (1 - pEx 0) + pEx 3 ≠ 0 := by
  norm_num [pEx]

private theorem concrete_equalizer_score {q : Fin 4 → ℝ} (hq : IsStrategy q) {v : Fin 4 → ℝ}
    (hv : IsStationary (markovMatrix pEx q) v) :
    v ⬝ᵥ payoffY 3 0 5 1 = 2 := by
  have h := equalizer_score (R := 3) (S := 0) (T := 5) (P := 1)
    (by norm_num : (3 : ℝ) ≠ 1) isStrategy_pEx hp2_pEx hp3_pEx hden_pEx hq hv
  have hvalue : ((1 - pEx 0) * 1 + pEx 3 * 3) / ((1 - pEx 0) + pEx 3) = 2 := by
    norm_num [pEx]
  simpa only [hvalue] using h

end DomainsTest.Biology.Ecology.ZeroDeterminantStrategyEqualizerScore
