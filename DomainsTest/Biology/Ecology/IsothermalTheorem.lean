/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.IsothermalTheorem
import Mathlib.Tactic.NormNum

/-!
# Tests for the isothermal theorem

On the uniform two-vertex graph, the average single-mutant fixation probabilities are
`2/3` for fitness `2` and `1/3` for fitness `1/2`.

Sources: E. Lieberman, C. Hauert and M. A. Nowak, "Evolutionary dynamics on graphs", Nature 433
(2005) 312–316, p. 313 and eq. (1).
-/

namespace DomainsTest.Biology.Ecology.IsothermalTheorem

open Finset WantedExt.Biology.Ecology.IsothermalTheoremWanted

private noncomputable def uniformTwo : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 2

private theorem uniform_average (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1)
    (φ : Finset (Fin 2) → ℝ) (hφ : IsFixationFunction r uniformTwo φ) :
    (∑ v, φ {v}) / 2 = moranFixation r 2 := by
  apply average_fixation_eq_moranFixation (by decide) r hr hr1 uniformTwo
  · intro i j
    norm_num [uniformTwo]
  · intro i
    norm_num [uniformTwo]
  · intro j
    norm_num [uniformTwo]
  · intro i j
    exact ⟨1, by rw [pow_one]; norm_num [uniformTwo]⟩
  · exact hφ

example (φ : Finset (Fin 2) → ℝ) (hφ : IsFixationFunction 2 uniformTwo φ) :
    (∑ v, φ {v}) / 2 = 2 / 3 := by
  convert uniform_average 2 (by norm_num) (by norm_num) φ hφ using 1
  norm_num [moranFixation]

example (φ : Finset (Fin 2) → ℝ) (hφ : IsFixationFunction (1 / 2) uniformTwo φ) :
    (∑ v, φ {v}) / 2 = 1 / 3 := by
  convert uniform_average (1 / 2) (by norm_num) (by norm_num) φ hφ using 1
  norm_num [moranFixation]

end DomainsTest.Biology.Ecology.IsothermalTheorem
