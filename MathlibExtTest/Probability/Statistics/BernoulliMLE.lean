/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.BernoulliMLE

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.BernoulliMLE

open MathlibExt.Probability.Statistics.BernoulliMLE

/-- Concrete test: three successes out of four gives sample proportion
`3 / 4`. -/
example : sampleProportion (![true, true, true, false] : Fin 4 → Bool) = 3 / 4 := by
  have hcard : (Finset.univ.filter
      (fun i : Fin 4 => ![true, true, true, false] i = true)).card = 3 := by
    decide
  unfold sampleProportion
  rw [hcard]
  norm_num

/-- Concrete test: the likelihood of `![true, true, true, false]` at its
sample proportion is `27 / 256`. -/
example : bernoulliLikelihood (![true, true, true, false] : Fin 4 → Bool)
    (3 / 4 : ℝ) = 27 / 256 := by
  have hcard : (Finset.univ.filter
      (fun i : Fin 4 => ![true, true, true, false] i = true)).card = 3 := by
    decide
  rw [bernoulliLikelihood_eq_pow, hcard]
  norm_num

/-- Concrete test: no `θ ∈ [0, 1]` beats `27 / 256` for that sample. -/
example : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
    bernoulliLikelihood (![true, true, true, false] : Fin 4 → Bool) θ ≤ 27 / 256 := by
  intro θ hθ
  have hle := bernoulliLikelihood_le (![true, true, true, false] : Fin 4 → Bool)
    (by norm_num) hθ
  have e1 : sampleProportion (![true, true, true, false] : Fin 4 → Bool)
      = 3 / 4 := by
    have hcard : (Finset.univ.filter
        (fun i : Fin 4 => ![true, true, true, false] i = true)).card = 3 := by
      decide
    unfold sampleProportion
    rw [hcard]
    norm_num
  have e2 : bernoulliLikelihood (![true, true, true, false] : Fin 4 → Bool)
      (3 / 4 : ℝ) = 27 / 256 := by
    have hcard : (Finset.univ.filter
        (fun i : Fin 4 => ![true, true, true, false] i = true)).card = 3 := by
      decide
    rw [bernoulliLikelihood_eq_pow, hcard]
    norm_num
  rw [e1, e2] at hle
  exact hle

end MathlibExtTest.Probability.Statistics.BernoulliMLE
