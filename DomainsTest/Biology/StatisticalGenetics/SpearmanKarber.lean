/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.StatisticalGenetics.SpearmanKarber
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace DomainsTest.Biology.StatisticalGenetics.SpearmanKarber

open WantedExt.Biology.StatisticalGenetics.SpearmanKarberWanted

-- The least allowed grid has no interior point.
example (x₀ d : ℝ) (p : Fin 2 → ℝ) (h₀ : p 0 = 0) (h₁ : p (Fin.last 1) = 1) :
    spearmanKarber x₀ d p = x₀ + d / 2 := by
  rw [spearmanKarber_eq x₀ d 1 (by decide) p h₀ h₁, Fin.sum_univ_two]
  norm_num [h₀, show p 1 = 1 from h₁]
  ring

-- The next grid keeps its arbitrary real interior value with coefficient -d.
example (x₀ d : ℝ) (p : Fin 3 → ℝ) (h₀ : p 0 = 0) (h₂ : p (Fin.last 2) = 1) :
    spearmanKarber x₀ d p = x₀ + (3 / 2 - p 1) * d := by
  rw [spearmanKarber_eq x₀ d 2 (by decide) p h₀ h₂, Fin.sum_univ_three]
  norm_num [h₀, show p 2 = 1 from h₂]
  ring

end DomainsTest.Biology.StatisticalGenetics.SpearmanKarber
