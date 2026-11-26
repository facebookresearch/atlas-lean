/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.ZeroCounts
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.NormNum

namespace ComplexZeroCounts

example (f : ℂ → ℂ) (S : Set ℂ) (a : ℝ) : windowZeros f S a a = ∅ := by
  ext z
  simp only [windowZeros, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
  exact ⟨fun h => (not_lt_of_ge h.2.2.2) h.2.2.1, False.elim⟩

example : (3 + Complex.I : ℂ) ∈ windowZeros (fun _ => 0) Set.univ 0 1 := by
  norm_num [windowZeros, Complex.add_im]

example : (3 + Complex.I : ℂ) ∉ windowZeros (fun _ => 0) openCriticalStrip 0 1 := by
  norm_num [windowZeros, openCriticalStrip, Complex.add_re]

example : countWithMultiplicity (fun z : ℂ => z ^ 2) ({0} : Set ℂ) = 2 := by
  rw [countWithMultiplicity, finsum_mem_singleton]
  have h : AnalyticAt ℂ (id : ℂ → ℂ) 0 := analyticAt_id
  change (analyticOrderAt ((id : ℂ → ℂ) ^ 2) 0).toNat = 2
  rw [analyticOrderAt_pow h]
  simp

end ComplexZeroCounts
