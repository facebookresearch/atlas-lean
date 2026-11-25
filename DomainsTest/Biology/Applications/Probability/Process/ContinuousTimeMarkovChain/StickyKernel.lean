/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.StickyKernel
public import Domains.Biology.Phylogenetics.SubstitutionModels

/-! The F81 generator and its transition function on four bases. -/

@[expose] public section

open Finset Matrix ProbabilityTheory

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.StickyKernel

open MathlibExt.Biology.Phylogenetics.SubstitutionModels in
/-- F81 (Felsenstein 1981) on four bases is the equal-input generator with rate `1`. -/
theorem f81Rate_eq_equalInputRate {π : Fin 4 → ℝ} (hπ : ∑ i, π i = 1) :
    f81Rate π = equalInputRate π 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [f81Rate, gtrRate, equalInputRate, hπ]
  · simp [f81Rate, gtrRate, equalInputRate, h]

open MathlibExt.Biology.Phylogenetics.SubstitutionModels in
-- Hence the F81 transition function is the sticky kernel with persistence `e^{-t}`.
example {π : Fin 4 → ℝ} (hπ : ∑ i, π i = 1) (t : ℝ) :
    ctmcTransition (f81Rate π) t = stickyKernel π (Real.exp (-t)) := by
  rw [f81Rate_eq_equalInputRate hπ, ctmcTransition_equalInputRate hπ, one_mul]

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.StickyKernel
