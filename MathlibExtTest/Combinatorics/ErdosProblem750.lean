/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ErdosProblem750
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

/-! # Finite-set bounds for Erdős Problem 750 -/

open Filter
open scoped NNReal
open MathlibExt.Combinatorics.ErdosProblem750Wanted

-- The error may vanish on an arbitrarily long initial segment.
example (k : ℕ) :
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ (m : ℕ) (S : Set V), 0 < m → m ≤ k → S.ncard = m →
        ∃ I ⊆ S, G.IsIndepSet I ∧ (m : ℝ) / 2 ≤ I.ncard := by
  have ht : Tendsto (fun m : ℕ => ((m - k : ℕ) : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat k)
  obtain ⟨V, G, hχ, hG⟩ := conjecture_holds.1 _ ht
  refine ⟨V, G, hχ, fun m S hm hmk hS => ?_⟩
  simpa [Nat.sub_eq_zero_of_le hmk] using hG m S hm hS

-- With linear error m/8, every eight vertices contain an independent triple.
example :
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ S : Set V, S.ncard = 8 → ∃ I ⊆ S, G.IsIndepSet I ∧ 3 ≤ I.ncard := by
  obtain ⟨V, G, hχ, hG⟩ := conjecture_holds.2.1 (1 / 8) (by norm_num)
  refine ⟨V, G, hχ, fun S hS => ?_⟩
  obtain ⟨I, hI, hind, hcard⟩ := hG 8 S (by decide) hS
  refine ⟨I, hI, hind, ?_⟩
  norm_num at hcard
  exact_mod_cast hcard
