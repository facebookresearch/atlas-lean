/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.AlonBoppana
import Mathlib.Tactic.NormNum

/-! # Tests for the Alon-Boppana bound -/

namespace MathlibExtTest.Combinatorics.SimpleGraph.AlonBoppana

open MathlibExt.Combinatorics.SpectralExpander
open MathlibExt.GraphTheory.SpectralExpanderWanted (alon_boppana)

-- At degree zero, division by zero gives the lower bound `-ε`.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lam : ℝ),
      IsSpectralExpander G 0 lam → -ε ≤ lam := by
  simpa using alon_boppana 0 ε hε

-- At degree one, the square-root term vanishes.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lam : ℝ),
      IsSpectralExpander G 1 lam → -ε ≤ lam := by
  simpa using alon_boppana 1 ε hε

-- Degree two includes disconnected unions of cycles; no connectedness hypothesis is needed.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lam : ℝ),
      IsSpectralExpander G 2 lam → 1 - ε ≤ lam := by
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using alon_boppana 2 ε hε

end MathlibExtTest.Combinatorics.SimpleGraph.AlonBoppana
