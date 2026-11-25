/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.SimpleGraph.RamseyFourFour
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # Boundary tests for the Ramsey number `R(4, 4)` -/

namespace MathlibExtTest.RamseyFourFour

open SimpleGraph MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted
open MathlibExt.Combinatorics.RamseyErdosLowerBound

-- Every graph on eighteen vertices contains a `K_4` or an independent `4`-set.
example (G : SimpleGraph (Fin 18)) :
    (completeGraph (Fin 4)).IsContained G ∨ (completeGraph (Fin 4)).IsContained Gᶜ := by
  have h : classicalRamsey 4 4 (graphRamsey 4 4) :=
    Nat.sInf_mem (s := {n | classicalRamsey 4 4 n}) (exists_classicalRamsey 4 4)
  rw [graphRamsey_four_four] at h
  exact h G

-- The Ramsey property for `(4, 4)` fails on seventeen vertices.
example : ¬ classicalRamsey 4 4 17 := by
  intro h
  have hle : graphRamsey 4 4 ≤ 17 := Nat.sInf_le h
  rw [graphRamsey_four_four] at hle
  omega

-- It fails on every smaller number of vertices too.
example {N : ℕ} (hN : N ≤ 17) : ¬ classicalRamsey 4 4 N := by
  intro h
  have hle : graphRamsey 4 4 ≤ 17 := Nat.sInf_le (classicalRamsey_mono hN h)
  rw [graphRamsey_four_four] at hle
  omega

-- Some graph on seventeen vertices has no `K_4` and no independent set of size `4`.
example : ∃ G : SimpleGraph (Fin 17), G.CliqueFree 4 ∧ G.IndepSetFree 4 := by
  have h : ¬ classicalRamsey 4 4 17 := by
    intro h
    have hle : graphRamsey 4 4 ≤ 17 := Nat.sInf_le h
    rw [graphRamsey_four_four] at hle
    omega
  simpa [classicalRamsey, ← not_cliqueFree_iff_top_isContained] using h

end MathlibExtTest.RamseyFourFour
