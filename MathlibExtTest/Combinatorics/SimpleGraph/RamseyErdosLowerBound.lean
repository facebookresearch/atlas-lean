/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound

@[expose] public section

open SimpleGraph MathlibExt.Combinatorics.RamseyErdosLowerBound

namespace MathlibExtTest.Combinatorics.SimpleGraph.RamseyErdosLowerBound

/-- `R(4, 4) > 6`: `C(6, 4) · 2^{1 - 6} = 15/32 < 1`. -/
example : ¬ classicalRamsey 4 4 6 :=
  not_classicalRamsey_of_choose_mul_lt 4 (by norm_num [Nat.choose])

/-- `R(5, 5) > 11`: `C(11, 5) · 2^{1 - 10} = 462/512 < 1`. -/
example : ¬ classicalRamsey 5 5 11 :=
  not_classicalRamsey_of_choose_mul_lt 5 (by norm_num [Nat.choose])

/-- Every `N` with the Ramsey property for `K_5` exceeds `11`. -/
example {N : ℕ} (hN : classicalRamsey 5 5 N) : 11 < N :=
  lt_of_classicalRamsey_of_choose_mul_lt 5 (by norm_num [Nat.choose]) hN

/-- The existence form: a graph on `6` vertices with no `K_4` in it or in its complement. -/
example : ∃ G : SimpleGraph (Fin 6),
    ¬ (completeGraph (Fin 4)).IsContained G ∧ ¬ (completeGraph (Fin 4)).IsContained Gᶜ :=
  exists_not_isContained_of_choose_mul_lt 4 (by norm_num [Nat.choose])

/-- `R(5, 5) > 11` for the repository's `graphRamsey`, with no extra hypothesis. -/
example : 11 < graphRamsey 5 5 :=
  lt_graphRamsey_of_choose_mul_lt 5 (by norm_num [Nat.choose])

/-- Ramsey numbers for cliques exist. -/
example : ∃ N, classicalRamsey 3 4 N := exists_classicalRamsey 3 4

/-- Monotonicity of the Ramsey property in the number of vertices. -/
example (h : classicalRamsey 3 3 6) : classicalRamsey 3 3 10 :=
  classicalRamsey_mono (by norm_num) h

/-- The pairs inside a `3`-set number `C(3, 2) = 3`. -/
example : (pairsIn ({0, 1, 2} : Finset (Fin 5))).card = 3 := by
  rw [card_pairsIn]
  decide

end MathlibExtTest.Combinatorics.SimpleGraph.RamseyErdosLowerBound
