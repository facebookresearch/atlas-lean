/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Assembly.LanderWaterman
public meta import CSLibExt.Bioinformatics.Assembly.LanderWaterman

/-!
# Lander–Waterman coverage tests

Executed fixtures: exhaustive counts over all `5 ^ 3 = 125` start tuples of `N = 3` reads of length
`L = 2` on a circular genome of length `G = 5` (uncovered base `3 ^ 3 = 27`; depth law
`27, 54, 36, 8`; island ends `3 * 5 * 4 ^ 2 = 240`) and the boundary `L = G` (every base covered);
the junk regime `L > G`, outside the hypothesis `L ≤ G`, where the count formula fails. Also a
non-vacuity witness for the hypotheses of the limit theorems: `G N = 2 (N + 1)`, `L = 2`, so
`N L / G N = N / (N + 1) → 1`.
-/

namespace Cslib.Bioinformatics.Assembly.LanderWaterman

open Filter Topology

-- Exhaustive counts, `G = 5`, `L = 2`, `N = 3`.
#guard (Finset.univ.filter fun s : Fin 3 → Fin 5 => ∀ j, ¬ Covers 5 2 (s j) 0).card = 27
#guard (List.range 4).map (fun k =>
  (Finset.univ.filter fun s : Fin 3 → Fin 5 => depth 2 s 0 = k).card) = [27, 54, 36, 8]
#guard (List.range 4).all fun k =>
  (Finset.univ.filter fun s : Fin 3 → Fin 5 => depth 2 s 0 = k).card =
    Nat.choose 3 k * 2 ^ k * 3 ^ (3 - k)
#guard (∑ j : Fin 3, (Finset.univ.filter fun s : Fin 3 → Fin 5 => NoSuccessor 2 s j).card) = 240
-- `L = G`: every read covers every base.
#guard (Finset.univ.filter fun s : Fin 2 → Fin 4 => ∀ j, ¬ Covers 4 4 (s j) 1).card = 0
-- Outside `L ≤ G` the island count formula fails: here `G - (L - 1) = 0`, but tuples with all
-- reads at one position have no successors.
#guard (∑ j : Fin 2, (Finset.univ.filter fun s : Fin 2 → Fin 3 => NoSuccessor 5 s j).card) = 6

/-- The exact laws, instantiated. -/
example : uniformProb (Finset.univ.filter fun s : Fin 3 → Fin 5 =>
    ∀ j, ¬ Covers 5 2 (s j) 0) = (1 - (2 : ℝ) / 5) ^ 3 :=
  uniformProb_uncovered (by norm_num) 0

/-- Non-vacuity of the limit hypotheses: `G N = 2 (N + 1) ≥ 2` and `N * 2 / G N → 1`. -/
example : Tendsto (fun N => uniformProb (Finset.univ.filter fun s : Fin N → Fin (2 * (N + 1)) =>
    ∀ j, ¬ Covers (2 * (N + 1)) 2 (s j) ⟨0, by omega⟩)) atTop (𝓝 (Real.exp (-1))) := by
  refine tendsto_uniformProb_uncovered 2 (fun N => 2 * (N + 1)) (fun N => by omega) 1 ?_ _
  have h := tendsto_natCast_div_add_atTop (1 : ℝ)
  refine h.congr fun N => ?_
  push_cast
  field_simp

end Cslib.Bioinformatics.Assembly.LanderWaterman
