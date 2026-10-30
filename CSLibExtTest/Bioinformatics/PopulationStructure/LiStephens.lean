/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationStructure.LiStephens
public meta import CSLibExt.Bioinformatics.PopulationStructure.LiStephens
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Li–Stephens copying model tests

Non-vacuity: with `K = 3`, `ρ = 1/10`, `ε = 1/100` over `ℚ` the model is a probability model
(transition rows, the initial law and the biallelic emissions sum to `1`). Closed checks: one
site and the switch probabilities by `norm_num`. Executed fixtures: on a 3-haplotype panel and
a 4-site target, the `O(K)` recursion, its tabulation and the generic forward algorithm agree
with the brute-force likelihood over all `3 ^ 4` copying paths, for several `(ρ, ε)`, including
the boundary cases `ρ = 0` (no switching) and `ρ = 1` (a fresh uniform haplotype at every
site). Junk-value probes document a negative weight outside the domain (`ρ = 2`), the exact
threshold `ρ = K / (K - 1)`, and that the emissions are normalized only over the target allele.
Each run throws on a disagreement.
-/

namespace Cslib.Bioinformatics.PopulationStructure.LiStephens

open Cslib.MachineLearning.Sequence.HiddenMarkov

/-! ## Non-vacuity: a genuine probability model -/

example (k : Fin 3) : ∑ k', trans (1 / 10 : ℚ) k k' = 1 :=
  trans_row_sum (K := 3) (by norm_num) _ k
example : ∑ k, (hmm (A := Bool) 3 (1 / 10 : ℚ) (1 / 100)).init k = 1 :=
  init_sum (K := 3) (by norm_num) _ _
example (k : Fin 3) (col : Fin 3 → Bool) : ∑ a : Bool, emit (1 / 100 : ℚ) k (col, a) = 1 :=
  emit_sum_bool _ k col

-- Staying put: `(1 - ρ) + ρ / K`; switching to another haplotype: `ρ / K`.
example : trans (1 / 10 : ℚ) (0 : Fin 3) 0 = 1 - 1 / 10 + 1 / 30 := by
  simp [trans]; norm_num
example : trans (1 / 10 : ℚ) (0 : Fin 3) 1 = 1 / 30 := by
  simp [trans]; norm_num

-- Outside the parameter domain (`ρ = 2`) the weights are not probabilities: staying has
-- negative weight `1 - 2 + 2/3`, although the rows still sum to `1`.
example : trans (2 : ℚ) (0 : Fin 3) 0 = -1 / 3 := by
  simp [trans]; norm_num

-- For `K = 3` the staying weight is negative only beyond `ρ = K / (K - 1) = 3/2`: at
-- `ρ = 11/10` the row is still stochastic, and at `ρ = 3/2` the staying weight is `0`.
example : trans (11 / 10 : ℚ) (0 : Fin 3) 0 = 4 / 15 := by
  simp [trans]; norm_num
example : trans (3 / 2 : ℚ) (0 : Fin 3) 0 = 0 := by
  simp [trans]; norm_num

-- The emissions are conditional on the panel column: over the whole observation type
-- `(Fin 1 → Bool) × Bool` they sum to `2`, not `1`.
example : ∑ o : (Fin 1 → Bool) × Bool, emit (1 / 100 : ℚ) 0 o = 2 := by
  decide +kernel

/-! ## Executed fixtures -/

/-- A reference panel of three biallelic haplotypes over four sites. -/
def panel : Fin 3 → ℕ → Bool
  | 0, t => t % 2 == 0
  | 1, t => t < 2
  | 2, _ => true

/-- A target haplotype: a mosaic of the panel with one mismatch at site `3`. -/
def target (t : ℕ) : Bool := t == 0 || t == 1

/-- Brute-force likelihood check of all three algorithms at sites `0, …, t`. -/
def agree (ρ ε : ℚ) (t : ℕ) : Bool :=
  let y := obs panel target
  let brute := likelihood (hmm 3 ρ ε) y t
  brute == ∑ k, fastForward ρ ε y t k && brute == likelihoodTab ρ ε y t &&
    brute == ∑ k, forward (hmm 3 ρ ε) y t k

#guard [(1 / 10, 1 / 100), (0, 1 / 100), (1, 1 / 100), (1 / 2, 0), (1 / 3, 1 / 2)].all
  fun (p : ℚ × ℚ) => (List.range 4).all (agree p.1 p.2)

-- With `ρ = 0` and `ε = 0` the likelihood is `1/K` times the number of panel haplotypes that
-- match the target exactly; haplotype `1` matches at sites `0, 1, 2`.
#guard likelihood (hmm 3 (0 : ℚ) 0) (obs panel target) 2 = 1 / 3

end Cslib.Bioinformatics.PopulationStructure.LiStephens
