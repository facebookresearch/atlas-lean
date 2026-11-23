/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.CurrentRep

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.CurrentRep`

* `partitionJ_eq_currentSum`: the sourceless current sum is `Z / 2^{|V|}`, hence positive, on the
  single edge `⊤ : SimpleGraph (Fin 2)`.
* `current_representation` on the single edge at `β = 1`, `J = 1`: `⟨σ_0 σ_1⟩` is the ratio of
  current sums with sources `{0, 1}` and `∅`; for `A = ∅` both sides are `1`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.CurrentRep

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Sharpness

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- The sourceless current sum is positive. -/
lemma currentSum_empty_pos (β : ℝ) (J : Sym2 (Fin 2) → ℝ) : 0 < currentSum edge β J ∅ := by
  have hZ : 0 < partitionJ edge β J :=
    Finset.sum_pos (fun s _ => boltzmannJ_pos edge β J s) Finset.univ_nonempty
  rw [partitionJ_eq_currentSum] at hZ
  exact pos_of_mul_pos_right hZ (by positivity)

-- The random-current representation of `⟨σ_0 σ_1⟩` on the single edge.
example : expectationJ edge 1 (fun _ => 1) {0, 1} =
    currentSum edge 1 (fun _ => 1) {0, 1} / currentSum edge 1 (fun _ => 1) ∅ :=
  current_representation edge 1 (fun _ => 1) {0, 1}

-- For `A = ∅` the representation reads `⟨1⟩ = 1`.
example (β : ℝ) (J : Sym2 (Fin 2) → ℝ) : expectationJ edge β J ∅ = 1 := by
  rw [current_representation, div_self (currentSum_empty_pos β J).ne']

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.CurrentRep
