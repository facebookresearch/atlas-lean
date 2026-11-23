/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.InfiniteMixtureLimit

@[expose] public section

open Filter Topology Finset MathlibExt.Probability.InfiniteMixtureLimit
  MathlibExt.Biology.PopulationGenetics.ChineseRestaurant

namespace MathlibExtTest.Probability.InfiniteMixtureLimit

/-- Non-vacuity: `K (K - 1) (K - 2) / K^3 → 1`. -/
example : Tendsto (fun K : ℕ => (K.descFactorial 3 : ℝ) / (K : ℝ) ^ 3) atTop (𝓝 1) :=
  tendsto_descFactorial_div_pow 3

/-- Non-vacuity: `(1 + α/K)(2 + α/K) → 2!`. -/
example (α : ℝ) :
    Tendsto (fun K : ℕ => ∏ j ∈ range 2, ((j + 1 : ℝ) + α / K)) atTop (𝓝 2) := by
  simpa using tendsto_prod_range_add_div α 2

/-- With fewer classes than blocks the closed form vanishes. -/
example (α : ℝ) : finitePartitionProb α 0 (⊥ : Finpartition (univ : Finset (Fin 2))) = 0 := by
  simp [finitePartitionProb]

/-- The limit for the partition of two objects into singletons. -/
example (α : ℝ) : Tendsto (fun K : ℕ => finitePartitionProb α K
    (⊥ : Finpartition (univ : Finset (Fin 2)))) atTop
    (𝓝 (crpProb α (⊥ : Finpartition (univ : Finset (Fin 2))))) :=
  tendsto_finitePartitionProb α _

/-- Sanity check of the recorded closed form: for two objects and `K ≥ 1` classes, the
probabilities of the two partitions (one block, two singletons) sum to one. -/
example {α : ℝ} (hα : 0 < α) {K : ℕ} (hK : K ≠ 0) :
    finitePartitionProb α K (⊤ : Finpartition (univ : Finset (Fin 2))) +
      finitePartitionProb α K (⊥ : Finpartition (univ : Finset (Fin 2))) = 1 := by
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  have htop : (⊤ : Finpartition (univ : Finset (Fin 2))).parts = {univ} :=
    (Finpartition.parts_nonempty _ (by simpa using univ_nonempty.ne_empty)).subset_singleton_iff.1
      (Finpartition.parts_top_subset _)
  have hbot : (⊥ : Finpartition (univ : Finset (Fin 2))).parts =
      univ.map ⟨singleton, singleton_injective⟩ := Finpartition.parts_bot univ
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := Nat.exists_eq_succ_of_ne_zero hK
  simp only [finitePartitionProb, Finpartition.cardProd, htop, hbot, card_singleton, card_map,
    card_univ, Fintype.card_fin, prod_singleton, prod_map, Function.Embedding.coeFn_mk,
    Nat.descFactorial_one, Nat.descFactorial, ascPochhammer_succ_eval, ascPochhammer_zero,
    Polynomial.eval_one]
  have hα1 : α + 1 ≠ 0 := by positivity
  simp
  field_simp
  ring

end MathlibExtTest.Probability.InfiniteMixtureLimit
