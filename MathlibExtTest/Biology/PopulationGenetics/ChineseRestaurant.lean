/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.ChineseRestaurant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Tests for the Chinese restaurant process

The empty restaurant (`n = 0`); the all-alone partition `⊥` (every customer at their own table)
has probability `θ^n / θ^{(n)}`, and the one-table partition `⊤` has probability
`(n - 1)! θ / θ^{(n)}`; for two customers these are `θ / (θ + 1)` and `1 / (θ + 1)`, and they
sum to one; exchangeability and consistency at small sizes; the Ewens law of the block sizes
for two customers; the junk value of the closed form at `θ = 0`, outside the domain. The model
has no `structure`; `crp` is a `PMF`, so its non-vacuity is that it is defined for every
`θ > 0` (the instances below use an arbitrary `θ > 0` and the concrete value `θ = 1`).
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Biology.PopulationGenetics.ChineseRestaurant

open MathlibExt.Biology.PopulationGenetics.ChineseRestaurant
open MathlibExt.Biology.PopulationGenetics.Ewens

/-- With no customers, the empty partition has probability one. -/
example (θ : ℝ) (hθ : 0 < θ) (π : Finpartition (univ : Finset (Fin 0))) :
    crp θ hθ 0 π = 1 := by
  rw [crp_apply, crpProb]
  have hparts : π.parts = ∅ := Finpartition.parts_eq_empty_iff.2 (by simp)
  simp [hparts, Finpartition.cardProd]

/-- Every customer at their own table: probability `θ^n / θ^{(n)}`. -/
theorem crpProb_bot (θ : ℝ) (n : ℕ) :
    crpProb θ (⊥ : Finpartition (univ : Finset (Fin n))) =
      θ ^ n / (ascPochhammer ℝ n).eval θ := by
  simp [crpProb]

/-- All `n ≥ 1` customers at one table: probability `(n - 1)! θ / θ^{(n)}`. -/
theorem crpProb_top (θ : ℝ) {n : ℕ} (hn : 0 < n) :
    crpProb θ (⊤ : Finpartition (univ : Finset (Fin n))) =
      θ * ((n - 1).factorial : ℝ) / (ascPochhammer ℝ n).eval θ := by
  have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩
  have hcard : #(⊤ : Finpartition (univ : Finset (Fin n))).parts = 1 :=
    (Finpartition.eq_top_iff_card_parts_eq_one _ hne).1 rfl
  rw [crpProb, Finpartition.cardProd_top hne, hcard]
  simp

/-- Two customers sit apart with probability `θ / (θ + 1)`. -/
example (θ : ℝ) (hθ : 0 < θ) :
    (crp θ hθ 2 ⊥).toReal = θ / (θ + 1) := by
  rw [crp_toReal, crpProb_bot]
  have : θ * (θ + 1) ≠ 0 := by positivity
  simp [ascPochhammer_succ_eval]
  field_simp

/-- Two customers share a table with probability `1 / (θ + 1)`. -/
example (θ : ℝ) (hθ : 0 < θ) :
    (crp θ hθ 2 ⊤).toReal = 1 / (θ + 1) := by
  rw [crp_toReal, crpProb_top θ (by norm_num)]
  have : θ * (θ + 1) ≠ 0 := by positivity
  simp [ascPochhammer_succ_eval]
  field_simp

/-- At `θ = 1` three customers all sit apart with probability `1 / 6 = 1 / 3!`. -/
example : crpProb 1 (⊥ : Finpartition (univ : Finset (Fin 3))) = 1 / 6 := by
  rw [crpProb_bot]
  simp [ascPochhammer_succ_eval]
  norm_num

/-- The two partitions of two customers are `⊥` and `⊤`, and their probabilities sum to
one. -/
example (θ : ℝ) (hθ : 0 < θ) :
    crpProb θ (⊥ : Finpartition (univ : Finset (Fin 2))) +
      crpProb θ (⊤ : Finpartition (univ : Finset (Fin 2))) = 1 := by
  rw [crpProb_bot, crpProb_top θ (by norm_num)]
  have : θ * (θ + 1) ≠ 0 := by positivity
  simp [ascPochhammer_succ_eval]
  field_simp

/-- Exchangeability: swapping customers `0` and `2` does not change the law. -/
example (θ : ℝ) (hθ : 0 < θ) (π : Finpartition (univ : Finset (Fin 3))) :
    crp θ hθ 3 (π.comap (Equiv.swap 0 2)) = crp θ hθ 3 π :=
  crp_comap_perm hθ _ π

/-- Consistency: restricting four customers to the first two gives the two-customer law. -/
example (θ : ℝ) (hθ : 0 < θ) :
    (crp θ hθ 4).map (Finpartition.comap (Fin.castLE (by norm_num : 2 ≤ 4))) = crp θ hθ 2 :=
  crp_map_restrict_castLE hθ _

/-- Every seating of customer `1` restricts back to the partition of customer `0`, and different
seatings give different partitions. -/
example (π : Finpartition (univ : Finset (Fin 1))) (c : Option π.parts) :
    (seat π c).comap Fin.castSucc = π ∧ ∀ c', seat π c' = seat π c → c' = c :=
  ⟨comap_castSucc_seat π c, fun _ h ↦ seat_injective π h⟩

/-- The block sizes of two customers: one allele carried by both genes with probability
`1 / (θ + 1)` (the Ewens sampling formula). -/
example (θ : ℝ) (hθ : 0 < θ) :
    (crp θ hθ 2).map blockSizes (Nat.Partition.indiscrete 2) =
      ENNReal.ofReal (1 / (θ + 1)) := by
  rw [crp_map_blockSizes hθ]
  congr 1
  have : θ * (θ + 1) ≠ 0 := by positivity
  simp [ewensProb, ascPochhammer_succ_eval]
  field_simp

/-- The expected number of tables for two customers is `1 + θ / (θ + 1)`. -/
example (θ : ℝ) (hθ : 0 < θ) :
    ∑ π : Finpartition (univ : Finset (Fin 2)), (crp θ hθ 2 π).toReal * #π.parts =
      1 + θ / (θ + 1) := by
  rw [sum_crp_toReal_mul_card_parts hθ]
  have : θ ≠ 0 := hθ.ne'
  simp [sum_range_succ, div_self this]

/-- Outside the domain `θ > 0`: at `θ = 0` the rising factorial vanishes for `n ≥ 1`, and the
closed form returns Lean's junk value `0` (division by zero), so it is not a probability
distribution. (`crp` itself requires a proof of `0 < θ`.) -/
example : crpProb 0 (⊥ : Finpartition (univ : Finset (Fin 1))) = 0 := by
  simp [crpProb]

end MathlibExtTest.Biology.PopulationGenetics.ChineseRestaurant
