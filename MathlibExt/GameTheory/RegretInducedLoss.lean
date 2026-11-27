/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Basic
public import MathlibExt.GameTheory.CorrelatedEquilibrium
public import MathlibExt.GameTheory.Regret
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Induced losses for regret in games

The game layer (C3) of the canonical regret vocabulary: a player's loss
vector induced by the opponents' independent mixed play in a finite
normal-form cost game, stated directly for
`CorrelatedEquilibrium.pureCost`. This adapter sits above both the
game-free regret base (`MathlibExt/GameTheory/Regret.lean`) and
`MathlibExt.GameTheory.CorrelatedEquilibrium`; keeping it here leaves the
base regret layer below the equilibrium modules.

## Main results

* `pureCost_eq_sum_filter`: the pure cost as a filtered profile sum.
* `pureCost_nonneg`
* `pureCost_le_one`

## References

* T. Roughgarden, CS364A lecture notes (no-regret definitions).
* Y. Freund and R. Schapire (1999) (the [0,1] loss normalization).
-/

@[expose] public section

namespace MathlibExt.GameTheory.Regret

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The pure cost as the cost weighted by the opponents' mixed play,
summed over profiles where player `i` plays `a`. (C3 game layer) -/
theorem pureCost_eq_sum_filter (cost : ι → (∀ i, S i) → ℝ)
    (σ : ∀ i, S i → ℝ) (i : ι) (a : S i) :
    MathlibExt.GameTheory.CorrelatedEquilibrium.pureCost cost σ i a
      = ∑ s ∈ Finset.univ.filter (fun s : ∀ j, S j => s i = a),
        cost i s * ∏ j ∈ Finset.univ.erase i, σ j (s j) := by
  unfold MathlibExt.GameTheory.CorrelatedEquilibrium.pureCost
    MathlibExt.GameTheory.CorrelatedEquilibrium.othersWeight
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s i = a
  · simp [h, mul_comm]
  · simp [h]

/-- Pure costs are nonnegative for nonnegative costs. (C3 game layer) -/
theorem pureCost_nonneg {cost : ι → (∀ i, S i) → ℝ} {σ : ∀ i, S i → ℝ}
    {i : ι} {a : S i} (hσ : ∀ j, j ≠ i → IsSimplex (σ j))
    (hcost : ∀ s, 0 ≤ cost i s) :
    0 ≤ MathlibExt.GameTheory.CorrelatedEquilibrium.pureCost cost σ i a := by
  rw [pureCost_eq_sum_filter]
  refine Finset.sum_nonneg fun s _ => ?_
  refine mul_nonneg (hcost s) ?_
  refine Finset.prod_nonneg fun j hj => ?_
  obtain ⟨hjn, -⟩ := (isSimplex_iff _).mp (hσ j (Finset.mem_erase.mp hj).1)
  exact hjn _

/-- Pure costs are at most one for [0,1] costs. (C3 game layer) -/
theorem pureCost_le_one {cost : ι → (∀ i, S i) → ℝ} {σ : ∀ i, S i → ℝ}
    {i : ι} {a : S i} (hσ : ∀ j, j ≠ i → IsSimplex (σ j))
    (hcost : ∀ s, cost i s ≤ 1) :
    MathlibExt.GameTheory.CorrelatedEquilibrium.pureCost cost σ i a ≤ 1 := by
  have hW : ∀ s : ∀ j, S j, 0 ≤ ∏ j ∈ Finset.univ.erase i, σ j (s j) := by
    intro s
    refine Finset.prod_nonneg fun j hj => ?_
    obtain ⟨hjn, -⟩ := (isSimplex_iff _).mp (hσ j (Finset.mem_erase.mp hj).1)
    exact hjn _
  have hBridge : Finset.univ.filter (fun s : ∀ j, S j => s i = a)
      = Fintype.piFinset (Function.update (fun _ => Finset.univ) i {a}) := by
    have hmem : a ∈ (fun _ => Finset.univ) i := Finset.mem_univ a
    have h := Fintype.piFinset_update_singleton_eq_filter_piFinset_eq
      (fun _ => Finset.univ) i hmem
    rw [Fintype.piFinset_univ] at h
    exact h.symm
  have hfib : ∀ j : ι, ∑ b ∈ Function.update (fun _ => Finset.univ) i {a} j,
      Function.update (fun j b => σ j b) i (fun _ => 1) j b = 1 := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, Function.update_self, Finset.sum_singleton]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      obtain ⟨-, hjsum⟩ := (isSimplex_iff _).mp (hσ j hj)
      exact hjsum
  have hLHS : ∏ j, ∑ b ∈ Function.update (fun _ => Finset.univ) i {a} j,
      Function.update (fun j b => σ j b) i (fun _ => 1) j b = 1 :=
    Finset.prod_eq_one fun j _ => hfib j
  have hRHS : (∑ x ∈ Fintype.piFinset
        (Function.update (fun _ => Finset.univ) i {a}),
        ∏ j, Function.update (fun j b => σ j b) i (fun _ => 1) j (x j))
      = ∑ x ∈ Fintype.piFinset (Function.update (fun _ => Finset.univ) i {a}),
        ∏ j ∈ Finset.univ.erase i, σ j (x j) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hfi : Function.update (fun j b => σ j b) i (fun _ => 1) i (x i) = 1 := by
      simp only [Function.update_self]
    have hrest : (∏ j ∈ Finset.univ.erase i,
          Function.update (fun j b => σ j b) i (fun _ => 1) j (x j))
        = ∏ j ∈ Finset.univ.erase i, σ j (x j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_erase] at hj
      simp only [Function.update_of_ne hj.1]
    have hsplit : (∏ j, Function.update (fun j b => σ j b) i (fun _ => 1) j (x j))
        = (∏ j ∈ Finset.univ.erase i,
            Function.update (fun j b => σ j b) i (fun _ => 1) j (x j))
          * Function.update (fun j b => σ j b) i (fun _ => 1) i (x i) :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [hsplit, hrest, hfi, mul_one]
  have hkey := Finset.prod_univ_sum
    (Function.update (fun _ => Finset.univ) i {a})
    (Function.update (fun j b => σ j b) i (fun _ => 1))
  have hsum : ∑ x ∈ Fintype.piFinset
      (Function.update (fun _ => Finset.univ) i {a}),
      ∏ j ∈ Finset.univ.erase i, σ j (x j) = 1 := by
    rw [← hRHS, ← hkey]
    exact hLHS
  rw [pureCost_eq_sum_filter]
  rw [hBridge, ← hsum]
  refine Finset.sum_le_sum fun s _ => ?_
  calc cost i s * ∏ j ∈ Finset.univ.erase i, σ j (s j)
      ≤ 1 * ∏ j ∈ Finset.univ.erase i, σ j (s j) :=
        mul_le_mul_of_nonneg_right (hcost s) (hW s)
    _ = ∏ j ∈ Finset.univ.erase i, σ j (s j) := one_mul _

end MathlibExt.GameTheory.Regret
