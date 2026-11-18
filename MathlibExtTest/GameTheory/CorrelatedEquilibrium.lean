/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.CorrelatedEquilibrium

open MathlibExt.GameTheory.CorrelatedEquilibrium
open MathlibExt.GameTheory.NoRegretDynamics

/-- Chicken has a correlated equilibrium that is not a product distribution. -/
example : IsCorrelatedEq chickenCost chickenCE 0 := chickenCE_isCorrelatedEq

/-- It is also a coarse correlated equilibrium (a point of the Hannan set). -/
example : IsCoarseCorrelatedEq chickenCost chickenCE 0 :=
  chickenCE_isCorrelatedEq.isCoarseCorrelatedEq fun _ => by simp

/-- The point mass at (stay, leave) is a pure Nash equilibrium of Chicken, hence a correlated
equilibrium. -/
example : IsCorrelatedEq chickenCost (fun s => if s = ![1, 0] then 1 else 0) 0 := by
  refine isCorrelatedEq_dirac fun i a => ?_
  fin_cases i <;> fin_cases a <;> norm_num [chickenCost, Function.update]

/-- One-action games are degenerate: every distribution is a correlated equilibrium. -/
example (cost : Fin 2 → (Fin 2 → Fin 1) → ℝ) (ψ : (Fin 2 → Fin 1) → ℝ)
    (hψ : IsDistribution ψ) : IsCorrelatedEq cost ψ 0 := by
  refine ⟨hψ, fun i j k => ?_⟩
  have h : ∀ s : Fin 2 → Fin 1, Function.update s i k = s := fun s =>
    funext fun _ => Subsingleton.elim _ _
  simp [switchGain, h]

/-- Playing (leave, leave), (leave, stay), (stay, leave) once each has no conditional regret
above `0`, so its empirical distribution is a correlated equilibrium. -/
example : IsCorrelatedEq chickenCost (empirical ![![0, 0], ![0, 1], ![1, 0]]) 0 := by
  rw [isCorrelatedEq_empirical_iff (by norm_num)]
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [condRegret, switchGain, chickenCost, Fin.sum_univ_three, Function.update] <;>
    norm_num

/-- Two strategies with regrets `a = 2` (from `0` to `1`) and `b = 1` (from `1` to `0`): the
regret-invariant vector is `(b, a) / (a + b) = (1/3, 2/3)`. -/
example : IsRegretInvariant (A := Fin 2) ![![0, 2], ![1, 0]] ![1 / 3, 2 / 3] := by
  intro j
  fin_cases j <;> simp [Fin.sum_univ_two] <;> norm_num

/-- For it, the Blackwell expression (3.3) vanishes for every payoff vector. -/
example (g : Fin 2 → ℝ) :
    ∑ j, ∑ k, (![![0, 2], ![1, 0]] : Fin 2 → Fin 2 → ℝ) j k * ![1 / 3, 2 / 3] j * (g k - g j)
      = 0 :=
  sum_mul_sub_eq_zero_of_isRegretInvariant (by
    intro j; fin_cases j <;> simp [Fin.sum_univ_two] <;> norm_num) g

/-- The set of correlated equilibria of Chicken is compact and convex. -/
example : IsCompact {ψ | IsCorrelatedEq chickenCost ψ 0} ∧
    Convex ℝ {ψ | IsCorrelatedEq chickenCost ψ 0} :=
  ⟨isCompact_setOf_isCorrelatedEq _ _, convex_setOf_isCorrelatedEq _ _⟩

#print axioms IsCorrelatedEq.isCoarseCorrelatedEq
#print axioms isCompact_setOf_isCorrelatedEq
#print axioms isCorrelatedEq_empirical_iff
#print axioms chickenCE_isCorrelatedEq

private theorem sum_fin_two_pi' (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ s, f s = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, piFinTwoEquiv_symm_apply]
  rw [← add_assoc]
  rfl

private theorem erase_fin_two (i : Fin 2) : (Finset.univ.erase i : Finset (Fin 2)) = {1 - i} := by
  fin_cases i <;> decide

/-- The mixed Nash equilibrium of Chicken, where each player leaves with probability `3/4`,
gives a correlated equilibrium as a product distribution. -/
example : IsCorrelatedEq chickenCost (productDist fun _ => ![3 / 4, 1 / 4]) 0 := by
  refine isCorrelatedEq_productDist (fun i a => by fin_cases a <;> norm_num)
    (fun i => by simp [Fin.sum_univ_two]; norm_num) fun i a => ?_
  simp only [pureCost, othersWeight, erase_fin_two, productDist, Fin.prod_univ_two,
    sum_fin_two_pi']
  fin_cases i <;> fin_cases a <;> simp [chickenCost] <;> norm_num

/-- Conversely, from the correlated equilibrium property of the product, no player of Chicken
gains by a pure deviation from `(3/4, 1/4)`. -/
example (h : IsCorrelatedEq chickenCost (productDist fun _ => ![3 / 4, 1 / 4]) 0) (i : Fin 2)
    (a : Fin 2) :
    ∑ s, productDist (fun _ => ![3 / 4, 1 / 4]) s * chickenCost i s ≤
      pureCost chickenCost (fun _ => ![(3 : ℝ) / 4, 1 / 4]) i a :=
  (isCorrelatedEq_productDist_iff (fun i a => by fin_cases a <;> norm_num)
    (fun i => by simp [Fin.sum_univ_two]; norm_num)).1 h i a
