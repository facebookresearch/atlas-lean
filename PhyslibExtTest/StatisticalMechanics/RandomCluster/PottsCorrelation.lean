/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PottsCorrelation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.EdwardsSokalFull`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)` at `β = J = 1` (so `p = 1 - e^{-1} ∈ (0, 1)`):
* the headline `edwards_sokal_correlation` is applied with every hypothesis discharged, for the
  Ising case `q = 2` and the Potts case `q = 3`, and its primed form `edwards_sokal_correlation'`;
* the conclusion is used: the open configuration connects `0` and `1` with positive
  random-cluster probability, so the Potts spins at `0` and `1` agree with probability strictly
  larger than `1/q`;
* the diagonal case `x = y`: `pottsAgreeProb G q β J x x = 1` and `connProb G p q x x = 1`, and the
  identity reads `1 - 1/q = (1 - 1/q) · 1`;
* `pottsAgreeProb_ge` at `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.EdwardsSokalFull

open _root_.StatMech _root_.StatMech.FK

/-- At `β = J = 1` the bond parameter `1 - e^{-1}` is positive. -/
theorem p_pos : 0 < 1 - Real.exp (-(1 * 1 : ℝ)) := by
  have h := Real.exp_lt_exp.mpr (show -(1 * 1 : ℝ) < 0 by norm_num)
  rw [Real.exp_zero] at h
  linarith

/-- At `β = J = 1` the bond parameter `1 - e^{-1}` is below `1`. -/
theorem p_lt_one : 1 - Real.exp (-(1 * 1 : ℝ)) < 1 := by
  have := Real.exp_pos (-(1 * 1 : ℝ))
  linarith

/-- The configuration with every coordinate open. -/
def allOpen : ConfigSpace (Sym2 (Fin 2)) := fun _ => true

/-- With every edge open, `0` and `1` are connected in `⊤ : SimpleGraph (Fin 2)`. -/
theorem connected_allOpen : Connected (⊤ : SimpleGraph (Fin 2)) allOpen 0 1 :=
  SimpleGraph.Adj.reachable (by simp [allOpen])

/-- The random-cluster connection probability of `0` and `1` is positive. -/
theorem connProb_pos (q : ℝ) (hq : 0 < q) :
    0 < connProb (⊤ : SimpleGraph (Fin 2)) (1 - Real.exp (-(1 * 1 : ℝ))) q 0 1 := by
  unfold connProb
  refine lt_of_lt_of_le (fkProb_pos (⊤ : SimpleGraph (Fin 2)) p_pos p_lt_one hq allOpen) ?_
  exact Finset.single_le_sum
    (fun ω _ => fkProb_nonneg (⊤ : SimpleGraph (Fin 2)) p_pos p_lt_one hq ω)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, connected_allOpen⟩)

-- The headline at `q = 2` (Ising): `μ(σ₀ = σ₁) - 1/2 = (1/2) φ_{p,2}(0 ↔ 1)`.
example : pottsAgreeProb (⊤ : SimpleGraph (Fin 2)) 2 1 1 0 1 - 1 / 2
    = (1 - 1 / 2) * connProb (⊤ : SimpleGraph (Fin 2)) (1 - Real.exp (-(1 * 1))) 2 0 1 := by
  simpa using edwards_sokal_correlation (⊤ : SimpleGraph (Fin 2)) 2 1 1 0 1 p_pos p_lt_one
    (by norm_num)

-- The headline at `q = 3` (Potts), primed form with prefactor `(q - 1)/q = 2/3`.
example : pottsAgreeProb (⊤ : SimpleGraph (Fin 2)) 3 1 1 0 1 - 1 / 3
    = 2 / 3 * connProb (⊤ : SimpleGraph (Fin 2)) (1 - Real.exp (-(1 * 1))) 3 0 1 := by
  have h := edwards_sokal_correlation' (⊤ : SimpleGraph (Fin 2)) 3 1 1 0 1 p_pos p_lt_one
    (by norm_num)
  norm_num at h ⊢
  exact h

-- Consequence of the headline: the two Potts spins agree with probability strictly above `1/3`.
example : 1 / 3 < pottsAgreeProb (⊤ : SimpleGraph (Fin 2)) 3 1 1 0 1 := by
  have h := edwards_sokal_correlation (⊤ : SimpleGraph (Fin 2)) 3 1 1 0 1 p_pos p_lt_one
    (by norm_num)
  have hc := connProb_pos 3 (by norm_num)
  norm_num at h hc ⊢
  linarith

/-- On the diagonal every spin configuration agrees with itself: `μ(σ_x = σ_x) = 1`. -/
theorem pottsAgreeProb_self (q : ℕ) [NeZero q] (β J : ℝ) (x : Fin 2) :
    pottsAgreeProb (⊤ : SimpleGraph (Fin 2)) q β J x x = 1 := by
  simpa [pottsAgreeProb] using Potts.pottsProb_sum_eq_one (⊤ : SimpleGraph (Fin 2)) q β J

/-- On the diagonal every configuration connects `x` to itself: `φ(x ↔ x) = 1`. -/
theorem connProb_self (q : ℝ) (hq : 0 < q) (x : Fin 2) :
    connProb (⊤ : SimpleGraph (Fin 2)) (1 - Real.exp (-(1 * 1 : ℝ))) q x x = 1 := by
  have h : ∀ ω, Connected (⊤ : SimpleGraph (Fin 2)) ω x x := fun _ => SimpleGraph.Reachable.refl x
  simpa [connProb, h] using fkProb_sum_eq_one (⊤ : SimpleGraph (Fin 2)) p_pos p_lt_one hq

-- The diagonal case of the headline is consistent: both sides equal `1 - 1/q`.
example : pottsAgreeProb (⊤ : SimpleGraph (Fin 2)) 3 1 1 0 0 - 1 / 3
    = (1 - 1 / 3) * connProb (⊤ : SimpleGraph (Fin 2)) (1 - Real.exp (-(1 * 1))) 3 0 0 := by
  rw [pottsAgreeProb_self, connProb_self 3 (by norm_num)]
  norm_num

-- `pottsAgreeProb_ge` for the Ising case `q = 2`.
example : 1 / 2 ≤ pottsAgreeProb (⊤ : SimpleGraph (Fin 2)) 2 1 1 0 1 := by
  simpa using pottsAgreeProb_ge (⊤ : SimpleGraph (Fin 2)) 2 1 1 0 1 p_pos p_lt_one le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.EdwardsSokalFull
