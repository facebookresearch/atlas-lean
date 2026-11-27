/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.RevealmentBoxCrossing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.RevealmentBoxCrossing`

For the FK mass on the complete graph `K₂` at `p = 1/2`, `q = 2`, and the indicator of the
increasing event "edge `s(0, 1)` is open":

* `revealAdapt_eq_reachProb`: revealment equals reach probability;
* `reachProb_nonneg` and `reachProb_le_one`;
* `os_cov_lower_bound_from_reachBound` with the reach bound `D = 1` discharged by
  `reachProb_le_one`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.RevealmentBoxCrossing

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.RevealmentBoxCrossing
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.MonotonicFK

/-- The event that the edge `s(0, 1)` of `K₂` is open. -/
def edgeOpen : Set (ConfigSpace (Sym2 (Fin 2))) := {ω | ω s(0, 1) = true}

/-- The indicator of `edgeOpen`. -/
noncomputable def ind : ConfigSpace (Sym2 (Fin 2)) → ℝ := edgeOpen.indicator (fun _ => 1)

/-- The indicator of `edgeOpen` is monotone. -/
theorem ind_monotone : Monotone ind := by
  refine IsIncreasing.indicator_monotone (fun x y hxy hx => ?_)
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  have hle := hxy s(0, 1)
  rw [hx] at hle
  exact le_antisymm (by simp) hle

/-- The indicator of `edgeOpen` is nonnegative. -/
theorem ind_nonneg : 0 ≤ ind := Set.indicator_nonneg (fun _ _ => zero_le_one)

/-- The indicator of `edgeOpen` is at most `1`. -/
theorem ind_le_one (ω : ConfigSpace (Sym2 (Fin 2))) : ind ω ≤ 1 := by
  by_cases h : ω ∈ edgeOpen <;> simp [ind, h]

/-- The indicator of `edgeOpen` is idempotent. -/
theorem ind_idem (ω : ConfigSpace (Sym2 (Fin 2))) : ind ω * ind ω = ind ω := by
  by_cases h : ω ∈ edgeOpen <;> simp [ind, h]

-- Revealment equals reach probability.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (e : Sym2 (Fin 2)) :
    revealAdapt (fkMass ⊤ (1 / 2) 2) σ ind e = reachProb (fkMass ⊤ (1 / 2) 2) σ ind e :=
  revealAdapt_eq_reachProb (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) σ ind e

-- The reach probability lies in `[0, 1]`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (e : Sym2 (Fin 2)) :
    0 ≤ reachProb (fkMass ⊤ (1 / 2) 2) σ ind e ∧ reachProb (fkMass ⊤ (1 / 2) 2) σ ind e ≤ 1 :=
  ⟨reachProb_nonneg (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num)) σ ind e,
    reachProb_le_one (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
      (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) σ ind e⟩

-- The covariance lower bound from the trivial reach bound `1`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    Lindeberg.mean (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ind
        * (1 - Lindeberg.mean (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ind) / 1
      ≤ ∑ e, Lindeberg.cov (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ind (Lindeberg.coord e) :=
  os_cov_lower_bound_from_reachBound (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num))
    (FK.fkProb_FKGLatticeCondition ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic ⊤ (by norm_num) (by norm_num) (by norm_num)) σ ind_monotone ind_nonneg
    ind_le_one ind_idem 1 one_pos
    (fun e => reachProb_le_one (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
      (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) σ ind e)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.RevealmentBoxCrossing
