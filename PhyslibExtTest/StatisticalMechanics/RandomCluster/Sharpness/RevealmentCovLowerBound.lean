/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.RevealmentCovLowerBound

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.RevealmentCovLowerBound`

* `revealAdapt_eq_one_witness`: the explicit revealment-`1` example, restated;
* `revealAdapt_single_no_over_n`: on the same example, the first-edge revealment is not `≤ 1/2`;
* `var_le_avg_reveal_mul_sum_cov` for the FK mass on `K₂` at `p = 1/2`, `q = 2`, a one-order
  family and the indicator of "edge `s(0, 1)` is open", with `D = 1` (`avg_reveal_le_one`);
* `fk_q2_cov_lower_bound_from_perScaleReveal` with `R = 1`, `D = 1` discharged.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.RevealmentCovLowerBound

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.FKRevealmentClose
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

-- The explicit example of revealment `1` on the first edge.
example :
    revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ))
      (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) = 1 :=
  revealAdapt_eq_one_witness

-- So no bound `c < 1` holds there.
example :
    ¬ revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ))
      (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) ≤ 1 / 2 := by
  rw [revealAdapt_eq_one_witness]
  norm_num

-- The averaged OSSS inequality for a one-order family, with `D = 1`.
example {m : ℕ} (σ : Fin m ≃ Sym2 (Fin 2)) :
    Lindeberg.var (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ind
      ≤ 1 * ∑ e, Lindeberg.cov (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ind
          (Lindeberg.coord e) :=
  var_le_avg_reveal_mul_sum_cov (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num))
    (FK.fkProb_FKGLatticeCondition ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic ⊤ (by norm_num) (by norm_num) (by norm_num)) (fun _ : Unit => σ)
    ind_monotone ind_nonneg ind_le_one 1 (fun e => avg_reveal_le_one _ ind e)

-- The `q = 2` per-scale bound with `R = 1` and `D = 1`.
example {m : ℕ} (σ : Fin m ≃ Sym2 (Fin 2)) :
    Lindeberg.mean (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ind
        * (1 - Lindeberg.mean (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ind) / 1
      ≤ ∑ e, Lindeberg.cov (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ind (Lindeberg.coord e) :=
  fk_q2_cov_lower_bound_from_perScaleReveal ⊤ (by norm_num) (by norm_num) (fun _ : Unit => σ)
    ind_monotone ind_nonneg ind_le_one ind_idem (fun _ _ => 1) 1 one_pos
    (fun _ e => RevealmentBoundAssembly.revealAdapt_le_one _ σ ind e) (fun _ => by simp)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.RevealmentCovLowerBound
