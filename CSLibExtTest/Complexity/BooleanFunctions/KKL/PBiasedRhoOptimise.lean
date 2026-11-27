/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.PBiasedRhoOptimise
public import CSLibExt.Complexity.BooleanFunctions.KKL.SummedBKKKLWitness
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.FSPerEdge

/-!
# Tests for rho-optimisation from the `p`-biased master estimate

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.PBiasedRhoOptimise`:

* `pro_degreeWeight_eq` at the `AND` function on `{0, 1}^Bool` under `μ_p`: the degree-weighted
  Fourier mass is `4 σ_p² · 2p = 8p²(1-p)`;
* `pro_master_lhs_zero_of_totalInfl_zero` and `pro_master_holds_of_totalInfl_zero` at the constant
  function `false`, whose total influence is `0`;
* the window predicate `pro_PBiasedMaster q` holds for `q ≤ 1/2` (empty window) and fails for
  every `q > 9/10` (`sbk_pBiasedMaster_false`, from the two-bit `OR` function at `p = 9/10`); for
  `q ∈ (1/2, 9/10]` it is neither proved nor refuted here, so `pro_rhoOptimise_of_master` is
  instantiated only at the degenerate `q = 1/2`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- `pro_degreeWeight_eq` at `AND`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∑ S : Finset Bool, 4 * (S.card : ℝ) * (ptn_coeff p andInd S) ^ 2) = 8 * p ^ 2 * (1 - p) := by
  rw [pro_degreeWeight_eq hp0 hp1 andFun, ptn_sigma_sq hp0 hp1, totalInfl_andInd_p]
  ring

/-- The constant function `false` has total influence `0` under every product weight. -/
lemma prot_totalInfl_const_false (p : ℝ) :
    totalInfl (bernoulliWeight p)
      (fun ω => if (fun _ => false : ConfigSpace Bool → Bool) ω then (1 : ℝ) else 0) = 0 := by
  simp [totalInfl, infl, expect]

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (u : ℝ) :
    (∑ S : Finset Bool, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace Bool → Bool) ω
            then (1 : ℝ) else 0) S) ^ 2) = 0 :=
  pro_master_lhs_zero_of_totalInfl_zero hp0 hp1 _ (prot_totalInfl_const_false p) u

example (u : ℝ) :
    (∑ S : Finset Bool, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (3 / 4) (fun ω => if (fun _ => false : ConfigSpace Bool → Bool) ω
            then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (bernoulliWeight (3 / 4))
            (fun ω => if (fun _ => false : ConfigSpace Bool → Bool) ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * (4 * (ptn_sigma (3 / 4)) ^ 2 * totalInfl (bernoulliWeight (3 / 4))
            (fun ω => if (fun _ => false : ConfigSpace Bool → Bool) ω then (1 : ℝ) else 0)) :=
  pro_master_holds_of_totalInfl_zero (by norm_num) (by norm_num) _
    (prot_totalInfl_const_false _) u

/-- `pro_PBiasedMaster q` for `q ≤ 1/2` holds vacuously. -/
lemma prot_pBiasedMaster_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : pro_PBiasedMaster q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : ¬ pro_PBiasedMaster 1 := sbk_pBiasedMaster_false (by norm_num)

example : ptn_RhoOptimise (1 / 2) :=
  pro_rhoOptimise_of_master (prot_pBiasedMaster_of_le_half le_rfl)

end StatMechTest.BooleanFunctions
