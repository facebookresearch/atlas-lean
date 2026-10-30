/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CoupledTensorizeRefutations

/-!
# Tests for the refutations of the coupled-tensorization residues

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CoupledTensorizeRefutations`:

* the one-coordinate computations for the dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}`
  (`ctc_expect_fin1`, `ctc_mean`, `ctc_infl`, `ctc_totalInfl`, `ctc_maxInfl`, `ctc_coeff_single`,
  `ctc_L1`, `ctc_ge2_empty`) at `p = 1/2` and `p = 3/4`;
* `ctc_variance_family_all_false` at `q = 1` (it bundles the five individual refutations), and
  `ctc_levelGe2_false` at `q = 4/5`;
* `ctc_lowDegree_k0_holds` at `p = 1/2, u = 1/2`.

The refuted predicates (`vgc_VarPowerCore`, `bkt2p_VarGapCore`, `mil_VarScalarCore`,
`bkt2_levelGe2MasterResidue`, `bkt2_RemainingGoal`) are window statements over `p ∈ (1/2, q)`:
they hold for `q ≤ 1/2` only because the window is empty (recorded below for
`vgc_VarPowerCore`), are false for `q > 3/4`, and are neither proved nor refuted for
`q ∈ (1/2, 3/4]`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.CoupledTensorizeRefutations

open StatMech StatMech.OSSS StatMech.Probability

/-- The dictator indicator `ω ↦ [ω 0]` on `{0, 1}^{Fin 1}`. -/
noncomputable def dictInd (ω : ConfigSpace (Fin 1)) : ℝ := if ω 0 then 1 else 0

example (p : ℝ) : expect (bernoulliWeight p) dictInd = p := by
  rw [ctc_expect_fin1]; simp [dictInd]

example : expect (bernoulliWeight (3 / 4))
    (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) = 3 / 4 :=
  ctc_mean _

example : infl (bernoulliWeight (3 / 4))
      (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) 0 = 1
    ∧ totalInfl (bernoulliWeight (3 / 4))
      (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) = 1
    ∧ maxInfl (bernoulliWeight (3 / 4))
      (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) = 1 :=
  ⟨ctc_infl _, ctc_totalInfl _, ctc_maxInfl _⟩

/-- `ptn_sigma (1/2) = 1/2`. -/
lemma ptn_sigma_half : ptn_sigma (1 / 2) = 1 / 2 := by
  rw [ptn_sigma, show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

example : ptn_coeff (1 / 2)
    (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) {0} = 1 / 2 := by
  rw [ctc_coeff_single _ (by norm_num) (by norm_num), ptn_sigma_half]

example : (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 1) => S.card = 1),
      (ptn_coeff (3 / 4)
        (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) S) ^ 2)
    = 3 / 16 := by
  rw [ctc_L1 _ (by norm_num) (by norm_num), ptn_sigma_sq (by norm_num) (by norm_num)]
  norm_num

example : Finset.univ.filter (fun S : Finset (Fin 1) => 2 ≤ S.card ∧ S.card ≤ 5) = ∅ :=
  ctc_ge2_empty 5

example : ¬ vgc_VarPowerCore 1 ∧ ¬ bkt2p_VarGapCore 1 ∧ ¬ mil_VarScalarCore 1
    ∧ ¬ bkt2_levelGe2MasterResidue 1 ∧ ¬ bkt2_RemainingGoal 1 :=
  ctc_variance_family_all_false (by norm_num)

example : ¬ bkt2_levelGe2MasterResidue (4 / 5) := ctc_levelGe2_false (by norm_num)

/-- `vgc_VarPowerCore q` for `q ≤ 1/2` holds because `(1/2, q)` is empty. -/
lemma vgc_varPowerCore_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : vgc_VarPowerCore q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : vgc_VarPowerCore (1 / 2) := vgc_varPowerCore_of_le_half le_rfl

example :
    4 * ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 1) => 1 ≤ S.card ∧ S.card ≤ 0),
        (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
          * (ptn_coeff (1 / 2)
            (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 * (ptn_sigma (1 / 2)) ^ 2)
        * ((maxInfl (bernoulliWeight (1 / 2))
              (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0))
                ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
          - (1 - 1 / 2) ^ (0 : ℕ))
        * totalInfl (bernoulliWeight (1 / 2))
            (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) :=
  ctc_lowDegree_k0_holds _

end StatMechTest.BooleanFunctions.CoupledTensorizeRefutations
