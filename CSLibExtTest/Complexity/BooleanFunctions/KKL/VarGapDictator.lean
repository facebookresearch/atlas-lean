/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapDictator

/-!
# Tests for the dictator computations

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.VarGapDictator`:

* `vgp_val_eq` at `p = 1/2`; `vgp_dictator_coeff` at `S = ∅`, `{0}` and a two-element set;
  `vgp_dictator_var`, `vgp_dictator_totalInfl`, `vgp_dictator_maxInfl` and
  `vgp_dictator_meanVar` at `p = 1/3`; `vgp_maxInfl_eq_totalInfl_fin1` on the constant-true
  function;
* `vgp_poincare_tight_on_dictator` and `vgp_master_holds_on_dictator` at `p = 1/2`;
* the refutations `vgp_varPowerCore_refutable` and `vgp_varGapCore_refutable` at `q = 3/5`;
* `vgp_integral_collapse_logGain` with its master hypothesis proved for one term of degree
  `1`, weight `1` and `δ = 1`.

Not tested beyond the degenerate case: `vgp_rhoOptimise_of_openResidue` assumes
`frh_openResidue q`, which the library neither proves nor refutes for any `q > 1/2`; the test
runs it on the empty window `q = 1/2`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.VarGapDictator

open Finset StatMech StatMech.OSSS StatMech.Probability

example : ptn_val true = 1 / 2 + ptn_sigma (1 / 2) * ptn_psi (1 / 2) true :=
  vgp_val_eq (by norm_num) (by norm_num) true

example : ptn_coeff (1 / 3)
    (fun ω : ConfigSpace (Fin 2) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) ∅ = 1 / 3 := by
  rw [vgp_dictator_coeff (by norm_num) (by norm_num)]; simp

example : ptn_coeff (1 / 3)
    (fun ω : ConfigSpace (Fin 2) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) {0}
      = ptn_sigma (1 / 3) := by
  rw [vgp_dictator_coeff (by norm_num) (by norm_num)]; simp

example : ptn_coeff (1 / 3)
    (fun ω : ConfigSpace (Fin 2) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) {0, 1} = 0 := by
  rw [vgp_dictator_coeff (by norm_num) (by norm_num),
    ite_eq_right (by decide : ({0, 1} : Finset (Fin 2)) ≠ ∅),
    ite_eq_right (by decide : ({0, 1} : Finset (Fin 2)) ≠ {0})]

example : OSSS.var (OSSS.bernoulliWeight (1 / 3))
    (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) = 2 / 9 := by
  rw [vgp_dictator_var (by norm_num) (by norm_num)]; norm_num

example : totalInfl (OSSS.bernoulliWeight (1 / 3))
    (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) = 1 :=
  vgp_dictator_totalInfl (by norm_num) (by norm_num)

example : maxInfl (OSSS.bernoulliWeight (1 / 3))
    (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) = 1 :=
  vgp_dictator_maxInfl (by norm_num) (by norm_num)

example : OSSS.expect (OSSS.bernoulliWeight (1 / 3))
      (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
    * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 3))
      (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)) = 2 / 9 := by
  rw [vgp_dictator_meanVar (by norm_num) (by norm_num)]; norm_num

example (p : ℝ) : maxInfl (OSSS.bernoulliWeight p)
    (fun ω => if (fun _ => true : ConfigSpace (Fin 1) → Bool) ω then (1 : ℝ) else 0) = 0 := by
  rw [vgp_maxInfl_eq_totalInfl_fin1, mil_constTrue_totalInfl]

/-- `vgp_poincare_tight_on_dictator` at `p = 1/2`: both sides equal `1/4`. -/
example : OSSS.expect (OSSS.bernoulliWeight (1 / 2))
      (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
    * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2))
      (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)) = 1 / 4 := by
  rw [vgp_poincare_tight_on_dictator (by norm_num) (by norm_num),
    vgp_dictator_totalInfl (by norm_num) (by norm_num),
    ptn_sigma_sq (by norm_num) (by norm_num)]
  norm_num

example : (∑ S : Finset (Fin 1), 4 * (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
      * (ptn_coeff (1 / 2)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) S) ^ 2)
    ≤ 1 := by
  have h := vgp_master_holds_on_dictator (p := 1 / 2) (u := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rwa [vgp_dictator_maxInfl (by norm_num) (by norm_num), Real.one_rpow,
    vgp_dictator_totalInfl (by norm_num) (by norm_num), one_mul] at h

example : ¬ vgc_VarPowerCore (3 / 5) := vgp_varPowerCore_refutable (by norm_num)
example : ¬ bkt2p_VarGapCore (3 / 5) := vgp_varGapCore_refutable (by norm_num)

/-- `vgp_integral_collapse_logGain` for one term of degree `1`, weight `1`, and `δ = 1`:
the master hypothesis is `4 ≤ 1 ^ (u / (2 - u)) · 4`. -/
example : 2 * (∑ i ∈ univ.filter (fun i : Fin 1 => (fun _ => 1 : Fin 1 → ℕ) i ≠ 0),
      (fun _ => 1 : Fin 1 → ℝ) i) * Real.log (1 / 1)
    ≤ ∑ i : Fin 1, 4 * (((fun _ => 1 : Fin 1 → ℕ) i : ℕ) : ℝ) * (fun _ => 1 : Fin 1 → ℝ) i :=
  vgp_integral_collapse_logGain (fun _ => zero_le_one) zero_le_one
    (fun u _ _ => by simp)

/-- `frh_openResidue q` holds vacuously for `q ≤ 1/2`. -/
lemma openResidue_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : frh_openResidue q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : ptn_RhoOptimise (1 / 2) := vgp_rhoOptimise_of_openResidue (openResidue_of_le_half le_rfl)

end StatMechTest.BooleanFunctions.VarGapDictator
