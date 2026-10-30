/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLMeanInfl
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.BKKKLLevel2

/-!
# Tests for mean, influence and Poincaré

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLMeanInfl`:

* `mil_poincare` on the one-variable dictator at every `p ∈ (0, 1)`: the conclusion is
  `p(1-p) ≤ p(1-p)`, so Poincaré is tight there; `mil_var_eq`, `mil_mean_nonneg`,
  `mil_mean_le_one`, `mil_level1_le_var` and `mil_levelGe2_le_var` on the same function;
* `mil_fourierMass_le_degreeWeight` on a general two-variable function;
* the constant-true computations `mil_constTrue_totalInfl`, `mil_constTrue_coeff`,
  `mil_constTrue_qnorm`;
* `bkt2f_meanInflResidue_refutable` at `q = 3/5`.

Window predicate: the library refutes `mil_VarScalarCore q` for `q > 3/4`
(`ctc_varScalarCore_false`, tested at `q = 1`) and for every `q > 1/2`
(`ctc_varScalarCore_false_of_half_lt`, tested at `q = 3/5`): at the one-variable dictator it asks
for `4(k+1)σ_p² ≤ 4σ_p²(1 - (1-u)^k)`.
The chain `mil_levelGe2_of_var`, `mil_master_of_varScalar`, `mil_rhoOptimise_of_varScalar`
is run on the empty window `q = 1/2` only.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.BKKKLMeanInfl

open Finset StatMech StatMech.OSSS StatMech.Probability

/-- `mil_poincare` on the dictator: `p(1-p) ≤ p(1-p) · 1`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : p * (1 - p) ≤ p * (1 - p) * 1 := by
  have h := mil_poincare hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
  rwa [vgp_dictator_meanVar hp0 hp1, vgp_dictator_totalInfl hp0 hp1, ptn_sigma_sq hp0 hp1] at h

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
      - (OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)) ^ 2
      = p * (1 - p) := by
  rw [← mil_var_eq, vgp_dictator_var hp0 hp1]

example {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) ∧
      OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) ≤ 1 :=
  ⟨mil_mean_nonneg hp0 hp1 _, mil_mean_le_one hp0 hp1 _⟩

/-- `mil_level1_le_var` on the dictator: the whole variance sits at level one. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : p * (1 - p) ≤ p * (1 - p) := by
  have h := mil_level1_le_var hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
  rw [vgp_dictator_level1 hp0 hp1, vgp_dictator_meanVar hp0 hp1] at h

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => 2 ≤ S.card ∧ S.card ≤ 3),
        (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0)
            S) ^ 2
      ≤ 4 * 3 * (p * (1 - p)) := by
  have h := mil_levelGe2_le_var hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
    (u := 1 / 2) (by norm_num) (by norm_num) 3
  rw [vgp_dictator_meanVar hp0 hp1] at h
  exact_mod_cast h

example {p : ℝ} (φ : ConfigSpace (Fin 2) → Bool) :
    ∑ S ∈ (univ.erase (∅ : Finset (Fin 2))),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ ∑ S : Finset (Fin 2), (S.card : ℝ)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 :=
  mil_fourierMass_le_degreeWeight φ

example (p : ℝ) : totalInfl (OSSS.bernoulliWeight p)
    (fun ω => if (fun _ => true : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0) = 0 :=
  mil_constTrue_totalInfl

example : ptn_coeff (1 / 2)
    (fun ω => if (fun _ => true : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0) {0} = 0 := by
  rw [mil_constTrue_coeff (by norm_num) (by norm_num)]
  simp

example : ptn_coeff (1 / 2)
    (fun ω => if (fun _ => true : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0) ∅ = 1 := by
  rw [mil_constTrue_coeff (by norm_num) (by norm_num)]
  simp

example : (ptn_qnorm (1 / 3) 2
    (fun ω => if (fun _ => true : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0)) ^ 2 = 1 :=
  mil_constTrue_qnorm (by norm_num) (by norm_num) (by norm_num)

example : ¬ bkt2f_meanInflResidue (3 / 5) := bkt2f_meanInflResidue_refutable (by norm_num)

example : ¬ mil_VarScalarCore 1 := ctc_varScalarCore_false (by norm_num)
example : ¬ mil_VarScalarCore (3 / 5) := ctc_varScalarCore_false_of_half_lt (by norm_num)

/-- `mil_VarScalarCore q` holds vacuously for `q ≤ 1/2`. -/
lemma varScalarCore_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : mil_VarScalarCore q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : bkt2_levelGe2MasterResidue (1 / 2) :=
  mil_levelGe2_of_var (varScalarCore_of_le_half le_rfl)
example : pro_PBiasedMaster (1 / 2) := mil_master_of_varScalar (varScalarCore_of_le_half le_rfl)
example : ptn_RhoOptimise (1 / 2) := mil_rhoOptimise_of_varScalar (varScalarCore_of_le_half le_rfl)

end StatMechTest.BooleanFunctions.BKKKLMeanInfl
