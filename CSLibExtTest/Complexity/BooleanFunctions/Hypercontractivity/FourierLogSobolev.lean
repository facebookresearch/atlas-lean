/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.FourierLogSobolev
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.EntropySubadditivity

/-!
# Tests for log-Sobolev inequalities by Fourier expansion

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.FourierLogSobolev`:

* `fsc2_perCoord_lsi` at the dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}`;
* `fsc2_dirichlet_fourier` at the dictator: both sides equal `1` for every `p ∈ (0, 1)`;
* `fsc2_globalLSI` at `AND` on `{0, 1}^Bool`: entropy `-p² log p²` and Dirichlet sum `2p`, giving
  `-p² log p² ≤ 2p`; `fsc2_lsi_spectral` at the dictator;
* `fsc2_coeff_noiseOp` at `ρ = 0` (only the empty coefficient survives) and `ρ = 1`;
* the named predicate `fsc2_EntMassFamily` is proved for `AND` and for the five-bit `AND` at
  every `p ∈ (0, 1)` (`fsc2_entMassFamily_holds`, `fsc2_residue_nonvac`);
* the damping estimate (damped mass at the threshold `exp (-1/(2p(1-p)))` at most
  `maxInfl · Var`) at the five-bit `AND` and `p = 11/20 ∈ (1/2, 1)`: all antecedents
  hold (including `fsc2_EntMassFamily`), and so does the conclusion, since the threshold
  is at most `1/7` (computations from the `EntropySubadditivity` test). So the estimate
  is neither vacuous nor false on this function.

Not proved here: the damping estimate uniformly over all Boolean functions and all
`p ∈ (1/2, q)` for any `q > 1/2`. No residue chain derives damping, rho-optimise or
hypercontractivity from it.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.FourierLogSobolev

open StatMech StatMech.OSSS StatMech.Probability
open StatMechTest.BooleanFunctions.EntropySubadditivity (and5 maxInfl_and5 var_and5
  and5_below_threshold dampedMass_and5 threshold_le_seventh)

/-- The dictator indicator `ω ↦ [ω 0]` on `{0, 1}^{Fin 1}`. -/
noncomputable def dictInd (ω : ConfigSpace (Fin 1)) : ℝ := if ω 0 then 1 else 0

/-- The discrete derivative of the dictator indicator is identically `1`. -/
lemma deriv_dictInd (e : Fin 1) (ω : ConfigSpace (Fin 1)) :
    dictInd (setOpen e ω) - dictInd (setClosed e ω) = 1 := by
  fin_cases e; simp [dictInd, setOpen, setClosed]

example (ω : ConfigSpace (Fin 1)) :
    esd_entCoord (1 / 2) (fun ω => (dictInd ω) ^ 2) 0 ω ≤ 1 := by
  have h := fsc2_perCoord_lsi (p := 1 / 2) (by norm_num) (by norm_num) dictInd 0 ω
  rwa [deriv_dictInd, one_pow] at h

/-- A sum over the configurations of `{0, 1}^{Fin 1}`. -/
lemma sum_fin_one (f : ConfigSpace (Fin 1) → ℝ) :
    ∑ ω, f ω = f (fun _ => true) + f (fun _ => false) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  rfl

/-- The Dirichlet sum of the dictator is `1`. -/
lemma dirichlet_dictInd (p : ℝ) :
    ∑ e : Fin 1, expect (bernoulliWeight p)
      (fun ω => (dictInd (setOpen e ω) - dictInd (setClosed e ω)) ^ 2) = 1 := by
  simp [deriv_dictInd, expect, weight, bernoulliWeight, sum_fin_one]

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset (Fin 1), (S.card : ℝ) * (ptn_coeff p dictInd S) ^ 2
      = 1 := by
  rw [← fsc2_dirichlet_fourier hp0 hp1, dirichlet_dictInd]

/-- The entropy of the (squared) dictator is `-p log p`. -/
lemma ent_dictInd (p : ℝ) :
    esd_ent (bernoulliWeight p) (fun ω => (dictInd ω) ^ 2) = -(p * Real.log p) := by
  simp [esd_ent, expect, weight, sum_fin_one, dictInd, bernoulliWeight, esd_Phi]

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : -(p * Real.log p) ≤ 1 := by
  have h := fsc2_lsi_spectral hp0 hp1 dictInd
  rwa [ent_dictInd, ← fsc2_dirichlet_fourier hp0 hp1, dirichlet_dictInd] at h

/-! ## The global log-Sobolev inequality at `AND` -/

/-- A sum over the configurations of `{0, 1}^Bool`. -/
lemma sum_configSpace_bool (g : ConfigSpace Bool → ℝ) :
    ∑ ω, g ω = ∑ a : Bool, ∑ b : Bool, g (fun x => cond x b a) := by
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => congrArg g ?_
  funext x; cases x <;> simp [Equiv.boolArrowEquivProd]

/-- The indicator of `AND` on `{0, 1}^Bool`. -/
noncomputable def andInd (ω : ConfigSpace Bool) : ℝ := if ω true && ω false then 1 else 0

/-- The entropy of the (squared) `AND` indicator is `-p² log p²`. -/
lemma ent_andInd (p : ℝ) :
    esd_ent (bernoulliWeight p) (fun ω => (andInd ω) ^ 2) = -(p ^ 2 * Real.log (p ^ 2)) := by
  simp [esd_ent, expect, weight, sum_configSpace_bool, andInd, bernoulliWeight, esd_Phi]
  rw [← sq, Real.log_pow]; push_cast; ring

/-- The Dirichlet sum of the `AND` indicator is `2p`. -/
lemma dirichlet_andInd (p : ℝ) :
    ∑ e : Bool, expect (bernoulliWeight p)
      (fun ω => (andInd (setOpen e ω) - andInd (setClosed e ω)) ^ 2) = 2 * p := by
  simp [expect, weight, sum_configSpace_bool, andInd, bernoulliWeight, setOpen, setClosed]
  ring

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : -(p ^ 2 * Real.log (p ^ 2)) ≤ 2 * p := by
  have h := fsc2_globalLSI hp0 hp1 andInd
  rwa [ent_andInd, dirichlet_andInd] at h

/-! ## The noise operator on coefficients -/

example (S : Finset Bool) (hS : S.Nonempty) :
    ptn_coeff (1 / 3) (ptn_noiseOp (1 / 3) 0 andInd) S = 0 := by
  rw [fsc2_coeff_noiseOp (by norm_num) (by norm_num), zero_pow (Finset.card_ne_zero.mpr hS),
    zero_mul]

example (S : Finset Bool) :
    ptn_coeff (1 / 3) (ptn_noiseOp (1 / 3) 1 andInd) S = ptn_coeff (1 / 3) andInd S := by
  rw [fsc2_coeff_noiseOp (by norm_num) (by norm_num), one_pow, one_mul]

/-! ## The predicates -/

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    fsc2_EntMassFamily p (fun ω : ConfigSpace Bool => ω true && ω false) :=
  fsc2_entMassFamily_holds hp0 hp1 _

example : fsc2_EntMassFamily (11 / 20) and5 := fsc2_residue_nonvac (by norm_num) (by norm_num) and5

/-- At `p = 11/20 ∈ (1/2, 1)`, the five-bit `AND` meets all antecedents of
the damping estimate. -/
example :
    (11 / 20 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1
      ∧ 0 < var (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
      ∧ 0 < maxInfl (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
      ∧ maxInfl (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
        < Real.exp (-(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20)))))
      ∧ fsc2_EntMassFamily (11 / 20) and5 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, fsc2_entMassFamily_holds (by norm_num)
    (by norm_num) and5⟩
  · rw [var_and5]; norm_num
  · rw [maxInfl_and5]; norm_num
  · rw [maxInfl_and5]; exact and5_below_threshold

/-- The damping estimate holds for the five-bit `AND` at `p = 11/20`:
the damped mass at the threshold `exp (-1/(2p(1-p))) ≤ 1/7` is at most `maxInfl · Var`. -/
example :
    pen_dampedMass (11 / 20) (Real.exp (-(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20))))))
        (fun ω => if and5 ω then (1 : ℝ) else 0)
      ≤ maxInfl (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
        * var (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0) := by
  rw [dampedMass_and5 (by norm_num) (by norm_num), maxInfl_and5, var_and5]
  have hr := threshold_le_seventh
  have hr0 := Real.exp_pos (-(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20)))))
  set r0 := Real.exp (-(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20)))))
  have hb : (1 + (1 - 11 / 20) / (11 / 20) * r0) ^ 5
      ≤ (1 + (1 - 11 / 20) / (11 / 20) * (1 / 7 : ℝ)) ^ 5 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 5
  calc (11 / 20 : ℝ) ^ 10 * ((1 + (1 - 11 / 20) / (11 / 20) * r0) ^ 5 - 1)
      ≤ (11 / 20 : ℝ) ^ 10 * ((1 + (1 - 11 / 20) / (11 / 20) * (1 / 7)) ^ 5 - 1) := by gcongr
    _ ≤ (11 / 20) ^ 4 * ((11 / 20) ^ 5 * (1 - (11 / 20) ^ 5)) := by norm_num

end StatMechTest.BooleanFunctions.FourierLogSobolev
