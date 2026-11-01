/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.GeneConstraint
public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization

import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture

/-!
# EM for the class weights of a Poisson constraint mixture (pLI)

Lek et al. (2016) fit pLI by expectation-maximization: each gene `n` has an observed LoF count
`o_n` and an expected count `E_n > 0`; its class `z` is latent with prior weights `w`, and
given the class `o_n ~ Poisson(rate_z E_n)` with fixed class rates. One EM step replaces the
weights by the average class posteriors, `w'_z = (1/N) ∑_n P_w(z | o_n)`. This file proves that
the step returns admissible weights and never decreases the log-likelihood, as an instance of
the repository's generic EM theorem.

## Main results

* `PosWeights`: strictly positive weights summing to one (the parameter space).
* `emStep`: the EM update of the weights; `emQ_le_emStep`: it maximizes `Q(· | w)`.
* `logLik_le_logLik_emStep`: **the likelihood does not decrease** along an EM step.
* `logLik_iterate_emStep_monotone`: it is monotone along the EM iterates.

## Cost model

No running-time model: the subject is the likelihood, over the reals.

## References

* M. Lek et al., *Analysis of protein-coding genetic variation in 60,706 humans*, Nature 536
  (2016), 285–291 (Supplementary Information, pLI).
* A. P. Dempster, N. M. Laird, D. B. Rubin, *Maximum likelihood from incomplete data via the
  EM algorithm*, J. Roy. Statist. Soc. B 39 (1977), 1–38.
-/

@[expose] public section

open Real Finset
open MathlibExt.Biology.StatisticalGenetics.GeneConstraint
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization

namespace Cslib.Bioinformatics.StatisticalGenetics.PoissonClassEM

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- Strictly positive class weights summing to one. -/
def PosWeights (ι : Type*) [Fintype ι] : Type _ :=
  {w : ι → ℝ // (∀ c, 0 < w c) ∧ ∑ c, w c = 1}

/-- A gene's data: observed LoF count `o` and positive expected count `E`. -/
structure GeneData where
  /-- Observed LoF count. -/
  o : ℕ
  /-- Expected LoF count under neutrality. -/
  E : ℝ
  E_pos : 0 < E

/-- The joint likelihood of a gene's data and class `z`: `w_z P(o | rate_z E)`. -/
noncomputable def joint (rate : ι → ℝ) (w : PosWeights ι) (x : GeneData) (z : ι) : ℝ :=
  w.1 z * poissonLik (rate z * x.E) x.o

/-- The joint likelihood is positive for positive rates. -/
theorem joint_pos {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c) (w : PosWeights ι) (x : GeneData)
    (z : ι) : 0 < joint rate w x z :=
  mul_pos (w.2.1 z) (poissonLik_pos (mul_pos (hrate z) x.E_pos) _)

/-- The expected number of genes in class `z` under the posteriors at weights `w`:
`∑_n P_w(z | o_n)`. -/
noncomputable def mass (rate : ι → ℝ) (xs : Fin N → GeneData) (w : PosWeights ι) (z : ι) : ℝ :=
  ∑ n, posterior (joint rate) w (xs n) z

private theorem posterior_pos [Nonempty ι] {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c)
    (w : PosWeights ι) (x : GeneData) (z : ι) : 0 < posterior (joint rate) w x z :=
  div_pos (joint_pos hrate w x z)
    (Finset.sum_pos (fun z _ => joint_pos hrate w x z) Finset.univ_nonempty)

/-- The class masses are positive when there is at least one gene. -/
theorem mass_pos [Nonempty ι] {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c)
    (xs : Fin N → GeneData) (hN : 0 < N) (w : PosWeights ι) (z : ι) : 0 < mass rate xs w z := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact Finset.sum_pos (fun n _ => posterior_pos hrate w (xs n) z) Finset.univ_nonempty

/-- The class masses add up to the number of genes. -/
theorem sum_mass [Nonempty ι] {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c)
    (xs : Fin N → GeneData) (w : PosWeights ι) : ∑ z, mass rate xs w z = N := by
  unfold mass
  rw [Finset.sum_comm]
  simp [(isDist_posterior (fun w x z => joint_pos hrate w x z) w _).2]

/-- The EM update `w'_z = (1/N) ∑_n P_w(z | o_n)`, for `N > 0` genes and positive rates. -/
noncomputable def emStep [Nonempty ι] {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c)
    (xs : Fin N → GeneData) (hN : 0 < N) (w : PosWeights ι) : PosWeights ι :=
  ⟨fun z => mass rate xs w z / N, fun z => div_pos (mass_pos hrate xs hN w z)
    (by exact_mod_cast hN), by
    rw [← Finset.sum_div, sum_mass hrate xs w]
    exact div_self (by exact_mod_cast hN.ne')⟩

private theorem emQ_eq [Nonempty ι] {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c)
    (xs : Fin N → GeneData) (w' w : PosWeights ι) :
    emQ (joint rate) xs w' w = ∑ z, mass rate xs w z * log (w'.1 z) +
      ∑ n, ∑ z, posterior (joint rate) w (xs n) z *
        log (poissonLik (rate z * (xs n).E) (xs n).o) := by
  unfold emQ mass
  simp_rw [joint, log_mul (w'.2.1 _).ne'
    (poissonLik_pos (mul_pos (hrate _) (GeneData.E_pos _)) _).ne', mul_add,
    Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun n z => posterior (joint rate) w (xs n) z * log (w'.1 z))]

/-- **The M-step maximizes `Q(· | w)`** over admissible weights. -/
theorem emQ_le_emStep [Nonempty ι] {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c)
    (xs : Fin N → GeneData) (hN : 0 < N) (w' w : PosWeights ι) :
    emQ (joint rate) xs w' w ≤ emQ (joint rate) xs (emStep hrate xs hN w) w := by
  rw [emQ_eq hrate, emQ_eq hrate]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Cslib.MachineLearning.LatentVariable.BernoulliMixture.sum_mul_log_le_sum_mul_log_div
    (fun z => (mass_pos hrate xs hN w z).le) (by rw [sum_mass hrate xs w]; exact hNr)
    w'.2.1 w'.2.2
  rw [sum_mass hrate xs w] at h
  have : ∑ z, mass rate xs w z * log ((emStep hrate xs hN w).1 z) =
      ∑ z, mass rate xs w z * log (mass rate xs w z / N) := rfl
  linarith

/-- **EM does not decrease the likelihood** of the class weights. -/
theorem logLik_le_logLik_emStep [Nonempty ι] {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c)
    (xs : Fin N → GeneData) (hN : 0 < N) (w : PosWeights ι) :
    logLik (joint rate) xs w ≤ logLik (joint rate) xs (emStep hrate xs hN w) :=
  logLik_le_of_emQ_le (fun w x z => joint_pos hrate w x z) xs (emQ_le_emStep hrate xs hN w w)

/-- The log-likelihood is monotone along the EM iterates. -/
theorem logLik_iterate_emStep_monotone [Nonempty ι] {rate : ι → ℝ} (hrate : ∀ c, 0 < rate c)
    (xs : Fin N → GeneData) (hN : 0 < N) (w₀ : PosWeights ι) :
    Monotone fun k => logLik (joint rate) xs ((emStep hrate xs hN)^[k] w₀) :=
  logLik_iterate_monotone (fun w x z => joint_pos hrate w x z) xs
    (fun w => emQ_le_emStep hrate xs hN w w) w₀

end Cslib.Bioinformatics.StatisticalGenetics.PoissonClassEM
