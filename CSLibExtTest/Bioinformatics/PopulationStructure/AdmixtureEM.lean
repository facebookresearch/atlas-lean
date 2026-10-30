/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationStructure.AdmixtureEM
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# ADMIXTURE EM tests

Closed checks:
- the allele-copy encoding on the three genotypes (`isRef`);
- a two-population, one-individual, one-SNP instance with `Q = (1/4, 3/4)`, `F = (1/2, 1/3)`,
  where `marginal_eq` gives the reference probability `3/8` and the alternative `5/8`;
- `K = 1`: the ADMIXTURE log-likelihood is the binomial log-likelihood of the pooled allele counts,
  `∑ j, (n j * log (F j) + (2 I - n j) * log (1 - F j))` with `n j = ∑ i, g i j`;
- the EM theorems instantiated on a polymorphic `3 × 2` genotype matrix with `K = 2`.

The definitions are real-valued and not executable.
-/

namespace Cslib.Bioinformatics.PopulationStructure.AdmixtureEM

open Real Cslib.MachineLearning.LatentVariable.ExpectationMaximization

/-! ## The allele-copy encoding -/

example : isRef (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 3)) 0 0 0 = false := by decide
example : isRef (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 3)) 0 0 1 = false := by decide
example : isRef (fun (_ : Fin 1) (_ : Fin 1) => (1 : Fin 3)) 0 0 0 = true := by decide
example : isRef (fun (_ : Fin 1) (_ : Fin 1) => (1 : Fin 3)) 0 0 1 = false := by decide
example : isRef (fun (_ : Fin 1) (_ : Fin 1) => (2 : Fin 3)) 0 0 0 = true := by decide
example : isRef (fun (_ : Fin 1) (_ : Fin 1) => (2 : Fin 3)) 0 0 1 = true := by decide

/-! ## A two-population instance -/

/-- One individual with ancestry `(1/4, 3/4)`, one SNP with frequencies `(1/2, 1/3)`. -/
noncomputable def θ₂ : Params (Fin 1) (Fin 1) (Fin 2) where
  Q _ := ![1 / 4, 3 / 4]
  F k _ := ![1 / 2, 1 / 3] k
  Q_pos _ k := by fin_cases k <;> norm_num
  Q_sum _ := by norm_num [Fin.sum_univ_two]
  F_pos k _ := by fin_cases k <;> norm_num
  F_lt_one k _ := by fin_cases k <;> norm_num

example : qf θ₂ 0 0 = 3 / 8 := by norm_num [qf, θ₂, Fin.sum_univ_two]

example : marginal joint θ₂ (0, 0, true) = 3 / 8 := by
  rw [marginal_eq]
  norm_num [qf, θ₂, Fin.sum_univ_two]

example : marginal joint θ₂ (0, 0, false) = 5 / 8 := by
  rw [marginal_eq]
  norm_num [qf, θ₂, Fin.sum_univ_two]

-- The same numbers straight from the definition of the marginal.
example : marginal joint θ₂ (0, 0, true) = 3 / 8 := by
  norm_num [marginal, joint, θ₂, Fin.sum_univ_two]

/-! ## One population: the binomial likelihood of pooled counts -/

example {I J : Type*} [Fintype I] [Fintype J] (g : I → J → Fin 3) (θ : Params I J (Fin 1)) :
    admixtureLogLik g θ = ∑ j, ((∑ i, ((g i j).val : ℝ)) * log (θ.F 0 j) +
      (2 * Fintype.card I - ∑ i, ((g i j).val : ℝ)) * log (1 - θ.F 0 j)) := by
  have hQ : ∀ i, θ.Q i 0 = 1 := fun i => by simpa using θ.Q_sum i
  have hqf : ∀ i j, qf θ i j = θ.F 0 j := fun i j => by simp [qf, hQ]
  simp only [admixtureLogLik, hqf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib]
  simp [mul_comm]

/-! ## The EM theorems on a concrete genotype matrix -/

/-- Three individuals, two SNPs; both SNPs are polymorphic. -/
def g₃ : Fin 3 → Fin 2 → Fin 3 := ![![0, 2], ![1, 1], ![2, 0]]

theorem polymorphic_g₃ : Polymorphic g₃ := by
  intro j
  fin_cases j
  · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

example (θ : Params (Fin 3) (Fin 2) (Fin 2)) :
    logLik joint (data g₃) θ = admixtureLogLik g₃ θ :=
  logLik_eq_admixtureLogLik g₃ θ

example (θ' θ : Params (Fin 3) (Fin 2) (Fin 2)) :
    emQ joint (data g₃) θ' θ ≤ emQ joint (data g₃) (emStep g₃ polymorphic_g₃ θ) θ :=
  emQ_le_emStep g₃ polymorphic_g₃ θ' θ

example (θ₀ : Params (Fin 3) (Fin 2) (Fin 2)) {s t : ℕ} (hst : s ≤ t) :
    admixtureLogLik g₃ ((emStep g₃ polymorphic_g₃)^[s] θ₀) ≤
      admixtureLogLik g₃ ((emStep g₃ polymorphic_g₃)^[t] θ₀) :=
  admixtureLogLik_iterate_emStep_monotone g₃ polymorphic_g₃ θ₀ hst

-- The updated parameters are strictly inside the parameter set.
example (θ : Params (Fin 3) (Fin 2) (Fin 2)) (k : Fin 2) (j : Fin 2) :
    0 < (emStep g₃ polymorphic_g₃ θ).F k j ∧ (emStep g₃ polymorphic_g₃ θ).F k j < 1 :=
  ⟨(emStep g₃ polymorphic_g₃ θ).F_pos k j, (emStep g₃ polymorphic_g₃ θ).F_lt_one k j⟩

-- A monomorphic SNP (no reference copy anywhere) is not `Polymorphic`.
example : ¬ Polymorphic (fun (_ : Fin 2) (_ : Fin 1) => (0 : Fin 3)) := by
  intro h
  obtain ⟨i, hi⟩ := (h 0).1
  exact hi rfl

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
