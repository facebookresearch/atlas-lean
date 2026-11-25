/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Real.Basic

import Mathlib.Tactic

/-!
# Finite-prior Bayes update: normalization and sequential/batch agreement

Weights are real functions on a `Fintype`. `finitePosterior π L θ` is
`π θ * L θ / ∑ θ', π θ' * L θ'`; at zero evidence Lean's `x / 0 = 0` makes it
the zero function. Normalization statements assume nonzero (or positive)
evidence, and the zero-evidence and prior-likelihood-conflict boundaries are
stated explicitly. Sequential updating on a list of observations agrees with
the one-shot update by the batch likelihood, with no evidence hypothesis: at
zero evidence both sides are the zero function. The identification of
`postWeight` from `FiniteConsistency` with these updates lives in that file,
so this module stays free of the asymptotic consistency machinery.
-/

@[expose] public section


namespace MathlibExt.Probability.Statistics.Bayesian

variable {Θ : Type*} [Fintype Θ]

/-- The evidence (marginal likelihood) of an observation with likelihood weights `L` under
prior weights `π` on finitely many hypotheses: `∑ θ, π θ * L θ`. -/
noncomputable def finiteEvidence (π L : Θ → ℝ) : ℝ :=
  ∑ θ, π θ * L θ

/-- The Bayes update of the prior weights `π` by the likelihood weights `L`:
`π θ * L θ / finiteEvidence π L`. At zero evidence this is the zero function (`x / 0 = 0`). -/
noncomputable def finitePosterior (π L : Θ → ℝ) (θ : Θ) : ℝ :=
  π θ * L θ / finiteEvidence π L

/-- The joint likelihood of a list of observations, the pointwise product of their likelihood
weights; `1` for the empty list. -/
def batchLikelihood (Ls : List (Θ → ℝ)) (θ : Θ) : ℝ :=
  (Ls.map fun L => L θ).prod

/-- Updating the prior on the observations one at a time, in list order. -/
noncomputable def sequentialPosterior (π : Θ → ℝ) : List (Θ → ℝ) → Θ → ℝ
  | [] => π
  | L :: Ls => sequentialPosterior (finitePosterior π L) Ls

theorem finiteEvidence_nonneg {π L : Θ → ℝ} (hπ : ∀ θ, 0 ≤ π θ) (hL : ∀ θ, 0 ≤ L θ) :
    0 ≤ finiteEvidence π L := by
  unfold finiteEvidence
  exact Finset.sum_nonneg fun θ _ => mul_nonneg (hπ θ) (hL θ)

theorem finitePosterior_nonneg {π L : Θ → ℝ} (hπ : ∀ θ, 0 ≤ π θ) (hL : ∀ θ, 0 ≤ L θ)
    (θ : Θ) : 0 ≤ finitePosterior π L θ := by
  unfold finitePosterior
  exact div_nonneg (mul_nonneg (hπ θ) (hL θ)) (finiteEvidence_nonneg hπ hL)

/-- **Normalization**: with nonzero evidence the updated weights sum to `1`. -/
theorem sum_finitePosterior {π L : Θ → ℝ} (hE : finiteEvidence π L ≠ 0) :
    ∑ θ, finitePosterior π L θ = 1 := by
  unfold finitePosterior finiteEvidence at *
  rw [← Finset.sum_div, div_self hE]

/-- The zero-evidence convention: the update is the zero function, not a probability vector. -/
theorem finitePosterior_eq_zero_of_finiteEvidence_eq_zero {π L : Θ → ℝ}
    (hE : finiteEvidence π L = 0) (θ : Θ) : finitePosterior π L θ = 0 := by
  unfold finitePosterior
  rw [hE, div_zero]

/-- A hypothesis with zero prior or zero likelihood gets zero posterior weight. -/
theorem finitePosterior_eq_zero_of_mul_eq_zero {π L : Θ → ℝ} {θ : Θ}
    (h : π θ * L θ = 0) : finitePosterior π L θ = 0 := by
  unfold finitePosterior
  rw [h, zero_div]

/-- The evidence of a second observation under the first posterior is the joint evidence divided
by the first evidence. No hypothesis is needed: at zero first evidence both sides are `0`. -/
theorem finiteEvidence_finitePosterior (π L₁ L₂ : Θ → ℝ) :
    finiteEvidence (finitePosterior π L₁) L₂ =
      finiteEvidence π (fun θ => L₁ θ * L₂ θ) / finiteEvidence π L₁ := by
  unfold finiteEvidence finitePosterior
  simp only [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro θ _
  ring

/-- **Two-step agreement**: updating on `L₁` and then on `L₂` is updating once on `L₁ * L₂`,
provided the first evidence is nonzero. -/
theorem finitePosterior_finitePosterior {π L₁ L₂ : Θ → ℝ} (hE : finiteEvidence π L₁ ≠ 0) :
    finitePosterior (finitePosterior π L₁) L₂ = finitePosterior π (fun θ => L₁ θ * L₂ θ) := by
  have hEv := finiteEvidence_finitePosterior π L₁ L₂
  funext θ
  simp only [finitePosterior]
  rw [hEv]
  by_cases hE12 : finiteEvidence π (fun θ => L₁ θ * L₂ θ) = 0
  · simp [hE12]
  · field_simp

omit [Fintype Θ] in
theorem batchLikelihood_nil : batchLikelihood ([] : List (Θ → ℝ)) = fun _ => 1 := by
  rfl

omit [Fintype Θ] in
theorem batchLikelihood_cons (L : Θ → ℝ) (Ls : List (Θ → ℝ)) :
    batchLikelihood (L :: Ls) = fun θ => L θ * batchLikelihood Ls θ := by
  rfl

omit [Fintype Θ] in
theorem batchLikelihood_nonneg {Ls : List (Θ → ℝ)} (hL : ∀ L ∈ Ls, ∀ θ, 0 ≤ L θ) (θ : Θ) :
    0 ≤ batchLikelihood Ls θ := by
  unfold batchLikelihood
  apply List.prod_nonneg
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨L, hLmem, rfl⟩ := ha
  exact hL L hLmem θ

omit [Fintype Θ] in
theorem batchLikelihood_perm {Ls Ls' : List (Θ → ℝ)} (h : Ls.Perm Ls') :
    batchLikelihood Ls = batchLikelihood Ls' := by
  funext θ
  unfold batchLikelihood
  exact List.Perm.prod_eq ((h.map _))

private theorem zero_evidence_sequentialPosterior_zero (Ls : List (Θ → ℝ)) :
    sequentialPosterior (fun _ => 0) Ls = fun _ => 0 := by
  induction Ls with
  | nil => rfl
  | cons L Ls' ih =>
    have h0 : finitePosterior (fun _ => 0) L = fun _ => 0 := by
      funext θ
      exact finitePosterior_eq_zero_of_mul_eq_zero (zero_mul (L θ))
    have hseq_def : sequentialPosterior (fun _ => 0) (L :: Ls') =
        sequentialPosterior (finitePosterior (fun _ => 0) L) Ls' := rfl
    rw [hseq_def, h0, ih]

/-- **Sequential/batch agreement**: for a normalized nonnegative prior and nonnegative
likelihoods, updating one observation at a time gives the batch posterior. No evidence
hypothesis is needed: at zero evidence both sides are the zero function. `∑ π = 1` is used
for the empty list. -/
theorem sequentialPosterior_eq_finitePosterior_batchLikelihood {π : Θ → ℝ}
    (hπ : ∀ θ, 0 ≤ π θ) (hπ1 : ∑ θ, π θ = 1) {Ls : List (Θ → ℝ)}
    (hL : ∀ L ∈ Ls, ∀ θ, 0 ≤ L θ) :
    sequentialPosterior π Ls = finitePosterior π (batchLikelihood Ls) := by
  have key : ∀ (Ls : List (Θ → ℝ)) (π : Θ → ℝ),
      (∀ θ, 0 ≤ π θ) → ∑ θ, π θ = 1 →
      (∀ L ∈ Ls, ∀ θ, 0 ≤ L θ) →
      sequentialPosterior π Ls = finitePosterior π (batchLikelihood Ls) := by
    intro Ls
    induction Ls with
    | nil =>
      intro π hπ hπ1 hL
      have hbatch : batchLikelihood ([] : List (Θ → ℝ)) = fun _ => 1 := batchLikelihood_nil
      rw [hbatch]
      have hseq_nil : sequentialPosterior π ([] : List (Θ → ℝ)) = π := rfl
      rw [hseq_nil]
      funext θ
      simp only [finitePosterior, finiteEvidence, mul_one]
      rw [hπ1, div_one]
    | cons L Ls' ih =>
      intro π hπ hπ1 hL
      have hLhead : ∀ θ, 0 ≤ L θ := fun θ => hL L (by simp) θ
      have hLtail : ∀ L' ∈ Ls', ∀ θ, 0 ≤ L' θ :=
        fun L' hmem θ => hL L' (by simp [hmem]) θ
      have hbatch_cons : batchLikelihood (L :: Ls') =
          fun θ => L θ * batchLikelihood Ls' θ :=
        batchLikelihood_cons L Ls'
      by_cases hE1 : finiteEvidence π L = 0
      · have hf : 0 ≤ (fun θ => π θ * L θ) := fun θ => mul_nonneg (hπ θ) (hLhead θ)
        have hsum : (∑ θ, π θ * L θ) = 0 := by
          simpa [finiteEvidence] using hE1
        have hfun : (fun θ => π θ * L θ) = 0 :=
          (Fintype.sum_eq_zero_iff_of_nonneg hf).mp hsum
        have hzero_each : ∀ θ, π θ * L θ = 0 := fun θ => congrFun hfun θ
        have hjoint_zero : finiteEvidence π (fun θ => L θ * batchLikelihood Ls' θ) = 0 := by
          simp only [finiteEvidence]
          apply Finset.sum_eq_zero
          intro θ _
          have hz := hzero_each θ
          rw [← mul_assoc, hz, zero_mul]
        have hpost0 : finitePosterior π L = fun _ => 0 := by
          funext θ
          exact finitePosterior_eq_zero_of_finiteEvidence_eq_zero hE1 θ
        have hseq0 : sequentialPosterior π (L :: Ls') = fun _ => 0 := by
          have hseq_def : sequentialPosterior π (L :: Ls') =
              sequentialPosterior (finitePosterior π L) Ls' := rfl
          rw [hseq_def, hpost0]
          exact zero_evidence_sequentialPosterior_zero Ls'
        have hbatch0 : finitePosterior π (batchLikelihood (L :: Ls')) = fun _ => 0 := by
          rw [hbatch_cons]
          funext θ
          exact finitePosterior_eq_zero_of_finiteEvidence_eq_zero hjoint_zero θ
        exact hseq0.trans hbatch0.symm
      · have hE1_ne : finiteEvidence π L ≠ 0 := hE1
        have hπ'_nonneg : ∀ θ, 0 ≤ finitePosterior π L θ :=
          finitePosterior_nonneg hπ hLhead
        have hπ'1 : ∑ θ, finitePosterior π L θ = 1 := sum_finitePosterior hE1_ne
        have hIH := ih (finitePosterior π L) hπ'_nonneg hπ'1 hLtail
        have hseq_def : sequentialPosterior π (L :: Ls') =
            sequentialPosterior (finitePosterior π L) Ls' := rfl
        rw [hseq_def, hIH, finitePosterior_finitePosterior hE1_ne]
        rw [← hbatch_cons]
  exact key Ls π hπ hπ1 hL

/-- The sequential posterior is normalized. -/
theorem sum_sequentialPosterior {π : Θ → ℝ}
    (hπ : ∀ θ, 0 ≤ π θ) (hπ1 : ∑ θ, π θ = 1) {Ls : List (Θ → ℝ)}
    (hL : ∀ L ∈ Ls, ∀ θ, 0 ≤ L θ) (hE : 0 < finiteEvidence π (batchLikelihood Ls)) :
    ∑ θ, sequentialPosterior π Ls θ = 1 := by
  rw [sequentialPosterior_eq_finitePosterior_batchLikelihood hπ hπ1 hL]
  exact sum_finitePosterior (ne_of_gt hE)

/-- The sequential posterior does not depend on the order of the observations. -/
theorem sequentialPosterior_perm {π : Θ → ℝ}
    (hπ : ∀ θ, 0 ≤ π θ) (hπ1 : ∑ θ, π θ = 1) {Ls Ls' : List (Θ → ℝ)} (h : Ls.Perm Ls')
    (hL : ∀ L ∈ Ls, ∀ θ, 0 ≤ L θ) :
    sequentialPosterior π Ls = sequentialPosterior π Ls' := by
  have hbatch : batchLikelihood Ls = batchLikelihood Ls' := batchLikelihood_perm h
  have hL' : ∀ L ∈ Ls', ∀ θ, 0 ≤ L θ := fun L hmem θ => hL L ((h.mem_iff).mpr hmem) θ
  rw [sequentialPosterior_eq_finitePosterior_batchLikelihood hπ hπ1 hL,
    sequentialPosterior_eq_finitePosterior_batchLikelihood hπ hπ1 hL', hbatch]

end MathlibExt.Probability.Statistics.Bayesian
