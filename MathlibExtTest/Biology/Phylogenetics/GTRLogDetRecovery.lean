/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.GTRLogDetRecovery
import Mathlib.Analysis.Matrix.Order

/-!
# Tests for the log-det recovery of the GTR rate matrix

* Definition-level values of `baseFreq` and `normDivergence` on a concrete non-symmetric
  divergence matrix, computed from the definitions.
* Boundary case `t = 0` (a sequence compared with itself): for a diagonal divergence matrix with
  positive marginals, `normDivergence = 1`, the log-det distance is `0` and the rate estimate
  degenerates to `0`, all computed from the definitions (not through `logDetDistance_gtr`).
  The paralinear form `logDetDistance_eq_logDet` is non-vacuous there.
* Non-vacuity of the recovery hypotheses: the two-state equal-rates model and the K80 model on
  the nucleotides satisfy them, with traces computed from `gtrRate`; the recovered matrices are
  stated explicitly.
* The consistency theorem applied to the constant divergence sequence.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory Filter Topology

namespace MathlibExtTest.Biology.Phylogenetics.GTRLogDetRecovery

open MathlibExt.Biology.Phylogenetics.GTRLogDetRecovery
open MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-! ## Definition-level values -/

/-- A non-symmetric divergence matrix on two states. -/
noncomputable def F₁ : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 10, 1 / 10; 2 / 10, 4 / 10]

/-- The base-frequency estimate averages the two marginals: `(0.4 + 0.5) / 2` and
`(0.6 + 0.5) / 2`. -/
example : baseFreq F₁ 0 = 9 / 20 ∧ baseFreq F₁ 1 = 11 / 20 := by
  constructor <;> norm_num [baseFreq, F₁, Fin.sum_univ_two]

/-- The normalized divergence matrix symmetrizes the off-diagonal entries `0.1` and `0.2` to
`0.15` before normalizing. -/
example : normDivergence F₁ 0 1 = 3 / 20 / (√(9 / 20) * √(11 / 20)) := by
  have h0 : baseFreq F₁ 0 = 9 / 20 := by norm_num [baseFreq, F₁, Fin.sum_univ_two]
  have h1 : baseFreq F₁ 1 = 11 / 20 := by norm_num [baseFreq, F₁, Fin.sum_univ_two]
  rw [normDivergence, of_apply, h0, h1]
  norm_num [F₁]

/-- The normalized divergence matrix is symmetric even though `F₁` is not. -/
example : normDivergence F₁ 0 1 = normDivergence F₁ 1 0 := by
  have h := congrFun (congrFun (isSelfAdjoint_normDivergence F₁) 0) 1
  simpa [star_eq_conjTranspose] using h.symm

/-! ## Boundary case: zero divergence -/

section Boundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}

theorem baseFreq_diagonal : baseFreq (diagonal p) = p := by
  funext i
  simp [baseFreq, diagonal_apply]

/-- A diagonal divergence matrix with positive marginals normalizes to the identity. -/
theorem normDivergence_diagonal (hp : ∀ i, 0 < p i) : normDivergence (diagonal p) = 1 := by
  ext i j
  rw [normDivergence, of_apply, baseFreq_diagonal]
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, one_apply_eq, Real.mul_self_sqrt (hp i).le]
    field_simp [(hp i).ne']
    ring
  · simp [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h), one_apply_ne h]

/-- **Zero distance from a sequence to itself**, computed from the definitions. -/
theorem logDetDistance_diagonal (hp : ∀ i, 0 < p i) : logDetDistance (diagonal p) = 0 := by
  open scoped Matrix.Norms.L2Operator in
  rw [logDetDistance, normDivergence_diagonal hp, ← CFC.log, CFC.log_one, trace_zero, neg_zero]

/-- At zero divergence the rate estimate degenerates to the zero matrix (Lean's `0⁻¹ = 0`): one
branch of length `0` carries no information about the rate matrix. -/
theorem rateEstimate_diagonal (hp : ∀ i, 0 < p i) : rateEstimate (diagonal p) = 0 := by
  rw [rateEstimate, logDetDistance_diagonal hp, _root_.inv_zero, zero_smul]

/-- The paralinear form is non-vacuous: at a diagonal divergence matrix its hypotheses hold and
both sides are `0`. -/
example (hp : ∀ i, 0 < p i) :
    -Real.log (Matrix.of fun i j => (diagonal p i j + diagonal p j i) / 2).det +
      ∑ i, Real.log (baseFreq (diagonal p) i) = 0 := by
  have hb : ∀ i, 0 < baseFreq (diagonal p) i := fun i => by rw [baseFreq_diagonal]; exact hp i
  have hpd : (normDivergence (diagonal p)).PosDef := by
    rw [normDivergence_diagonal hp]
    exact PosDef.one
  rw [← logDetDistance_eq_logDet hb hpd, logDetDistance_diagonal hp]

end Boundary

/-! ## Non-vacuity of the recovery hypotheses -/

/-- Two states, equal frequencies, unit exchangeability. -/
noncomputable def π₂ : Fin 2 → ℝ := fun _ => 1 / 2

/-- Unit exchangeabilities. -/
def s₂ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1

/-- The two-state rate matrix, computed from `gtrRate`. -/
example : gtrRate π₂ s₂ = !![-1 / 2, 1 / 2; 1 / 2, -1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gtrRate, π₂, s₂]

/-- Its trace, computed from the definition, is `-1`. -/
theorem trace_gtrRate_two : (gtrRate π₂ s₂).trace = -1 := by
  norm_num [trace, gtrRate, π₂, s₂, Fin.sum_univ_two]

/-- **Exact recovery, two states**: for every branch length `t ≠ 0`, the log-det rate estimate
of the divergence matrix returns the rate matrix itself (its trace is already `-1`). -/
example {t : ℝ} (ht : t ≠ 0) :
    rateEstimate (diagonal π₂ * ctmcTransition (gtrRate π₂ s₂) t) = gtrRate π₂ s₂ := by
  rw [rateEstimate_gtr (fun _ => by norm_num [π₂]) (fun _ _ => rfl)
    (fun _ _ _ => by norm_num [s₂]) ht, trace_gtrRate_two, neg_neg, inv_one, one_smul]

/-- **Exact log-det distance, two states**: it is the branch length `t`. -/
example (t : ℝ) : logDetDistance (diagonal π₂ * ctmcTransition (gtrRate π₂ s₂) t) = t := by
  rw [logDetDistance_gtr (fun _ => by norm_num [π₂]) (fun _ _ => rfl)
    (fun _ _ _ => by norm_num [s₂]), trace_gtrRate_two]
  ring

/-- The K80 exchangeabilities satisfy the recovery hypotheses for `κ > 0`. -/
theorem hky_hyps {κ : ℝ} (hκ : 0 < κ) :
    (∀ i j, hkyExchangeability κ i j = hkyExchangeability κ j i) ∧
      ∀ i j, i ≠ j → 0 < hkyExchangeability κ i j := by
  refine ⟨fun i j => ?_, fun i j _ => ?_⟩
  · simp only [hkyExchangeability, of_apply, eq_comm (a := (i : ℕ) % 2)]
  · simp only [hkyExchangeability, of_apply]
    split_ifs <;> norm_num [hκ]

/-- The trace of the K80 rate matrix, computed from the definition: `-(κ + 2) / 4` per state,
four states. -/
theorem trace_k80Rate (κ : ℝ) : (k80Rate κ).trace = -(κ + 2) := by
  simp only [k80Rate, hkyRate, trace, diag_apply, gtrRate, of_apply, ite_true, hkyExchangeability,
    Fin.sum_univ_four]
  simp [Finset.sum_erase_eq_sub, Fin.sum_univ_four]
  ring

/-- **Exact recovery, K80**: the log-det rate estimate returns `k80Rate κ / (κ + 2)`. -/
example {κ t : ℝ} (hκ : 0 < κ) (ht : t ≠ 0) :
    rateEstimate (diagonal (fun _ => 1 / 4) * ctmcTransition (k80Rate κ) t) =
      (κ + 2)⁻¹ • k80Rate κ := by
  obtain ⟨hsymm, hs⟩ := hky_hyps hκ
  have h := rateEstimate_gtr (π := fun _ : Fin 4 => (1 : ℝ) / 4) (fun _ => by norm_num) hsymm
    (fun i j hij => (hs i j hij).le) ht
  rw [show gtrRate (fun _ : Fin 4 => (1 : ℝ) / 4) (hkyExchangeability κ) = k80Rate κ from rfl,
    trace_k80Rate, neg_neg] at h
  exact h

/-- **Recovery of the K80 exchangeabilities up to scale**: transitions recover `κ / (κ + 2)`. -/
example {κ t : ℝ} (hκ : 0 < κ) (ht : t ≠ 0) :
    rateEstimate (diagonal (fun _ => 1 / 4) * ctmcTransition (k80Rate κ) t) 0 2 /
        baseFreq (diagonal (fun _ => 1 / 4) * ctmcTransition (k80Rate κ) t) 2 =
      (κ + 2)⁻¹ * κ := by
  obtain ⟨hsymm, hs⟩ := hky_hyps hκ
  have h := exchangeability_gtr (π := fun _ : Fin 4 => (1 : ℝ) / 4) (fun _ => by norm_num) hsymm
    (fun i j hij => (hs i j hij).le) ht (i := 0) (j := 2) (by decide)
  rw [show gtrRate (fun _ : Fin 4 => (1 : ℝ) / 4) (hkyExchangeability κ) = k80Rate κ from rfl,
    trace_k80Rate, neg_neg] at h
  rw [h]
  simp [hkyExchangeability]

/-! ## Consistency, applied -/

/-- The consistency theorem applies to the constant (exact) divergence sequence. -/
example {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun _ : ℕ => rateEstimate (diagonal π₂ * ctmcTransition (gtrRate π₂ s₂) t)) atTop
      (𝓝 ((-(gtrRate π₂ s₂).trace)⁻¹ • gtrRate π₂ s₂)) :=
  (tendsto_rateEstimate_gtr (fun _ => by norm_num [π₂]) (fun _ _ => rfl)
    (fun _ _ _ => by norm_num [s₂]) ht tendsto_const_nhds).1

end MathlibExtTest.Biology.Phylogenetics.GTRLogDetRecovery
