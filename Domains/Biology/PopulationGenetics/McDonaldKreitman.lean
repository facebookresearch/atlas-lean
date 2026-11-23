/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.StrongLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The McDonald–Kreitman test and the proportion of adaptive substitutions

The McDonald–Kreitman (MK) test (McDonald & Kreitman 1991) classifies the variable sites of a
coding region into a 2×2 table: fixed differences between species (`D`) and polymorphisms
within species (`P`), each nonsynonymous (`n`) or synonymous (`s`). Under neutrality the
proportion of nonsynonymous changes is the same among fixed differences and polymorphisms.
Smith & Eyre-Walker (2002) estimate the proportion of adaptive nonsynonymous substitutions by

`α̂ = 1 - (D_s P_n) / (D_n P_s)`,

which is `1 - NI` for the neutrality index `NI = (P_n / P_s) / (D_n / D_s)`.

## Model

`MKModel` gives the expected counts. Synonymous mutations are neutral; a fraction `f₀` of
nonsynonymous mutations is neutral and the rest are either strongly deleterious (never
observed as polymorphisms or substitutions) or advantageous (fixed quickly, contributing
substitutions but no polymorphism). Expected counts are proportional to the mutational target
(`L_s`, `L_n`) of the neutral class, with the same neutral fraction `f₀` for divergence and
polymorphism, plus `A` expected adaptive substitutions:

`E P_s = θ_P L_s`, `E P_n = θ_P f₀ L_n`, `E D_s = λ_D L_s`, `E D_n = λ_D f₀ L_n + A`.

The model has **no slightly deleterious class**: slightly deleterious mutations would
contribute to polymorphism more than to divergence, and `α̂` is then biased downwards; this is
the condition under which the estimator is consistent, and it is a hypothesis here.

The exact MK test of the neutral null (`A = 0`) is Fisher's exact test of the 2×2 table, whose
conditional hypergeometric law is `cond_measureReal_eq_hypergeometricReal` in
`Probability/Statistics/ExactTests/FisherExact.lean`; it is not repeated here.

## Main results

* `alphaHat_eq_one_sub_neutralityIndex`: `α̂ = 1 - NI` (for all real counts).
* `MKModel.alphaHat_expected`: at the expected counts, `α̂ = A / E D_n` is the proportion of
  adaptive substitutions.
* `MKModel.propNonsyn_eq_iff`: the nonsynonymous proportions among expected fixed differences
  and polymorphisms agree iff `A = 0` (the MK null is neutrality).
* `MKModel.tendsto_alphaHat`: for independent, identically distributed loci, `α̂` computed from
  the summed counts of `m` loci converges almost surely to the true proportion as `m → ∞`.

## References

* J. H. McDonald and M. Kreitman, *Adaptive protein evolution at the Adh locus in
  Drosophila*, Nature 351 (1991), 652–654.
* N. G. C. Smith and A. Eyre-Walker, *Adaptive protein evolution in Drosophila*, Nature 415
  (2002), 1022–1024.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology Function

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.McDonaldKreitman

/-- The Smith–Eyre-Walker estimator of the proportion of adaptive nonsynonymous
substitutions, `α̂ = 1 - (D_s P_n) / (D_n P_s)`. -/
def alphaHat (Dn Ds Pn Ps : ℝ) : ℝ := 1 - Ds * Pn / (Dn * Ps)

/-- The neutrality index `NI = (P_n / P_s) / (D_n / D_s)`. -/
def neutralityIndex (Dn Ds Pn Ps : ℝ) : ℝ := Pn / Ps / (Dn / Ds)

/-- `α̂ = 1 - NI`, for all real counts (the junk values of division agree). -/
theorem alphaHat_eq_one_sub_neutralityIndex (Dn Ds Pn Ps : ℝ) :
    alphaHat Dn Ds Pn Ps = 1 - neutralityIndex Dn Ds Pn Ps := by
  rw [alphaHat, neutralityIndex, div_div_div_eq, mul_comm Ds Pn, mul_comm Dn Ps]

/-- Expected counts of the MK table without a slightly deleterious class (see the module
docstring): synonymous and nonsynonymous mutational targets `Ls`, `Ln`, neutral fraction `f₀`
of nonsynonymous mutations, polymorphisms and neutral fixed differences per unit of neutral
target `polyRate`, `divRate` (`θ_P`, `λ_D` in the module docstring), and `A` expected adaptive
substitutions. -/
structure MKModel where
  /-- Synonymous mutational target. -/
  Ls : ℝ
  /-- Nonsynonymous mutational target. -/
  Ln : ℝ
  /-- Fraction of nonsynonymous mutations that are neutral. -/
  f₀ : ℝ
  /-- Expected polymorphisms per unit of neutral target. -/
  polyRate : ℝ
  /-- Expected neutral fixed differences per unit of neutral target. -/
  divRate : ℝ
  /-- Expected number of adaptive nonsynonymous substitutions. -/
  A : ℝ
  Ls_pos : 0 < Ls
  Ln_pos : 0 < Ln
  f₀_pos : 0 < f₀
  f₀_le_one : f₀ ≤ 1
  polyRate_pos : 0 < polyRate
  divRate_pos : 0 < divRate
  A_nonneg : 0 ≤ A

namespace MKModel

variable (M : MKModel)

/-- Expected synonymous polymorphisms `E P_s = θ_P L_s`. -/
def EPs : ℝ := M.polyRate * M.Ls

/-- Expected nonsynonymous polymorphisms `E P_n = θ_P f₀ L_n`. -/
def EPn : ℝ := M.polyRate * M.f₀ * M.Ln

/-- Expected synonymous fixed differences `E D_s = λ_D L_s`. -/
def EDs : ℝ := M.divRate * M.Ls

/-- Expected nonsynonymous fixed differences `E D_n = λ_D f₀ L_n + A`. -/
def EDn : ℝ := M.divRate * M.f₀ * M.Ln + M.A

/-- The proportion of nonsynonymous substitutions that are adaptive, `α = A / E D_n`. -/
def alpha : ℝ := M.A / M.EDn

/-- **`α̂` at the expected counts is the proportion of adaptive substitutions**
(Smith & Eyre-Walker 2002): `1 - (E D_s E P_n) / (E D_n E P_s) = A / E D_n`. -/
theorem alphaHat_expected : alphaHat M.EDn M.EDs M.EPn M.EPs = M.alpha := by
  have := M.Ls_pos
  have := M.Ln_pos
  have := M.f₀_pos
  have := M.polyRate_pos
  have := M.divRate_pos
  have := M.A_nonneg
  have hD : 0 < M.EDn := by unfold EDn; positivity
  unfold alphaHat alpha
  rw [EDs, EPn, EPs]
  field_simp
  rw [EDn]
  ring

/-- **The MK null is neutrality**: the proportions of nonsynonymous changes among expected
fixed differences and expected polymorphisms agree iff there are no adaptive substitutions. -/
theorem propNonsyn_eq_iff :
    M.EDn / (M.EDn + M.EDs) = M.EPn / (M.EPn + M.EPs) ↔ M.A = 0 := by
  have := M.Ls_pos
  have := M.Ln_pos
  have := M.f₀_pos
  have := M.polyRate_pos
  have := M.divRate_pos
  have := M.A_nonneg
  have hD : 0 < M.EDn + M.EDs := by unfold EDn EDs; positivity
  have hP : 0 < M.EPn + M.EPs := by unfold EPn EPs; positivity
  have hPs : 0 < M.EPs := by unfold EPs; positivity
  have key : M.EDn * (M.EPn + M.EPs) - M.EPn * (M.EDn + M.EDs) = M.A * M.EPs := by
    unfold EDn EDs EPn EPs
    ring
  rw [div_eq_div_iff hD.ne' hP.ne']
  constructor
  · intro h
    have h0 : M.A * M.EPs = 0 := by linarith
    exact (mul_eq_zero.mp h0).resolve_right hPs.ne'
  · intro h
    rw [h, zero_mul] at key
    linarith

/-- **Consistency of `α̂` over loci**: let `Dn i, Ds i, Pn i, Ps i` be the counts at locus
`i`; suppose each of the four sequences consists of pairwise independent, identically
distributed, integrable variables whose means are the expected counts of `M` (the loci are
exchangeable copies of the model). Then almost surely `α̂` computed from the counts summed over
the first `m` loci converges to `α = A / E D_n` as `m → ∞`. -/
theorem tendsto_alphaHat {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {Dn Ds Pn Ps : ℕ → Ω → ℝ}
    (hDn : Integrable (Dn 0) μ) (hDs : Integrable (Ds 0) μ)
    (hPn : Integrable (Pn 0) μ) (hPs : Integrable (Ps 0) μ)
    (iDn : Pairwise ((· ⟂ᵢ[μ] ·) on Dn)) (iDs : Pairwise ((· ⟂ᵢ[μ] ·) on Ds))
    (iPn : Pairwise ((· ⟂ᵢ[μ] ·) on Pn)) (iPs : Pairwise ((· ⟂ᵢ[μ] ·) on Ps))
    (dDn : ∀ i, IdentDistrib (Dn i) (Dn 0) μ μ) (dDs : ∀ i, IdentDistrib (Ds i) (Ds 0) μ μ)
    (dPn : ∀ i, IdentDistrib (Pn i) (Pn 0) μ μ) (dPs : ∀ i, IdentDistrib (Ps i) (Ps 0) μ μ)
    (eDn : μ[Dn 0] = M.EDn) (eDs : μ[Ds 0] = M.EDs) (ePn : μ[Pn 0] = M.EPn)
    (ePs : μ[Ps 0] = M.EPs) :
    ∀ᵐ ω ∂μ, Tendsto (fun m : ℕ => alphaHat (∑ i ∈ range m, Dn i ω) (∑ i ∈ range m, Ds i ω)
      (∑ i ∈ range m, Pn i ω) (∑ i ∈ range m, Ps i ω)) atTop (𝓝 M.alpha) := by
  have hDpos : 0 < M.EDn := by
    have := M.Ln_pos; have := M.f₀_pos; have := M.divRate_pos; have := M.A_nonneg
    unfold EDn; positivity
  have hPpos : 0 < M.EPs := by
    have := M.Ls_pos; have := M.polyRate_pos
    unfold EPs; positivity
  filter_upwards [strong_law_ae_real Dn hDn iDn dDn, strong_law_ae_real Ds hDs iDs dDs,
    strong_law_ae_real Pn hPn iPn dPn, strong_law_ae_real Ps hPs iPs dPs] with ω h1 h2 h3 h4
  rw [eDn] at h1
  rw [eDs] at h2
  rw [ePn] at h3
  rw [ePs] at h4
  have hlim : Tendsto (fun m : ℕ => alphaHat ((∑ i ∈ range m, Dn i ω) / m)
      ((∑ i ∈ range m, Ds i ω) / m) ((∑ i ∈ range m, Pn i ω) / m)
      ((∑ i ∈ range m, Ps i ω) / m)) atTop (𝓝 M.alpha) := by
    rw [← M.alphaHat_expected]
    exact ((h2.mul h3).div (h1.mul h4) (mul_pos hDpos hPpos).ne').const_sub 1
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : ((m : ℝ) * m) ≠ 0 := by positivity
  simp only [alphaHat]
  rw [div_mul_div_comm, div_mul_div_comm, div_div_div_cancel_right₀ hm']

end MKModel

end MathlibExt.Biology.PopulationGenetics.McDonaldKreitman
