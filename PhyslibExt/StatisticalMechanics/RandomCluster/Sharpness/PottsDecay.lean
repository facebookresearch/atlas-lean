/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Assembly
public import MathlibExt.Probability.OSSS.BetaCMatch

/-!
# Sharpness package for the q = 2 random-cluster model

The `q = 2` differential inequality with Russo prefactor at least `4`, exponential decay below the
threshold, the mean-field bound, and the identification of the threshold.

## i. Overview

`ofa_russoPrefactor_ge_four` gives `russoPrefactor p ≥ 4`. `ofa_fk_q2_differential_inequality` and
`ofa_summary` are conditional on `hbridge` (discharged for connection events in
`HorizontalBridgeDecay`) and `hθub`. `ofa_fk_q2_sharpness` also takes the supplied mean-field limits
and the hypotheses `hP1`, `hP2` on `Θ`. `hP2` (the backbone chain rule, P2) is always an assumption.
The third conjunct `sSup (bcm_subcriticalSet Θ) = β₁` follows from `hP1` and `hP2` alone.

## ii. Key results

- `ofa_fk_q2_sharpness`: decay, mean-field bound and threshold identification, conditional on
  `hbridge`, `hθub`, the mean-field limits, `hP1` and `hP2`.
- `ofa_summary`: Poincaré bound and decay, conditional on `hbridge` and `hθub`.

## iii. Table of contents

- A. The q = 2 sharpness package

## iv. References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open Finset Real Set Filter Topology


namespace StatMech
namespace OSSS
namespace OSFKAssemblyClose

open StatMech.OSSS.Lindeberg
open StatMech.OSSS.SharpnessFK
open StatMech.OSSS.Integration
open StatMech.OSSS.BetaCMatch
open StatMech.FK
open MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A. The q = 2 sharpness package -/

lemma ofa_russoPrefactor_ge_four {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (4 : ℝ) ≤ russoPrefactor p := by
  rw [russoPrefactor, le_div_iff₀ (mul_pos hp (by linarith))]
  nlinarith [sq_nonneg (p - 1 / 2)]

lemma ofa_fk_q2_differential_inequality (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (hbridge : ∑ e, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)) :
    russoPrefactor p * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A))
      ≤ deriv (fun p => fkProbOf G p 2 A) p :=
  fk_differential_inequality G hp hp1 (by norm_num : (1 : ℝ) ≤ 2) A hA hbridge

/-- Decay, mean-field bound and threshold identification, conditional on `hbridge`, `hθub`, the
  mean-field limits, `hP1` and `hP2`. -/
theorem ofa_fk_q2_sharpness (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hbridge : ∀ x ∈ Icc a b,
        ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ)
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hboundMF : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β')
    (Θ : ℝ → ℝ) (β₁ : ℝ)
    (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
    (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
    (fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a))))
      ∧ (β - β' ≤ fβ - fβ')
      ∧ sSup (bcm_subcriticalSet Θ) = β₁ :=
  ⟨StatMech.OSSS.fk_q2_crossing_decay_poincare G A hA a b κ hab ha0 hb1 hκ hbridge hθub,
   StatMech.OSSS.Integration.meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hboundMF,
   StatMech.OSSS.BetaCMatch.bcm_betaC_eq_threshold Θ β₁ hP1 hP2⟩

lemma ofa_summary (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hbridge : ∀ x ∈ Icc a b,
        ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ) :
    (fkProbOf G a 2 A * (1 - fkProbOf G a 2 A)
        ≤ ∑ e, fkCov G a 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    ∧ (fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a)))) :=
  ⟨StatMech.OSSS.fk_poincare_indicator G ha0 (by linarith) (by norm_num : (1 : ℝ) ≤ 2) A hA,
   StatMech.OSSS.fk_q2_crossing_decay_poincare G A hA a b κ hab ha0 hb1 hκ hbridge hθub⟩

end OSFKAssemblyClose
end OSSS
end StatMech
