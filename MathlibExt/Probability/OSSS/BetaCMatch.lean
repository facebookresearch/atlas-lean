/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.OSSS.BetaThresholdBound

/-!
# Identifying the critical point with the threshold `β₁`

If the limit quantity `Θ(β)` vanishes below `β₁` (because it is bounded by `M e^{-n δ / Q}` for
every `n`) and is at least `β - β₁` above `β₁` (the mean-field bound), then
`β_c := sup {β : Θ(β) = 0} = β₁`. Below `β_c` the finite-volume quantities then decay
exponentially.

## Main definitions

* `StatMech.OSSS.BetaCMatch.bcm_subcriticalSet`: `{β : Θ(β) = 0}`.

## Main results

* `StatMech.OSSS.BetaCMatch.bcm_betaC_eq_threshold`: `Θ = 0` below `β₁` and `Θ > 0` above it
  give `sup {Θ = 0} = β₁`.
* `StatMech.OSSS.BetaCMatch.bcm_betaC_eq_beta1`: the same from the decay and mean-field
  hypotheses.
* `StatMech.OSSS.BetaCMatch.bcm_fk_q2_subcritical_decay_of_betaC`: exponential decay of
  `θ_n(β - 2δ)` for `β < β_c`.

## References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and
  Potts models via decision trees*, Ann. of Math. 189 (2019), 75–99.
-/

@[expose] public section

open scoped BigOperators
open Real Filter Topology Set Finset

namespace StatMech
namespace OSSS.BetaCMatch

open StatMech.OSSS.IntegrationSubcritical
open StatMech.OSSS.BetaThresholdBound

/-- `M e^{-n δ / Q} → 0` for `Q, δ > 0`. -/
theorem bcm_expBound_tendsto_zero (M Q δ : ℝ) (hQ : 0 < Q) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => M * Real.exp (-(((n : ℝ) / Q) * δ))) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = M * 0 by ring]
  apply Tendsto.const_mul
  apply Real.tendsto_exp_atBot.comp
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) / Q) * δ) atTop atTop := by
    apply Filter.Tendsto.atTop_mul_const hδ
    apply Filter.Tendsto.atTop_div_const hQ
    exact tendsto_natCast_atTop_atTop
  exact tendsto_neg_atBot_iff.mpr h1

/-- A nonnegative number bounded by `M e^{-n δ / Q}` for all `n` is `0`. -/
theorem bcm_theta_zero_of_decay (θ M Q δ : ℝ) (hQ : 0 < Q) (hδ : 0 < δ)
    (hθnn : 0 ≤ θ)
    (hbound : ∀ n : ℕ, θ ≤ M * Real.exp (-(((n : ℝ) / Q) * δ))) :
    θ = 0 := by
  have hb0 := bcm_expBound_tendsto_zero M Q δ hQ hδ
  have hconst : Tendsto (fun _ : ℕ => θ) atTop (𝓝 θ) := tendsto_const_nhds
  have hle : θ ≤ 0 := le_of_tendsto_of_tendsto hconst hb0 (Eventually.of_forall hbound)
  linarith

/-- `θ ≥ β - β₁ > 0` gives `θ > 0`. -/
theorem bcm_theta_pos_of_meanField (θ f β₁ β : ℝ)
    (hθf : θ = f) (hmf : β - β₁ ≤ f) (hlt : β₁ < β) : 0 < θ := by
  rw [hθf]
  have : 0 < β - β₁ := by linarith
  linarith

/-- The set `{β : Θ(β) = 0}`. -/
def bcm_subcriticalSet (θ : ℝ → ℝ) : Set ℝ := {β | θ β = 0}

/-- If `Θ > 0` above `β₁`, every `β` with `Θ(β) = 0` is at most `β₁`. -/
theorem bcm_subcriticalSet_le (θ : ℝ → ℝ) (β₁ : ℝ)
    (hP2 : ∀ β, β₁ < β → 0 < θ β) :
    ∀ β ∈ bcm_subcriticalSet θ, β ≤ β₁ := by
  intro β hβ
  by_contra hlt
  rw [not_le] at hlt
  have hpos := hP2 β hlt
  rw [bcm_subcriticalSet, mem_ofPred_eq] at hβ
  rw [hβ] at hpos
  exact lt_irrefl 0 hpos

/-- If `Θ = 0` below `β₁`, then `(-∞, β₁) ⊆ {Θ = 0}`. -/
theorem bcm_Iio_subset_subcritical (θ : ℝ → ℝ) (β₁ : ℝ)
    (hP1 : ∀ β, β < β₁ → θ β = 0) :
    Iio β₁ ⊆ bcm_subcriticalSet θ := by
  intro β hβ
  rw [bcm_subcriticalSet, mem_ofPred_eq]
  exact hP1 β hβ

/-- `Θ = 0` on `(-∞, β₁)` and `Θ > 0` on `(β₁, ∞)` give `sup {Θ = 0} = β₁`. -/
theorem bcm_betaC_eq_threshold (θ : ℝ → ℝ) (β₁ : ℝ)
    (hP1 : ∀ β, β < β₁ → θ β = 0)
    (hP2 : ∀ β, β₁ < β → 0 < θ β) :
    sSup (bcm_subcriticalSet θ) = β₁ := by
  have hub := bcm_subcriticalSet_le θ β₁ hP2
  have hbdd : BddAbove (bcm_subcriticalSet θ) := ⟨β₁, hub⟩
  have hsub := bcm_Iio_subset_subcritical θ β₁ hP1
  have hne : (bcm_subcriticalSet θ).Nonempty := ⟨β₁ - 1, hsub (by simp)⟩
  apply le_antisymm
  · exact csSup_le hne hub
  · have h1 : sSup (Iio β₁) = β₁ := csSup_Iio
    rw [← h1]
    exact csSup_le_csSup hbdd nonempty_Iio hsub

/-- `β_c = β₁`, given `hdecay` (below `β₁`, `0 ≤ Θ(β) ≤ M e^{-n δ / Q}` for every `n`, so `Θ(β) =
0`) and `hmf` (above `β₁`, `Θ(β) ≥ β - β₁`). Both are hypotheses: they are the conclusions of the
subcritical and mean-field halves applied to the limit quantity `Θ`, which this file does not
connect to `θ_n`. -/
theorem bcm_betaC_eq_beta1 (θ : ℕ → ℝ → ℝ) (Θ : ℝ → ℝ) (M : ℝ)
    (Qf δf : ℝ → ℝ)
    (hdecay : ∀ β, β < beta1 (fun b n => Sig θ n b) →
      0 ≤ Θ β ∧ 0 < Qf β ∧ 0 < δf β ∧
        ∀ n : ℕ, Θ β ≤ M * Real.exp (-(((n : ℝ) / Qf β) * δf β)))
    (hmf : ∀ β, beta1 (fun b n => Sig θ n b) < β →
      β - beta1 (fun b n => Sig θ n b) ≤ Θ β) :
    sSup (bcm_subcriticalSet Θ) = beta1 (fun b n => Sig θ n b) := by
  set β₁ := beta1 (fun b n => Sig θ n b) with hβ₁
  have hP1 : ∀ β, β < β₁ → Θ β = 0 := by
    intro β hβ
    obtain ⟨hΘnn, hQ, hδ, hbound⟩ := hdecay β hβ
    exact bcm_theta_zero_of_decay (Θ β) M (Qf β) (δf β) hQ hδ hΘnn hbound
  have hP2 : ∀ β, β₁ < β → 0 < Θ β := by
    intro β hβ
    exact bcm_theta_pos_of_meanField (Θ β) (Θ β) β₁ β rfl (hmf β hβ) hβ
  exact bcm_betaC_eq_threshold Θ β₁ hP1 hP2

/-- Exponential decay below `β_c`: if `β < sup {Θ = 0}`, then `θ_n(β - 2δ) ≤ M e^{-n δ / Q}`.
Conditional on `hdiff` (the OSSS differential inequality), `hθmono`, and `hdecay`, `hmf` (which
identify `β_c` with `β₁`). -/
theorem bcm_fk_q2_subcritical_decay_of_betaC (θ θ' : ℕ → ℝ → ℝ) (Θ : ℝ → ℝ)
    (δ β M : ℝ) (Qf δf : ℝ → ℝ)
    (hδ : 0 < δ) (hMnn : 0 ≤ M)
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
    (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
    (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
    (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → θ k y ≤ θ k x)
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
    (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / Sig θ n x) * θ n x ≤ θ' n x)
    (hSgβpos : ∀ n : ℕ, 2 ≤ n → 0 < Sig θ n β)
    (hθ1 : ∀ k, θ k β ≤ 1)
    (hbddSet : BddBelow (thresholdSet (fun b n => Sig θ n b)))
    (hdecay : ∀ b, b < beta1 (fun b n => Sig θ n b) →
      0 ≤ Θ b ∧ 0 < Qf b ∧ 0 < δf b ∧
        ∀ n : ℕ, Θ b ≤ M * Real.exp (-(((n : ℝ) / Qf b) * δf b)))
    (hmf : ∀ b, beta1 (fun b n => Sig θ n b) < b →
      b - beta1 (fun b n => Sig θ n b) ≤ Θ b)
    (hβc : β < sSup (bcm_subcriticalSet Θ)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
  have hmatch := bcm_betaC_eq_beta1 θ Θ M Qf δf hdecay hmf
  rw [hmatch] at hβc
  exact btb_fk_q2_subcritical_decay_of_threshold' θ θ' δ β M hδ hMnn hd hθnn hθM hθmono
    hSpos hdiff hSgβpos hθ1 hbddSet hβc

end OSSS.BetaCMatch
end StatMech
