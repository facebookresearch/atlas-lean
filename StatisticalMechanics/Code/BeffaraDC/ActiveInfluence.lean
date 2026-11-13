/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib
import Code.BeffaraDC.ActiveRussoHamming
import Code.FK.ComparisonHolley

open scoped BigOperators

namespace StatMech.BeffaraDC

open Finset
open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem activeWeight_open_pair {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (e : G.edgeSet) (ω : ConfigSpace G.edgeSet) :
    p * activeWeight G (fun _ => p) q (setClosed e ω) ≤
      q * (1 - p) * activeWeight G (fun _ => p) q (setOpen e ω) := by
  unfold activeWeight fkWeightW
  rw [extendActive_setOpen, extendActive_setClosed,
    edgeProductW_setOpen, edgeProductW_setClosed]
  let R := ∏ a ∈ G.edgeFinset.erase e.1,
    (if extendActive G ω a then p else 1 - p)
  have hR : 0 ≤ R := by
    unfold R
    apply Finset.prod_nonneg
    intro a _
    split
    · exact hp.le
    · linarith
  have hk := numClusters_setClosed_le_setOpen_succ G e.1 (extendActive G ω)
  have hpow : q ^ numClusters G (setClosed e.1 (extendActive G ω)) ≤
      q * q ^ numClusters G (setOpen e.1 (extendActive G ω)) := by
    calc
      q ^ numClusters G (setClosed e.1 (extendActive G ω)) ≤
          q ^ (numClusters G (setOpen e.1 (extendActive G ω)) + 1) :=
        pow_le_pow_right₀ hq hk
      _ = q * q ^ numClusters G (setOpen e.1 (extendActive G ω)) := by
        rw [pow_succ]
        ring
  have hcoef : 0 ≤ p * (1 - p) * R := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hcoef]

lemma openMarginal_lower_of_open_pair {E : Type*} [Fintype E] [DecidableEq E]
    (μ : ConfigSpace E → ℝ) (hμ1 : ∑ ω, μ ω = 1) (e : E)
    {p q : ℝ} (hden : 0 < p + q * (1 - p))
    (hpair : ∀ ψ, p * μ (setClosed e ψ) ≤
      q * (1 - p) * μ (setOpen e ψ)) :
    p / (p + q * (1 - p)) ≤ openMarginal μ e := by
  let S := Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false)
  have hs := Finset.sum_le_sum fun ψ (_ : ψ ∈ S) => hpair ψ
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← openMarginal_eq_closedFiber] at hs
  have hone := activeClosedFiber_pairMass_eq_one μ hμ1 e
  change (∑ ψ ∈ S, (μ (setOpen e ψ) + μ (setClosed e ψ))) = 1 at hone
  rw [Finset.sum_add_distrib, ← openMarginal_eq_closedFiber] at hone
  have hclosed : (∑ ψ ∈ S, μ (setClosed e ψ)) = 1 - openMarginal μ e := by
    linarith
  rw [hclosed] at hs
  rw [div_le_iff₀ hden]
  nlinarith [hs]

theorem active_reducedDensity_le_openMarginal {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (e : G.edgeSet) :
    reducedDensity p q ≤ openMarginal (activeProb G (fun _ => p) q) e := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hden : 0 < p + q * (1 - p) := add_pos hp (mul_pos hq0 (by linarith))
  apply openMarginal_lower_of_open_pair _
    (activeProb_sum_eq_one G (fun _ => hp) (fun _ => hp1) hq0) e hden
  intro ψ
  unfold activeProb
  have hZ := activeZ_pos G (fun _ => hp) (fun _ => hp1) hq0
  rw [show p * (activeWeight G (fun _ => p) q (setClosed e ψ) /
      activeZ G (fun _ => p) q) =
      (p * activeWeight G (fun _ => p) q (setClosed e ψ)) /
        activeZ G (fun _ => p) q by ring]
  rw [show q * (1 - p) * (activeWeight G (fun _ => p) q (setOpen e ψ) /
      activeZ G (fun _ => p) q) =
      (q * (1 - p) * activeWeight G (fun _ => p) q (setOpen e ψ)) /
        activeZ G (fun _ => p) q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2
    (activeWeight_open_pair G hp hp1 hq e ψ)


noncomputable def activeInfluence (p q : ℝ)
    (A : Set (ConfigSpace G.edgeSet)) (e : G.edgeSet) : ℝ :=
  let m := openMarginal (activeProb G (fun _ => p) q) e
  activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ))
    (OSSS.Lindeberg.coord e) / (m * (1 - m))

theorem activeInfluence_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A)
    (e : G.edgeSet) : 0 ≤ activeInfluence G p q A e := by
  have hcov := active_fkg_cov G hp hp1 hq hA.indicator_monotone
    (OSSS.Lindeberg.coord_mono e)
  unfold activeInfluence activeCov at *
  have hm0 : 0 < openMarginal (activeProb G (fun _ => p) q) e := by
    have hr := active_reducedDensity_le_openMarginal G hp hp1 hq e
    exact lt_of_lt_of_le (reducedDensity_mem_Ioo hp hp1 hq).1 hr
  have hm1 : openMarginal (activeProb G (fun _ => p) q) e < 1 :=
    (active_openMarginal_le_param G (fun _ => hp) (fun _ => hp1) hq e).trans_lt hp1
  exact div_nonneg (by linarith) (mul_nonneg hm0.le (by linarith))

theorem activeCov_eq_marginal_mul_influence {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace G.edgeSet)) (e : G.edgeSet) :
    activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ))
        (OSSS.Lindeberg.coord e) =
      openMarginal (activeProb G (fun _ => p) q) e *
        (1 - openMarginal (activeProb G (fun _ => p) q) e) *
          activeInfluence G p q A e := by
  have hm0 : 0 < openMarginal (activeProb G (fun _ => p) q) e := by
    exact lt_of_lt_of_le (reducedDensity_mem_Ioo hp hp1 hq).1
      (active_reducedDensity_le_openMarginal G hp hp1 hq e)
  have hm1 : openMarginal (activeProb G (fun _ => p) q) e < 1 :=
    (active_openMarginal_le_param G (fun _ => hp) (fun _ => hp1) hq e).trans_lt hp1
  unfold activeInfluence
  field_simp [hm0.ne', (sub_pos.mpr hm1).ne']



theorem active_deriv_ge_total_influence {p q ε : ℝ} (hε : 0 < ε)
    (hp0 : ε ≤ p) (hp1 : p ≤ 1 - ε) (hq : 1 ≤ q)
    (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A) :
    (ε ^ 2 / q) * (∑ e : G.edgeSet, activeInfluence G p q A e) ≤
      deriv (fun x => activeProbOf G (fun _ => x) q A) p := by
  have hp : 0 < p := hε.trans_le hp0
  have hp' : p < 1 := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hden : 0 < p + q * (1 - p) := add_pos hp (mul_pos hq0 (by linarith))
  have hdenle : p + q * (1 - p) ≤ q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) hp.le]
  have hred : ε / q ≤ reducedDensity p q := by
    rw [reducedDensity, div_le_div_iff₀ hq0 hden]
    exact mul_le_mul hp0 hdenle hden.le hp.le
  have hterm : ∀ e : G.edgeSet,
      ε ^ 2 / q * activeInfluence G p q A e ≤
        activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ))
          (OSSS.Lindeberg.coord e) := by
    intro e
    have hmlo : ε / q ≤ openMarginal (activeProb G (fun _ => p) q) e :=
      hred.trans (active_reducedDensity_le_openMarginal G hp hp' hq e)
    have hmhi := active_openMarginal_le_param G (fun _ => hp) (fun _ => hp') hq e
    have hclosed : ε ≤ 1 - openMarginal (activeProb G (fun _ => p) q) e := by
      linarith
    have hprod : ε ^ 2 / q ≤
        openMarginal (activeProb G (fun _ => p) q) e *
          (1 - openMarginal (activeProb G (fun _ => p) q) e) := by
      calc
        ε ^ 2 / q = (ε / q) * ε := by ring
        _ ≤ openMarginal (activeProb G (fun _ => p) q) e *
            (1 - openMarginal (activeProb G (fun _ => p) q) e) :=
          mul_le_mul hmlo hclosed hε.le
            ((div_nonneg hε.le hq0.le).trans hmlo)
    have hI := activeInfluence_nonneg G hp hp' hq A hA e
    rw [activeCov_eq_marginal_mul_influence G hp hp' hq A e]
    exact mul_le_mul_of_nonneg_right hprod hI
  have hsum : (ε ^ 2 / q) * (∑ e : G.edgeSet, activeInfluence G p q A e) ≤
      ∑ e : G.edgeSet, activeCov G (fun _ => p) q
        (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => hterm e
  have hcovnonneg : 0 ≤ ∑ e : G.edgeSet, activeCov G (fun _ => p) q
      (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e) := by
    exact Finset.sum_nonneg fun e _ => by
      have h := active_fkg_cov G hp hp' hq hA.indicator_monotone
        (OSSS.Lindeberg.coord_mono e)
      unfold activeCov
      linarith
  rw [(hasDerivAt_activeProbOf_p G hp hp' hq0 A).deriv]
  refine hsum.trans ?_
  have hpden : 0 < p * (1 - p) := mul_pos hp (by linarith)
  rw [le_div_iff₀ hpden]
  have hpden_le : p * (1 - p) ≤ 1 := by nlinarith [mul_nonneg hp.le (by linarith)]
  nlinarith

end StatMech.BeffaraDC
