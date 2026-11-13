/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.Sharpness.SharpnessBeta
import Code.Sharpness.PercoItems

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}








theorem bfp_pBeta_hasDerivAt (J β : ℝ) :
    HasDerivAt (pBeta J) (J * Real.exp (-β * J)) β := by
  unfold pBeta
  have h1 : HasDerivAt (fun b => -b * J) (-J) β := by
    simpa using ((hasDerivAt_id β).neg.mul_const J)
  have h2 : HasDerivAt (fun b => Real.exp (-b * J)) (Real.exp (-β * J) * (-J)) β :=
    (Real.hasDerivAt_exp _).comp β h1
  have h3 : HasDerivAt (fun b => 1 - Real.exp (-b * J)) (-(Real.exp (-β * J) * (-J))) β := by
    simpa using (hasDerivAt_const β (1 : ℝ)).sub h2
  convert h3 using 1; ring





theorem bfp_pBeta_le_betaJ (J β : ℝ) : pBeta J β ≤ β * J := by
  unfold pBeta
  have := Real.add_one_le_exp (-β * J)
  nlinarith [this]






























theorem bfp_meanfield_perco_beta (J β m fp' : ℝ) (f : ℝ → ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (hp0 : 0 < pBeta J β) (hp1 : pBeta J β < 1) (hm : 0 ≤ m) (hf1 : f (pBeta J β) ≤ 1)
    (hf : HasDerivAt f fp' (pBeta J β))
    (hpform : (1 / (pBeta J β * (1 - pBeta J β))) * m * (1 - f (pBeta J β)) ≤ fp') :
    HasDerivAt (fun b => f (pBeta J b)) (fp' * (J * Real.exp (-β * J))) β
      ∧ (1 / β) * m * (1 - f (pBeta J β)) ≤ fp' * (J * Real.exp (-β * J)) := by
  set p := pBeta J β with hp_def
  
  have hF : HasDerivAt (fun b => f (pBeta J b))
      (fp' * (J * Real.exp (-β * J))) β := by
    have := hf.comp β (bfp_pBeta_hasDerivAt J β)
    simpa [Function.comp] using this
  refine ⟨hF, ?_⟩
  
  have hexp_eq : Real.exp (-β * J) = 1 - p := by rw [hp_def]; unfold pBeta; ring
  rw [hexp_eq]
  have h1mp : 0 < 1 - p := by linarith
  have hJfac : 0 < J * (1 - p) := mul_pos hJ h1mp
  
  have step1 : (1 / (p * (1 - p))) * m * (1 - f p) * (J * (1 - p))
      ≤ fp' * (J * (1 - p)) := mul_le_mul_of_nonneg_right hpform (le_of_lt hJfac)
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1mpne : (1 - p) ≠ 0 := ne_of_gt h1mp
  
  have hsimp : (1 / (p * (1 - p))) * m * (1 - f p) * (J * (1 - p))
      = (J / p) * m * (1 - f p) := by field_simp
  rw [hsimp] at step1
  
  have hinvle : 1 / β ≤ J / p := by
    rw [div_le_div_iff₀ hβ hp0]
    have := bfp_pBeta_le_betaJ J β; rw [← hp_def] at this; nlinarith [this]
  have hmnn : 0 ≤ m * (1 - f p) := mul_nonneg hm (by linarith)
  have step0 : (1 / β) * m * (1 - f p) ≤ (J / p) * m * (1 - f p) := by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hinvle hmnn
  linarith [step0, step1]



















theorem bfp_meanfield_perco_beta_crossProb {q : ℝ≥0} (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (hq1 : (q : ℝ) < 1) (htpc0 : 0 < (tildePc d : ℝ)) (n : ℕ)
    (ht : pBeta J β ∈ Ioo (tildePc d : ℝ) (q : ℝ)) :
    HasDerivAt (fun b => crossProbReal d (n + 1) (pBeta J b))
        (deriv (crossPoly d n) (pBeta J β) * (J * Real.exp (-β * J))) β
      ∧ (1 / β) * (1 - crossProbReal d (n + 1) (pBeta J β))
          ≤ deriv (crossPoly d n) (pBeta J β) * (J * Real.exp (-β * J)) := by
  set p := pBeta J β with hp_def
  obtain ⟨htlo, hthi⟩ := ht
  have hp0 : 0 < p := lt_trans htpc0 htlo
  have hp1 : p < 1 := lt_trans hthi hq1
  
  have hf : HasDerivAt (crossProbReal d (n + 1)) (deriv (crossPoly d n) p) p :=
    hasDerivAt_crossProbReal n hp0 hp1
  have hpform := dct_diffineq_crossProbReal hq1 htpc0 n ⟨htlo, hthi⟩
  rw [ge_iff_le] at hpform
  have hf1 : crossProbReal d (n + 1) p ≤ 1 := crossProbReal_le_one d (n + 1) p
  
  have hbr := bfp_meanfield_perco_beta J β 1 (deriv (crossPoly d n) p) (crossProbReal d (n + 1))
    hJ hβ hp0 hp1 (by norm_num) hf1 hf (by simpa using hpform)
  exact ⟨hbr.1, by simpa using hbr.2⟩




























theorem bfp_integrate_perco_beta (J β βc : ℝ) (f : ℝ → ℝ) (hJ : 0 < J)
    (hβc : 0 < βc) (hββc : βc < β)
    (hdiff : ∀ q ∈ Ico (pBeta J βc) 1, DifferentiableAt ℝ f q)
    (hineq : ∀ q ∈ Ioo (pBeta J βc) 1, (1 / (q * (1 - q))) * (1 - f q) ≤ deriv f q)
    (hf0 : 0 ≤ f (pBeta J βc)) :
    (β - βc) / β ≤ f (pBeta J β) := by
  set p₀ := pBeta J βc with hp₀
  set p := pBeta J β with hp
  
  have hp₀0 : 0 < p₀ := by
    rw [hp₀]; unfold pBeta
    have : Real.exp (-βc * J) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hp₀1 : p₀ < 1 := pBeta_lt_one J βc
  have hp₀p : p₀ ≤ p := le_of_lt (pBeta_strictMono hJ hββc)
  have hp1 : p < 1 := pBeta_lt_one J β
  
  have hpf := profile_ge_of_diffineq p₀ hp₀0 hp₀1 f hdiff hineq hf0 hp₀p hp1
  
  exact pform_le_betaform J β βc p₀ (f p) hJ hβc hββc hp₀0 hp₀1
    (by rw [hp₀]; unfold pBeta; ring) hpf


















theorem bfp_integrate_perco_beta_named {J β : ℝ} (f : ℝ → ℝ) (hJ : 0 < J) (hd : 0 < d)
    (htc1 : (tildePc d : ℝ) < 1) (hβ : betaTildeC d J < β)
    (hdiff : ∀ q ∈ Ico (tildePc d : ℝ) 1, DifferentiableAt ℝ f q)
    (hineq : ∀ q ∈ Ioo (tildePc d : ℝ) 1, (1 / (q * (1 - q))) * (1 - f q) ≤ deriv f q)
    (hf0 : 0 ≤ f (tildePc d : ℝ)) :
    (β - betaTildeC d J) / β ≤ f (pBeta J β) := by
  set βc := betaTildeC d J with hβc_def
  have hβc_pos : 0 < βc := betaTildeC_pos hJ hd htc1
  
  have hval : pBeta J βc = (tildePc d : ℝ) := by
    rw [hβc_def]; exact pBeta_betaTildeC hJ htc1
  
  refine bfp_integrate_perco_beta J β βc f hJ hβc_pos hβ ?_ ?_ ?_
  · rw [hval]; exact hdiff
  · rw [hval]; exact hineq
  · rw [hval]; exact hf0

end Sharpness

end StatMech
