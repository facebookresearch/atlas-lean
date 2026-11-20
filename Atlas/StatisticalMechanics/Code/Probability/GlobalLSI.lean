/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Code.Probability.EntropySubadd
import Code.Probability.TwoPointLSI

open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {n : ℕ}






noncomputable def gls_deriv (f : ConfigSpace (Fin n) → ℝ) (e : Fin n) (ω : ConfigSpace (Fin n)) : ℝ :=
  f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω)












theorem gls_entCoord_eq_tpl (p : ℝ) (g : ConfigSpace (Fin n) → ℝ) (e : Fin n)
    (ω : ConfigSpace (Fin n)) :
    esd_entCoord p g e ω
      = tpl_ent (1 - p) (g (StatMech.setOpen e ω)) (g (StatMech.setClosed e ω)) := by
  unfold esd_entCoord tpl_ent OSSS.condMean esd_Phi OSSS.bernoulliWeight
  simp only [if_true, Bool.false_eq_true, if_false]
  ring_nf










theorem gls_entCoord_le_deriv_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : ConfigSpace (Fin n) → ℝ) (e : Fin n) (ω : ConfigSpace (Fin n)) :
    esd_entCoord p (fun ω => (f ω) ^ 2) e ω ≤ (gls_deriv f e ω) ^ 2 := by
  rw [gls_entCoord_eq_tpl]
  unfold gls_deriv
  exact tpl_lsi (by linarith) (by linarith) (f (StatMech.setOpen e ω)) (f (StatMech.setClosed e ω))
















theorem gls_globalLSI {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f : ConfigSpace (Fin n) → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2)
      ≤ ∑ e : Fin n, OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (gls_deriv f e ω) ^ 2) := by
  
  have hsub := esd_subadditivity hp0 hp1 (fun ω => (f ω) ^ 2) (fun ω => sq_nonneg (f ω))
  refine hsub.trans ?_
  
  apply Finset.sum_le_sum
  intro e _
  apply OSSS.expect_mono (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le)
  
  intro ω
  exact gls_entCoord_le_deriv_sq hp0 hp1 f e ω










theorem gls_globalLSI_weighted {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f : ConfigSpace (Fin n) → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2)
      ≤ (1 / (p * (1 - p))) * ∑ e : Fin n,
          OSSS.expect (OSSS.bernoulliWeight p) (fun ω => p * (1 - p) * (gls_deriv f e ω) ^ 2) := by
  have hppos : 0 < p * (1 - p) := by nlinarith
  refine (gls_globalLSI hp0 hp1 f).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [OSSS.expect_const_mul, ← mul_assoc, one_div, inv_mul_cancel₀ hppos.ne', one_mul]

end StatMech.Probability
