/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.OSSS.IntegrationSubcriticalAssembly
import Code.OSSS.FKSharpDiffIneq

open scoped BigOperators
open Real Filter Topology Set Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech
namespace OSSS.BetaThresholdBound

open StatMech.OSSS.IntegrationSubcritical








noncomputable def logRatio (Sg : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (Sg n) / Real.log (n : ℝ)



def thresholdSet (Sgf : ℝ → ℕ → ℝ) : Set ℝ :=
  {β | 1 ≤ Filter.limsup (logRatio (Sgf β)) atTop}



noncomputable def beta1 (Sgf : ℝ → ℕ → ℝ) : ℝ := sInf (thresholdSet Sgf)










theorem btb_limsup_lt_one_of_lt_threshold (Sgf : ℝ → ℕ → ℝ) (β : ℝ)
    (hbdd : BddBelow (thresholdSet Sgf)) (hlt : β < beta1 Sgf) :
    Filter.limsup (logRatio (Sgf β)) atTop < 1 := by
  by_contra hge
  rw [not_lt] at hge
  
  have hmem : β ∈ thresholdSet Sgf := hge
  have := csInf_le hbdd hmem
  unfold beta1 at hlt
  linarith









theorem btb_eventually_ratio_lt (u : ℕ → ℝ)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop u)
    (h : Filter.limsup u atTop < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n in atTop, u n < 1 - α := by
  refine ⟨(1 - Filter.limsup u atTop) / 2, by linarith, ?_⟩
  apply Filter.eventually_lt_of_limsup_lt _ hbdd
  linarith









theorem btb_poly_bound_of_ratio_lt (n : ℕ) (S α : ℝ) (hn : 2 ≤ n) (hS : 0 < S)
    (h : Real.log S / Real.log (n : ℝ) < 1 - α) :
    S < (n : ℝ) ^ (1 - α) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlt : Real.log S < (1 - α) * Real.log (n : ℝ) := by
    rw [div_lt_iff₀ hlogn] at h; linarith
  have hpow : Real.log ((n : ℝ) ^ (1 - α)) = (1 - α) * Real.log (n : ℝ) :=
    Real.log_rpow hnpos _
  rw [← hpow] at hlt
  have hrpos : (0 : ℝ) < (n : ℝ) ^ (1 - α) := by positivity
  exact (Real.log_lt_log_iff hS hrpos).mp hlt











theorem btb_poly_bound_of_limsup_lt (Sg : ℕ → ℝ)
    (hSpos : ∀ n, 2 ≤ n → 0 < Sg n)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio Sg))
    (h : Filter.limsup (logRatio Sg) atTop < 1) :
    ∃ (N : ℕ) (α : ℝ), 0 < α ∧ ∀ n, N ≤ n → Sg n ≤ (n : ℝ) ^ (1 - α) := by
  obtain ⟨α, hα, hev⟩ := btb_eventually_ratio_lt (logRatio Sg) hbdd h
  have hcomb : ∀ᶠ n in atTop, Sg n ≤ (n : ℝ) ^ (1 - α) := by
    filter_upwards [hev, eventually_ge_atTop 2] with n hun hn2
    exact le_of_lt (btb_poly_bound_of_ratio_lt n (Sg n) α hn2 (hSpos n hn2) hun)
  rw [eventually_atTop] at hcomb
  obtain ⟨N, hN⟩ := hcomb
  exact ⟨N, α, hα, hN⟩






theorem btb_poly_bound_of_lt_threshold (Sgf : ℝ → ℕ → ℝ) (β : ℝ)
    (hbddSet : BddBelow (thresholdSet Sgf))
    (hSpos : ∀ n, 2 ≤ n → 0 < Sgf β n)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio (Sgf β)))
    (hlt : β < beta1 Sgf) :
    ∃ (N : ℕ) (α : ℝ), 0 < α ∧ ∀ n, N ≤ n → Sgf β n ≤ (n : ℝ) ^ (1 - α) :=
  btb_poly_bound_of_limsup_lt (Sgf β) hSpos hbdd
    (btb_limsup_lt_one_of_lt_threshold Sgf β hbddSet hlt)













theorem btb_bddAbove_ratio_of_linear (Sg : ℕ → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hSpos : ∀ n, 2 ≤ n → 0 < Sg n)
    (hbound : ∀ n, Sg n ≤ C * (n : ℝ)) :
    IsBoundedUnder (· ≤ ·) atTop (logRatio Sg) := by
  apply Filter.isBoundedUnder_of_eventually_le (a := Real.log C / Real.log 2 + 1)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2n : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
  have hCpos : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hSn : Real.log (Sg n) ≤ Real.log C + Real.log (n : ℝ) := by
    have h1 : Real.log (Sg n) ≤ Real.log (C * (n : ℝ)) :=
      Real.log_le_log (hSpos n hn) (hbound n)
    rwa [Real.log_mul (ne_of_gt hCpos) (by positivity)] at h1
  unfold logRatio
  rw [div_le_iff₀ hlogn]
  have hkey : Real.log C ≤ Real.log C / Real.log 2 * Real.log (n : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith [hlogC, hlog2, hlog2n]
  nlinarith [hSn, hkey, hlogn]





theorem btb_Sig_le_card (f : ℕ → ℝ → ℝ) (β : ℝ) (hf : ∀ k, f k β ≤ 1) (n : ℕ) :
    Sig f n β ≤ (n : ℝ) := by
  unfold Sig
  calc ∑ k ∈ Finset.range n, f k β ≤ ∑ k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => hf k)
    _ = (n : ℝ) := by rw [Finset.sum_const, card_range, nsmul_eq_mul, mul_one]





theorem btb_bddAbove_ratio_of_le_one (f : ℕ → ℝ → ℝ) (β : ℝ)
    (hSpos : ∀ n, 2 ≤ n → 0 < Sig f n β) (hf : ∀ k, f k β ≤ 1) :
    IsBoundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig f n β)) :=
  btb_bddAbove_ratio_of_linear (fun n => Sig f n β) 1 (le_refl _) hSpos
    (fun n => by simpa using btb_Sig_le_card f β hf n)

























theorem btb_subcritical_decay_of_threshold (f f' : ℕ → ℝ → ℝ) (δ β M : ℝ)
    (hδ : 0 < δ) (hMnn : 0 ≤ M)
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (f n) (f' n x) x)
    (hfnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ f n x)
    (hfM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, f n x ≤ M)
    (hfmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → f k y ≤ f k x)
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig f n x)
    (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / Sig f n x) * f n x ≤ f' n x)
    (hSgβpos : ∀ n : ℕ, 2 ≤ n → 0 < Sig f n β)
    (hbddSet : BddBelow (thresholdSet (fun b n => Sig f n b)))
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig f n β)))
    (hlt : β < beta1 (fun b n => Sig f n b)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
  
  obtain ⟨N, α, hα, hSpoly⟩ :=
    btb_poly_bound_of_lt_threshold (fun b n => Sig f n b) β hbddSet hSgβpos hbdd hlt
  
  
  set α' : ℝ := min α 1 with hα'def
  have hα' : 0 < α' := lt_min hα (by norm_num)
  have hα'1 : α' ≤ 1 := min_le_right _ _
  have hα'le : α' ≤ α := min_le_left _ _
  
  set N' : ℕ := max N 1 with hN'def
  have hN' : 1 ≤ N' := le_max_right _ _
  have hSpoly' : ∀ n : ℕ, N' ≤ n → Sig f n β ≤ (n : ℝ) ^ (1 - α') := by
    intro n hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans hN' hn
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hbase := hSpoly n hnN
    
    have hmono : (n : ℝ) ^ (1 - α) ≤ (n : ℝ) ^ (1 - α') :=
      Real.rpow_le_rpow_of_exponent_le hn1R (by linarith [hα'le])
    exact le_trans hbase hmono
  exact isc_subcritical_decay f f' α' δ β M N' hδ hα' hα'1 hMnn hN' hd hfnn hfM hfmono
    hSpos hdiff hSpoly'




















theorem btb_fk_q2_subcritical_decay_of_threshold (θ θ' : ℕ → ℝ → ℝ) (δ β M : ℝ)
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
    (hbddSet : BddBelow (thresholdSet (fun b n => Sig θ n b)))
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig θ n β)))
    (hlt : β < beta1 (fun b n => Sig θ n b)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) :=
  btb_subcritical_decay_of_threshold θ θ' δ β M hδ hMnn hd hθnn hθM hθmono hSpos hdiff
    hSgβpos hbddSet hbdd hlt
















theorem btb_fk_q2_subcritical_decay_of_threshold' (θ θ' : ℕ → ℝ → ℝ) (δ β M : ℝ)
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
    (hlt : β < beta1 (fun b n => Sig θ n b)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) :=
  btb_fk_q2_subcritical_decay_of_threshold θ θ' δ β M hδ hMnn hd hθnn hθM hθmono hSpos hdiff
    hSgβpos hbddSet (btb_bddAbove_ratio_of_le_one θ β hSgβpos hθ1) hlt

end OSSS.BetaThresholdBound
end StatMech
