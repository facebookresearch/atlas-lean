/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.OSSS.RussoPrefactor
import Code.OSSS.IntegrationSubcriticalAssembly
import Code.OSSS.Integration

open scoped BigOperators
open Real Filter Topology Set Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech
namespace OSSS.FKSharpDiffIneq

open StatMech.OSSS.RussoPrefactor
open StatMech.OSSS.IntegrationSubcritical
open StatMech.OSSS.Integration

































theorem fkd_diff_ineq_pointwise (n : ℕ) (cR Sg θ θ' S : ℝ)
    (hSg : 0 < Sg) (hcR : 0 ≤ cR)
    (hcov : ((n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ S)
    (hRusso : cR * S ≤ θ') :
    (cR * (n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ θ' := by
  have h4Sg : 0 < 4 * Sg := by positivity
  
  have hmul : cR * (((n : ℝ) / (4 * Sg)) * (θ * (1 - θ))) ≤ cR * S :=
    mul_le_mul_of_nonneg_left hcov hcR
  calc (cR * (n : ℝ) / (4 * Sg)) * (θ * (1 - θ))
      = cR * (((n : ℝ) / (4 * Sg)) * (θ * (1 - θ))) := by ring
    _ ≤ cR * S := hmul
    _ ≤ θ' := hRusso


























theorem fkd_diff_ineq_pointwise_weighted {E : Type*} [Fintype E] [Nonempty E]
    (n : ℕ) (Sg θ θ' : ℝ) (J Cov : E → ℝ) (β : ℝ)
    (hSg : 0 < Sg) (hJ : ∀ e, 0 < J e) (hβ : 0 < β) (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e)
    (hcov : ((n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ ∑ e, Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ (cR * (n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ θ' := by
  obtain ⟨cR, hcRpos, hRusso⟩ :=
    rp_differential_lower_weighted J Cov β θ' hJ hβ hCov hderiv
  exact ⟨cR, hcRpos,
    fkd_diff_ineq_pointwise n cR Sg θ θ' (∑ e, Cov e) hSg hcRpos.le hcov hRusso⟩






























theorem fkd_engine_rate_of_assembled (n : ℕ) (cR Sg θ θ' Sn : ℝ)
    (hSg : 0 < Sg) (hcR : 0 < cR) (hSn : 0 < Sn) (hθ1 : θ < 1)
    (hident : Sn * (cR * (1 - θ)) = 4 * Sg)
    (hassembled : (cR * (n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) ≤ θ') :
    ((n : ℝ) / Sn) * θ ≤ θ' := by
  have h1θ : 0 < 1 - θ := by linarith
  have h4Sg : 0 < 4 * Sg := by positivity
  
  have hcR1θ : 0 < cR * (1 - θ) := mul_pos hcR h1θ
  have heq : ((n : ℝ) / Sn) * θ = (cR * (n : ℝ) / (4 * Sg)) * (θ * (1 - θ)) := by
    rw [← hident]; field_simp
  rw [heq]; exact hassembled





































theorem fk_q2_subcritical_decay (θ θ' : ℕ → ℝ → ℝ) (α δ β M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1) (hMnn : 0 ≤ M) (hN : 1 ≤ N)
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
    (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
    (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
    (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → θ k y ≤ θ k x)
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
    (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / Sig θ n x) * θ n x ≤ θ' n x)
    (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) :=
  isc_subcritical_decay θ θ' α δ β M N hδ hα hα1 hMnn hN hd hθnn hθM hθmono hSpos hdiff hSpoly




















theorem fk_q2_meanField_lower
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    β - β' ≤ fβ - fβ' :=
  meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound



























theorem fk_q2_sharp_differential
    (θ θ' : ℕ → ℝ → ℝ) (α δ β M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1) (hMnn : 0 ≤ M) (hN : 1 ≤ N)
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
    (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
    (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
    (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → θ k y ≤ θ k x)
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
    (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / Sig θ n x) * θ n x ≤ θ' n x)
    (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α))
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β₂' β₂ fβ₂ fβ₂' m : ℝ)
    (hββ : β₂' ≤ β₂) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β₂) atTop (𝓝 fβ₂))
    (hTβ' : Tendsto (fun n => T n β₂') atTop (𝓝 fβ₂'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β₂ - β₂') * mseq n ≤ T n β₂ - T n β₂') :
    (∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
        θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)))
      ∧ (β₂ - β₂' ≤ fβ₂ - fβ₂') :=
  ⟨fk_q2_subcritical_decay θ θ' α δ β M N hδ hα hα1 hMnn hN hd hθnn hθM hθmono hSpos
      hdiff hSpoly,
   fk_q2_meanField_lower T mseq β₂' β₂ fβ₂ fβ₂' m hββ hm1 hTβ hTβ' hmlim hbound⟩










































theorem fk_q2_subcritical_decay_of_cov {E : Type*} [Fintype E] [Nonempty E]
    (θ θ' : ℕ → ℝ → ℝ) (J : E → ℝ) (Cov : ℕ → ℝ → E → ℝ) (Sgn : ℕ → ℝ → ℝ)
    (cRf : ℕ → ℝ → ℝ)
    (α δ β M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1) (hMnn : 0 ≤ M) (hN : 1 ≤ N)
    (hJ : ∀ e, 0 < J e)
    (hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
    (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
    (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
    (hθlt1 : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x < 1)
    (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → θ k y ≤ θ k x)
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
    (hSgnpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sgn n x)
    (hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e)
    (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Cov n x e)
    (hcov : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / (4 * Sgn n x)) * (θ n x * (1 - θ n x)) ≤ ∑ e, Cov n x e)
    (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
    (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * Sgn n x)
    (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
  
  have hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / Sig θ n x) * θ n x ≤ θ' n x := by
    intro n hn x hx
    obtain ⟨hcRpos, hcRle⟩ := hcRf n x hx
    
    have hRusso : cRf n x * ∑ e, Cov n x e ≤ θ' n x := by
      rw [hderiv n x hx]
      exact rp_prefactor_extraction (fun e => J e / (Real.exp (x * J e) - 1)) (Cov n x)
        (cRf n x) hcRle (hCovnn n x hx)
    
    have hassembled : (cRf n x * (n : ℝ) / (4 * Sgn n x)) * (θ n x * (1 - θ n x)) ≤ θ' n x :=
      fkd_diff_ineq_pointwise n (cRf n x) (Sgn n x) (θ n x) (θ' n x) (∑ e, Cov n x e)
        (hSgnpos n x hx) hcRpos.le (hcov n x hx) hRusso
    
    exact fkd_engine_rate_of_assembled n (cRf n x) (Sgn n x) (θ n x) (θ' n x) (Sig θ n x)
      (hSgnpos n x hx) hcRpos (hSpos n hn x hx) (hθlt1 n x hx) (hident n hn x hx) hassembled
  exact fk_q2_subcritical_decay θ θ' α δ β M N hδ hα hα1 hMnn hN hd hθnn hθM hθmono hSpos
    hdiff hSpoly



























theorem fk_q2_sharp_differential_of_cov {E : Type*} [Fintype E] [Nonempty E]
    (θ θ' : ℕ → ℝ → ℝ) (J : E → ℝ) (Cov : ℕ → ℝ → E → ℝ) (Sgn : ℕ → ℝ → ℝ)
    (cRf : ℕ → ℝ → ℝ)
    (α δ β M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1) (hMnn : 0 ≤ M) (hN : 1 ≤ N)
    (hJ : ∀ e, 0 < J e)
    (hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
    (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
    (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
    (hθlt1 : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x < 1)
    (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → θ k y ≤ θ k x)
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
    (hSgnpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sgn n x)
    (hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e)
    (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Cov n x e)
    (hcov : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / (4 * Sgn n x)) * (θ n x * (1 - θ n x)) ≤ ∑ e, Cov n x e)
    (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
    (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * Sgn n x)
    (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α))
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β₂' β₂ fβ₂ fβ₂' m : ℝ)
    (hββ : β₂' ≤ β₂) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β₂) atTop (𝓝 fβ₂))
    (hTβ' : Tendsto (fun n => T n β₂') atTop (𝓝 fβ₂'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β₂ - β₂') * mseq n ≤ T n β₂ - T n β₂') :
    (∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
        θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)))
      ∧ (β₂ - β₂' ≤ fβ₂ - fβ₂') :=
  ⟨fk_q2_subcritical_decay_of_cov θ θ' J Cov Sgn cRf α δ β M N hδ hα hα1 hMnn hN hJ hxpos
      hd hθnn hθM hθlt1 hθmono hSpos hSgnpos hCovnn hderiv hcov hcRf hident hSpoly,
   fk_q2_meanField_lower T mseq β₂' β₂ fβ₂ fβ₂' m hββ hm1 hTβ hTβ' hmlim hbound⟩

end OSSS.FKSharpDiffIneq
end StatMech
