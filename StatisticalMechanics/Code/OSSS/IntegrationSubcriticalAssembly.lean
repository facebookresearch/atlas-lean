/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Code.OSSS.IntegrationSubcritical

open scoped BigOperators
open Real Filter Topology Set Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech
namespace OSSS.IntegrationSubcritical








noncomputable def Sig (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, f k x


theorem isc_Sig_succ (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) :
    Sig f (n + 1) x = Sig f n x + f n x := by
  unfold Sig; rw [Finset.sum_range_succ]


theorem isc_Sig_mono (f : ℕ → ℝ → ℝ) (n : ℕ) {y x : ℝ} (hyx : y ≤ x)
    (hf : ∀ k, f k y ≤ f k x) :
    Sig f n y ≤ Sig f n x := by
  unfold Sig
  exact Finset.sum_le_sum (fun k _ => hf k)








theorem isc_rate_weaken_stretched (n : ℕ) (α Sigx fp fnx : ℝ) (hn : 1 ≤ n)
    (hSig : 0 < Sigx) (hSigle : Sigx ≤ (n : ℝ) ^ (1 - α)) (hfnn : 0 ≤ fnx)
    (hdi : ((n : ℝ) / Sigx) * fnx ≤ fp) :
    ((n : ℝ) ^ α) * fnx ≤ fp := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hpow : (n : ℝ) / (n : ℝ) ^ (1 - α) = (n : ℝ) ^ α := by
    rw [div_eq_iff (by positivity), ← Real.rpow_add hnpos]; simp
  rw [← hpow]
  have h1 : (n : ℝ) / (n : ℝ) ^ (1 - α) ≤ (n : ℝ) / Sigx :=
    div_le_div_of_nonneg_left hnpos.le hSig hSigle
  calc (n : ℝ) / (n : ℝ) ^ (1 - α) * fnx ≤ (n : ℝ) / Sigx * fnx :=
        mul_le_mul_of_nonneg_right h1 hfnn
    _ ≤ fp := hdi











theorem isc_stretched_decay (f f' : ℕ → ℝ → ℝ) (n : ℕ) (α δ β M : ℝ)
    (hn : 1 ≤ n) (hδ : 0 < δ)
    (hd : ∀ x ∈ Icc (β - δ) β, HasDerivAt (f n) (f' n x) x)
    (hfnn : ∀ x ∈ Icc (β - δ) β, 0 ≤ f n x)
    (hSpos : ∀ x ∈ Icc (β - δ) β, 0 < Sig f n x)
    (hSpoly : ∀ x ∈ Icc (β - δ) β, Sig f n x ≤ (n : ℝ) ^ (1 - α))
    (hdiff : ∀ x ∈ Icc (β - δ) β, ((n : ℝ) / Sig f n x) * f n x ≤ f' n x)
    (hfb : f n β ≤ M) :
    f n (β - δ) ≤ M * Real.exp (-(δ * (n : ℝ) ^ α)) := by
  have hab : β - δ ≤ β := by linarith
  
  have hrate : ∀ x ∈ Icc (β - δ) β, ((n : ℝ) ^ α) * f n x ≤ f' n x := by
    intro x hx
    exact isc_rate_weaken_stretched n α (Sig f n x) (f' n x) (f n x) hn
      (hSpos x hx) (hSpoly x hx) (hfnn x hx) (hdiff x hx)
  have hg := isc_gronwall_decay (β - δ) β ((n : ℝ) ^ α) M hab (f n) (f' n) hd hrate hfb
  
  rwa [show β - (β - δ) = δ by ring, show (n : ℝ) ^ α * δ = δ * (n : ℝ) ^ α by ring] at hg















theorem isc_Sigma_bound (f : ℕ → ℝ → ℝ) (α δ β M : ℝ) (N n : ℕ)
    (hMnn : 0 ≤ M) (hα : 0 < α) (hδ : 0 < δ)
    (hfM : ∀ k, f k (β - δ) ≤ M)
    (hstretch : ∀ k, N ≤ k → f k (β - δ) ≤ M * Real.exp (-(δ * (k : ℝ) ^ α))) :
    Sig f n (β - δ)
      ≤ (N : ℝ) * M + ∑' k : ℕ, M * Real.exp (-(δ * (k : ℝ) ^ α)) := by
  unfold Sig
  refine isc_partial_sum_le (fun k => f k (β - δ))
    (fun k : ℕ => M * Real.exp (-(δ * (k : ℝ) ^ α))) M N n hfM hMnn ?_ ?_ hstretch
  · intro k; positivity
  · exact (isc_summable_stretched_exp α δ hα hδ).mul_left M

















theorem isc_stage2_decay (f f' : ℕ → ℝ → ℝ) (n : ℕ) (δ Q β M : ℝ)
    (hδ : 0 < δ) (hQ : 0 < Q)
    (hd : ∀ x ∈ Icc (β - 2 * δ) (β - δ), HasDerivAt (f n) (f' n x) x)
    (hfnn : ∀ x ∈ Icc (β - 2 * δ) (β - δ), 0 ≤ f n x)
    (hSpos : ∀ x ∈ Icc (β - 2 * δ) (β - δ), 0 < Sig f n x)
    (hSle : ∀ x ∈ Icc (β - 2 * δ) (β - δ), Sig f n x ≤ Q)
    (hdiff : ∀ x ∈ Icc (β - 2 * δ) (β - δ), ((n : ℝ) / Sig f n x) * f n x ≤ f' n x)
    (hfb : f n (β - δ) ≤ M) :
    f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
  have hab : β - 2 * δ ≤ β - δ := by linarith
  
  have hrate : ∀ x ∈ Icc (β - 2 * δ) (β - δ), ((n : ℝ) / Q) * f n x ≤ f' n x := by
    intro x hx
    exact isc_rate_weaken n (Sig f n x) (f' n x) (f n x) Q
      (hSpos x hx) (hSle x hx) (hfnn x hx) (hdiff x hx)
  have hg := isc_gronwall_decay (β - 2 * δ) (β - δ) ((n : ℝ) / Q) M hab
    (f n) (f' n) hd hrate hfb
  rwa [show (β - δ) - (β - 2 * δ) = δ by ring] at hg


























theorem isc_subcritical_decay (f f' : ℕ → ℝ → ℝ) (α δ β M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1) (hMnn : 0 ≤ M) (hN : 1 ≤ N)
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (f n) (f' n x) x)
    (hfnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ f n x)
    (hfM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, f n x ≤ M)
    (hfmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → f k y ≤ f k x)
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig f n x)
    (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / Sig f n x) * f n x ≤ f' n x)
    (hSpoly : ∀ n : ℕ, N ≤ n → Sig f n β ≤ (n : ℝ) ^ (1 - α)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
  
  have hsub1 : Icc (β - δ) β ⊆ Icc (β - 2 * δ) β := by
    intro x hx; rw [Set.mem_Icc] at hx ⊢; constructor <;> [linarith [hx.1]; exact hx.2]
  have hsub2 : Icc (β - 2 * δ) (β - δ) ⊆ Icc (β - 2 * δ) β := by
    intro x hx; rw [Set.mem_Icc] at hx ⊢; constructor <;> [exact hx.1; linarith [hx.2]]
  have hβinmem : β ∈ Icc (β - 2 * δ) β := by rw [Set.mem_Icc]; constructor <;> linarith
  have hβ'mem : β - δ ∈ Icc (β - 2 * δ) β := by rw [Set.mem_Icc]; constructor <;> linarith
  
  have hstretch_geN : ∀ n, N ≤ n → f n (β - δ) ≤ M * Real.exp (-(δ * (n : ℝ) ^ α)) := by
    intro n hNn
    have hn1 : 1 ≤ n := le_trans hN hNn
    
    have hSpolyx : ∀ x ∈ Icc (β - δ) β, Sig f n x ≤ (n : ℝ) ^ (1 - α) := by
      intro x hx
      have hxmem := hsub1 hx
      have hxβ : x ≤ β := (Set.mem_Icc.mp hx).2
      have hmono : Sig f n x ≤ Sig f n β :=
        isc_Sig_mono f n hxβ (fun k => hfmono k hxmem hβinmem hxβ)
      exact le_trans hmono (hSpoly n hNn)
    exact isc_stretched_decay f f' n α δ β M hn1 hδ
      (fun x hx => hd n x (hsub1 hx))
      (fun x hx => hfnn n x (hsub1 hx))
      (fun x hx => hSpos n hn1 x (hsub1 hx))
      hSpolyx
      (fun x hx => hdiff n hn1 x (hsub1 hx))
      (hfM n β hβinmem)
  
  have hfMβ' : ∀ k, f k (β - δ) ≤ M := fun k => hfM k (β - δ) hβ'mem
  
  set Q : ℝ := (N : ℝ) * M + ∑' k : ℕ, M * Real.exp (-(δ * (k : ℝ) ^ α)) with hQdef
  
  
  have hSig1pos : 0 < Sig f 1 (β - δ) := hSpos 1 le_rfl (β - δ) hβ'mem
  have hQbound1 : Sig f 1 (β - δ) ≤ Q :=
    isc_Sigma_bound f α δ β M N 1 hMnn hα hδ hfMβ' hstretch_geN
  have hQpos : 0 < Q := lt_of_lt_of_le hSig1pos hQbound1
  refine ⟨Q, hQpos, ?_⟩
  intro n hn1
  
  have hSle : ∀ x ∈ Icc (β - 2 * δ) (β - δ), Sig f n x ≤ Q := by
    intro x hx
    
    have hxmem := hsub2 hx
    have hxβ' : x ≤ β - δ := (Set.mem_Icc.mp hx).2
    have hmono : Sig f n x ≤ Sig f n (β - δ) :=
      isc_Sig_mono f n hxβ' (fun k => hfmono k hxmem hβ'mem hxβ')
    exact le_trans hmono
      (isc_Sigma_bound f α δ β M N n hMnn hα hδ hfMβ' hstretch_geN)
  exact isc_stage2_decay f f' n δ Q β M hδ hQpos
    (fun x hx => hd n x (hsub2 hx))
    (fun x hx => hfnn n x (hsub2 hx))
    (fun x hx => hSpos n hn1 x (hsub2 hx))
    hSle
    (fun x hx => hdiff n hn1 x (hsub2 hx))
    (hfM n (β - δ) hβ'mem)

end OSSS.IntegrationSubcritical
end StatMech
