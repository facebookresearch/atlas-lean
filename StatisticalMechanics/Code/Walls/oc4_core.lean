/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib
import Code.OSSS.FKRevealmentClose
import Code.OSSS.FKSharpDiffIneq
import Code.OSSS.MonotoneOSSSAssembly
import Code.Walls.oc4_revealeqreach
import Code.Walls.oc4_scalesum

open scoped BigOperators
open MeasureTheory Finset Real Filter Topology Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.FKRevealmentClose
open StatMech.OSSS.FKSharpDiffIneq
open StatMech.OSSS.IntegrationSubcritical
open StatMech.OSSS.AdaptMConditional
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.MonotonicFK
































theorem oc4_fk_hcov_codingFrame {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {κ : Type*} [Fintype κ] [Nonempty κ] {m : ℕ} (σf : κ → (Fin m ≃ Sym2 V))
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (R : κ → Sym2 V → ℝ) (D : ℝ) (hDpos : 0 < D)
    (hreach : ∀ k e, revealAdapt (fkMass G p 2) (σf k) f e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    ((Fintype.card κ : ℝ) / (4 * ((Fintype.card κ : ℝ) * D / 4)))
        * (Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f))
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
  set N := (Fintype.card κ : ℝ) with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  
  have hgenuine := fk_q2_cov_lower_bound_from_perScaleReveal G hp hp1 σf hf hf0 hf1 hidem
    R D hDpos hreach hsum
  
  have h4 : 4 * (N * D / 4) = N * D := by ring
  rw [h4]
  rw [show N / (N * D) = 1 / D by field_simp]
  rw [one_div, ← div_eq_inv_mul]
  exact hgenuine





















theorem oc4_fk_reveal_input_codingFrame {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    revealAdapt (fkMass G p q) σ f e = reachProb (fkMass G p q) σ f e
      ∧ reachProb (fkMass G p q) σ f e = oc4_notDetProb (fkMass G p q) σ f e :=
  oc4_fk_reveal_eq_reach G hp hp1 hq σ f e




























theorem oc4_fk_hcovFamily_codingFrame {V : Type*} [Fintype V] [DecidableEq V]
    (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (pf : ℕ → ℝ → ℝ) (ff : ℕ → ℝ → ConfigSpace (Sym2 V) → ℝ)
    {κ : ℕ → Type} [∀ n, Fintype (κ n)] [∀ n, Nonempty (κ n)]
    (mdim : ℕ → ℕ) (σf : ∀ n, κ n → (Fin (mdim n) ≃ Sym2 V))
    (Rfam : ∀ n, κ n → Sym2 V → ℝ) (Dseq : ℕ → ℝ → ℝ) (β δ : ℝ)
    (hp : ∀ n x, x ∈ Icc (β - 2 * δ) β → 0 < pf n x)
    (hp1 : ∀ n x, x ∈ Icc (β - 2 * δ) β → pf n x < 1)
    (hfmono : ∀ n x, Monotone (ff n x)) (hf0 : ∀ n x, 0 ≤ ff n x)
    (hf1 : ∀ n x ω, ff n x ω ≤ 1) (hidem : ∀ n x ω, ff n x ω * ff n x ω = ff n x ω)
    (hDpos : ∀ n x, x ∈ Icc (β - 2 * δ) β → 0 < Dseq n x)
    (hreach : ∀ n x, x ∈ Icc (β - 2 * δ) β → ∀ k e,
      revealAdapt (fkMass (Gf n) (pf n x) 2) (σf n k) (ff n x) e ≤ Rfam n k e)
    (hsum : ∀ n x, x ∈ Icc (β - 2 * δ) β → ∀ e,
      (∑ k, Rfam n k e) ≤ (Fintype.card (κ n) : ℝ) * Dseq n x) :
    ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)
          * (1 - Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)) / Dseq n x
        ≤ ∑ e, Lindeberg.cov (fkMass (Gf n) (pf n x) 2) (ff n x) (Lindeberg.coord e) := by
  intro n x hx
  exact fk_q2_cov_lower_bound_from_perScaleReveal (Gf n) (hp n x hx) (hp1 n x hx)
    (σf n) (hfmono n x) (hf0 n x) (hf1 n x) (hidem n x) (Rfam n) (Dseq n x) (hDpos n x hx)
    (hreach n x hx) (hsum n x hx)






























theorem oc4_fk_sharp_subcritical_of_codingFrame {E : Type*} [Fintype E] [Nonempty E]
    (θ θ' : ℕ → ℝ → ℝ) (J : E → ℝ) (Cov : ℕ → ℝ → E → ℝ)
    (cRf : ℕ → ℝ → ℝ) (Dseq : ℕ → ℝ → ℝ)
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
    (hDpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Dseq n x)
    (hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e)
    (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Cov n x e)
    (hcovGenuine : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      θ n x * (1 - θ n x) / Dseq n x ≤ ∑ e, Cov n x e)
    (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
    (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * ((n : ℝ) * Dseq n x / 4))
    (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
  
  set Sgn : ℕ → ℝ → ℝ := fun n x => (n : ℝ) * Dseq n x / 4 + (if n = 0 then 1 else 0)
    with hSgndef
  
  have hcov : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / (4 * Sgn n x)) * (θ n x * (1 - θ n x)) ≤ ∑ e, Cov n x e := by
    intro n x hx
    by_cases hn0 : n = 0
    · subst hn0
      rw [show ((0 : ℕ) : ℝ) / (4 * Sgn 0 x) * (θ 0 x * (1 - θ 0 x)) = 0 by
        rw [Nat.cast_zero, zero_div, zero_mul]]
      exact Finset.sum_nonneg (fun e _ => hCovnn 0 x hx e)
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      have hDp := hDpos n x hx
      have hSgnval : Sgn n x = (n : ℝ) * Dseq n x / 4 := by simp [hSgndef, hn0]
      rw [hSgnval, show 4 * ((n : ℝ) * Dseq n x / 4) = (n : ℝ) * Dseq n x by ring,
        show (n : ℝ) / ((n : ℝ) * Dseq n x) = 1 / Dseq n x by field_simp,
        one_div, ← div_eq_inv_mul]
      exact hcovGenuine n x hx
  have hSgnpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sgn n x := by
    intro n x hx
    by_cases hn0 : n = 0
    · subst hn0; simp [hSgndef]
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      have hDp := hDpos n x hx
      simp only [hSgndef, hn0, if_false, add_zero]
      positivity
  have hident' : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * Sgn n x := by
    intro n hn x hx
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
    have hSgnval : Sgn n x = (n : ℝ) * Dseq n x / 4 := by simp [hSgndef, hn0]
    rw [hSgnval]; exact hident n hn x hx
  exact fk_q2_subcritical_decay_of_cov θ θ' J Cov Sgn cRf α δ β M N hδ hα hα1 hMnn hN hJ
    hxpos hd hθnn hθM hθlt1 hθmono hSpos hSgnpos hCovnn hderiv hcov hcRf hident' hSpoly


























theorem oc4_fk_sharpness_of_codingFrame {E : Type*} [Fintype E] [Nonempty E]
    (θ θ' : ℕ → ℝ → ℝ) (J : E → ℝ) (Cov : ℕ → ℝ → E → ℝ)
    (cRf : ℕ → ℝ → ℝ) (Dseq : ℕ → ℝ → ℝ)
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
    (hDpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Dseq n x)
    (hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e)
    (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Cov n x e)
    (hcovGenuine : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      θ n x * (1 - θ n x) / Dseq n x ≤ ∑ e, Cov n x e)
    (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
    (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * ((n : ℝ) * Dseq n x / 4))
    (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α))
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β₂' β₂ fβ₂ fβ₂' mlim : ℝ)
    (hββ : β₂' ≤ β₂) (hm1 : 1 ≤ mlim)
    (hTβ : Tendsto (fun n => T n β₂) atTop (𝓝 fβ₂))
    (hTβ' : Tendsto (fun n => T n β₂') atTop (𝓝 fβ₂'))
    (hmlim : Tendsto mseq atTop (𝓝 mlim))
    (hbound : ∀ᶠ n in atTop, (β₂ - β₂') * mseq n ≤ T n β₂ - T n β₂') :
    (∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
        θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)))
      ∧ (β₂ - β₂' ≤ fβ₂ - fβ₂') :=
  ⟨oc4_fk_sharp_subcritical_of_codingFrame θ θ' J Cov cRf Dseq α δ β M N hδ hα hα1 hMnn hN hJ
      hxpos hd hθnn hθM hθlt1 hθmono hSpos hDpos hCovnn hderiv hcovGenuine hcRf hident hSpoly,
   fk_q2_meanField_lower T mseq β₂' β₂ fβ₂ fβ₂' mlim hββ hm1 hTβ hTβ' hmlim hbound⟩
































theorem oc4_fk_sharp_subcritical_fullyDischarged {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty (Sym2 V)]
    (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (pf : ℕ → ℝ → ℝ) (ff : ℕ → ℝ → ConfigSpace (Sym2 V) → ℝ)
    {κ : ℕ → Type} [∀ n, Fintype (κ n)] [∀ n, Nonempty (κ n)]
    (mdim : ℕ → ℕ) (σf : ∀ n, κ n → (Fin (mdim n) ≃ Sym2 V))
    (Rfam : ∀ n, κ n → Sym2 V → ℝ) (Dseq : ℕ → ℝ → ℝ)
    (θ' : ℕ → ℝ → ℝ) (J : Sym2 V → ℝ) (cRf : ℕ → ℝ → ℝ)
    (α δ β M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1) (hMnn : 0 ≤ M) (hN : 1 ≤ N)
    (hJ : ∀ e, 0 < J e)
    (hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
    
    (hp : ∀ n x, x ∈ Icc (β - 2 * δ) β → 0 < pf n x)
    (hp1 : ∀ n x, x ∈ Icc (β - 2 * δ) β → pf n x < 1)
    (hfmono : ∀ n x, Monotone (ff n x)) (hf0 : ∀ n x, 0 ≤ ff n x)
    (hf1 : ∀ n x ω, ff n x ω ≤ 1) (hidem : ∀ n x ω, ff n x ω * ff n x ω = ff n x ω)
    (hDpos : ∀ n x, x ∈ Icc (β - 2 * δ) β → 0 < Dseq n x)
    
    (hreach : ∀ n x, x ∈ Icc (β - 2 * δ) β → ∀ k e,
      revealAdapt (fkMass (Gf n) (pf n x) 2) (σf n k) (ff n x) e ≤ Rfam n k e)
    (hsum : ∀ n x, x ∈ Icc (β - 2 * δ) β → ∀ e,
      (∑ k, Rfam n k e) ≤ (Fintype.card (κ n) : ℝ) * Dseq n x)
    
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      HasDerivAt (fun y => Lindeberg.mean (fkMass (Gf n) (pf n y) 2) (ff n y)) (θ' n x) x)
    (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x) ≤ M)
    (hθlt1 : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x) < 1)
    (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → Lindeberg.mean (fkMass (Gf k) (pf k y) 2) (ff k y)
        ≤ Lindeberg.mean (fkMass (Gf k) (pf k x) 2) (ff k x))
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      0 < Sig (fun n x => Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)) n x)
    (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1))
        * Lindeberg.cov (fkMass (Gf n) (pf n x) 2) (ff n x) (Lindeberg.coord e))
    (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
    (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      Sig (fun n x => Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)) n x
          * (cRf n x * (1 - Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)))
        = 4 * ((n : ℝ) * Dseq n x / 4))
    (hSpoly : ∀ n : ℕ, N ≤ n →
      Sig (fun n x => Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)) n β
        ≤ (n : ℝ) ^ (1 - α)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      Lindeberg.mean (fkMass (Gf n) (pf n (β - 2 * δ)) 2) (ff n (β - 2 * δ))
        ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
  
  set θ : ℕ → ℝ → ℝ := fun n x => Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x) with hθdef
  set Cov : ℕ → ℝ → Sym2 V → ℝ :=
    fun n x e => Lindeberg.cov (fkMass (Gf n) (pf n x) 2) (ff n x) (Lindeberg.coord e) with hCdef
  
  
  have hcovGenuine : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β,
      θ n x * (1 - θ n x) / Dseq n x ≤ ∑ e, Cov n x e :=
    oc4_fk_hcovFamily_codingFrame Gf pf ff mdim σf Rfam Dseq β δ hp hp1 hfmono hf0 hf1 hidem
      hDpos hreach hsum
  
  have hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e := by
    intro n x hx e
    exact LindebergTree.cov_coord_nonneg
      (fun ω => fkMass_pos (Gf n) (hp n x hx) (hp1 n x hx) (by norm_num) ω)
      (fkMass_sum_eq_one (Gf n) (hp n x hx) (hp1 n x hx) (by norm_num))
      (FK.fkProb_FKGLatticeCondition (Gf n) (hp n x hx) (hp1 n x hx) (by norm_num))
      (hfmono n x) e
  have hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x := by
    intro n x hx
    rw [hθdef]
    unfold Lindeberg.mean
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hf0 n x ω)
      (fkMass_pos (Gf n) (hp n x hx) (hp1 n x hx) (by norm_num) ω).le)
  exact oc4_fk_sharp_subcritical_of_codingFrame θ θ' J Cov cRf Dseq α δ β M N hδ hα hα1 hMnn hN
    hJ hxpos hd hθnn hθM hθlt1 hθmono hSpos hDpos hCovnn hderiv hcovGenuine hcRf hident hSpoly

end Walls
end StatMech
