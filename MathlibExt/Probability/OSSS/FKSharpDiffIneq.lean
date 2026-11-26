/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.OSSS.RussoPrefactor
public import MathlibExt.Probability.OSSS.IntegrationSubcriticalAssembly
public import MathlibExt.Probability.OSSS.Integration

/-!
# The Duminil-Copin–Raoufi–Tassion differential inequality for the random-cluster model, abstractly

Assembly of the Duminil-Copin–Raoufi–Tassion argument for random-cluster measures (the names
`fk_q2_*` refer to cluster weight `q = 2`, the FK representation of the Ising model), for abstract
functions `θ_n(β)` standing for `φ_β[0 ↔ ∂Λ_n]`. The chain is:

1. a Russo-type derivative formula `θ_n' = ∑_e g_e Cov_e` with positive prefactors `g_e`
   (hypothesis `hderiv`);
2. the OSSS inequality with the revealment of a decision tree exploring from `∂Λ_k`, averaged
   over `k`, giving `∑_e Cov_e ≥ (n / (4 Σ_n)) θ_n (1 - θ_n)` (hypothesis `hcov`);
3. hence the differential inequality `θ_n' ≥ (n / Σ_n) θ_n`, after the algebraic normalization
   `hident` that absorbs the constants `c_R (1 - θ_n) / 4` into `Σ_n`;
4. integration: exponential decay below the threshold
   (`StatMech.OSSS.IntegrationSubcritical.isc_subcritical_decay`) and the mean-field bound above
   it (`StatMech.OSSS.Integration.meanField_lower`).

Steps 3 and 4 are proved. Steps 1 and 2, which carry the probabilistic content, are hypotheses,
as are monotonicity in `β` (`hθmono`), the case assumption `hSpoly` (`Σ_n(β) ≤ n^{1-α}`), and,
for the mean-field part, the convergence hypotheses `hTβ`, `hTβ'`, `hmlim`, `hbound`. No
random-cluster measure appears in this file. Because the integration lemma has rate constant
`1`, `hcov` together with `hident` is stronger than the OSSS bound by a constant factor; see
`fk_q2_subcritical_decay_of_cov`.

## Main results

* `StatMech.OSSS.FKSharpDiffIneq.fkd_diff_ineq_pointwise`: steps 1–2 combined at one point.
* `StatMech.OSSS.FKSharpDiffIneq.fk_q2_subcritical_decay_of_cov`: exponential decay of
  `θ_n(β - 2δ)` from `hderiv`, `hcov` and the other hypotheses.
* `StatMech.OSSS.FKSharpDiffIneq.fk_q2_sharp_differential_of_cov`: the same, paired with the
  mean-field bound.

## References

* R. O'Donnell, M. Saks, O. Schramm, R. A. Servedio, *Every decision tree has an influential
  variable*, FOCS 2005.
* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and
  Potts models via decision trees*, Ann. of Math. 189 (2019), 75–99.
-/

@[expose] public section

open scoped BigOperators
open Real Filter Topology Set Finset

namespace StatMech
namespace OSSS.FKSharpDiffIneq

open StatMech.OSSS.RussoPrefactor
open StatMech.OSSS.IntegrationSubcritical
open StatMech.OSSS.Integration

/-- Pointwise combination of the covariance bound `hcov` (from OSSS) and the Russo-type bound
`hRusso`: `(c_R n / (4 Σ)) θ (1 - θ) ≤ θ'`. -/
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

/-- `fkd_diff_ineq_pointwise` with the prefactor `J_e / (e^{βJ_e} - 1)` and the derivative formula
`hderiv` as a hypothesis (see `StatMech.OSSS.RussoPrefactor` for its normalization). -/
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

/-- Algebraic step: under the normalization `hident` (`Σ_n c_R (1 - θ) = 4 Σ`), the assembled
inequality becomes `(n / Σ_n) θ ≤ θ'`. -/
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

/-- Conjunction of `isc_subcritical_decay` (decay below the threshold) and `meanField_lower` (linear
growth above it). The two parts share no hypotheses: `T`, `mseq` are unrelated to `θ`. -/
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
  ⟨isc_subcritical_decay θ θ' α δ β M N hδ hα hα1 hMnn hN hd hθnn hθM hθmono hSpos
      hdiff hSpoly,
   meanField_lower T mseq β₂' β₂ fβ₂ fβ₂' m hββ hm1 hTβ hTβ' hmlim hbound⟩

/-- Exponential decay `θ_n(β - 2δ) ≤ M e^{-n δ / Q}` (Duminil-Copin–Raoufi–Tassion, 2019),
conditional form.

The content is in the hypotheses: `hderiv` (derivative formula), `hcov` (OSSS inequality with
revealment), `hcRf` (positive lower bound on the prefactors), `hident` (normalization relating `Σ_n`
and `Sgn`), `hθmono` (monotonicity in `β`) and `hSpoly` (`Σ_n(β) ≤ n^{1-α}`, the subcritical case).
The differential inequality is derived from these, and the integration is proved. `_hJ` and `_hxpos`
are not used.

Fidelity: the integration lemma uses the rate `n / Σ_n` with constant `1`. `hident` forces
`Sgn = Σ_n c_R (1 - θ_n) / 4`, so `hcov` then asks for `∑_e Cov_e ≥ n θ_n / (c_R Σ_n)`. That is
stronger than the OSSS-revealment bound `∑_e Cov_e ≥ (n / (4 Σ_n)) θ_n (1 - θ_n)` by the factor
`4 / (c_R (1 - θ_n))`. In the literature this constant is carried in the rate `c n / Σ_n`
(equivalently, `β` is rescaled). -/
theorem fk_q2_subcritical_decay_of_cov {E : Type*} [Fintype E] [Nonempty E]
    (θ θ' : ℕ → ℝ → ℝ) (J : E → ℝ) (Cov : ℕ → ℝ → E → ℝ) (Sgn : ℕ → ℝ → ℝ)
    (cRf : ℕ → ℝ → ℝ)
    (α δ β M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1) (hMnn : 0 ≤ M) (hN : 1 ≤ N)
    (_hJ : ∀ e, 0 < J e)
    (_hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
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
  exact isc_subcritical_decay θ θ' α δ β M N hδ hα hα1 hMnn hN hd hθnn hθM hθmono hSpos
    hdiff hSpoly

/-- `fk_q2_subcritical_decay_of_cov` paired with the mean-field bound `meanField_lower`; the second
part takes its own convergence hypotheses and is independent of the first. -/
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
   meanField_lower T mseq β₂' β₂ fβ₂ fβ₂' m hββ hm1 hTβ hTβ' hmlim hbound⟩

end OSSS.FKSharpDiffIneq
end StatMech
