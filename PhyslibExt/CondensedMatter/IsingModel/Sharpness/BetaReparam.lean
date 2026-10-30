/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessBeta
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercolationMeanfield
public import MathlibExt.Probability.Percolation.SurfaceReassembly

/-!
# Mean-field differential inequality on the β scale

Chain-rule transfer of the percolation differential inequality from the `p` scale to the `β` scale,
and the subcritical exponential decay at `p(β)`.

## i. Overview

With `p(β) = 1 - e^{-βJ}` one has `p'(β) = J(1 - p)` and `p(β) ≤ βJ`. The inequality `f'(p) ≥
(1/(p(1 - p))) m (1 - f(p))` for the crossing probability becomes an inequality in `β`, which
integrates over `[β₀, β]`. Below `β̃_c` the subcritical decay of the connection probability holds at
`p(β)`.

## ii. Key results

- `shr_pBeta_hasDerivAt` : `p'(β) = J e^{-βJ}`
- `shr_meanfield_beta` : the differential inequality on the `β` scale
- `shr_integrate_beta` : integrated form
- `shr_item3_beta` : exponential decay at `p(β)` when `φ_{p(β)}(S) < 1`

## iii. Table of contents

- A. The derivative of the parametrization
- B. Transfer of the differential inequality
- C. Subcritical decay

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}

/-! ## A. The derivative of the parametrization -/

lemma shr_pBeta_hasDerivAt (J β : ℝ) :
    HasDerivAt (pBeta J) (J * Real.exp (-β * J)) β := by
  unfold pBeta
  have h1 : HasDerivAt (fun b => -b * J) (-J) β := by
    simpa using ((hasDerivAt_id β).neg.mul_const J)
  have h2 : HasDerivAt (fun b => Real.exp (-b * J)) (Real.exp (-β * J) * (-J)) β :=
    (Real.hasDerivAt_exp _).comp β h1
  have h3 : HasDerivAt (fun b => 1 - Real.exp (-b * J)) (-(Real.exp (-β * J) * (-J))) β := by
    exact ((hasDerivAt_const β (1 : ℝ)).sub h2).congr_deriv (by simp)
  convert h3 using 1; ring

lemma shr_pBeta_le_betaJ (J β : ℝ) : pBeta J β ≤ β * J := by
  unfold pBeta
  have := Real.add_one_le_exp (-β * J)
  nlinarith [this]

/-! ## B. Transfer of the differential inequality -/

lemma shr_meanfield_beta (J β m fp' : ℝ) (f : ℝ → ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (hp0 : 0 < pBeta J β) (hp1 : pBeta J β < 1) (hm : 0 ≤ m) (hf1 : f (pBeta J β) ≤ 1)
    (hf : HasDerivAt f fp' (pBeta J β))
    (hpform : (1 / (pBeta J β * (1 - pBeta J β))) * m * (1 - f (pBeta J β)) ≤ fp') :
    HasDerivAt (fun b => f (pBeta J b)) (fp' * (J * Real.exp (-β * J))) β
      ∧ (1 / β) * m * (1 - f (pBeta J β)) ≤ fp' * (J * Real.exp (-β * J)) := by
  set p := pBeta J β with hp_def
  have hF : HasDerivAt (fun b => f (pBeta J b))
      (fp' * (J * Real.exp (-β * J))) β := by
    have := hf.comp β (shr_pBeta_hasDerivAt J β)
    exact this
  refine ⟨hF, ?_⟩
  have hexp_eq : Real.exp (-β * J) = 1 - p := by rw [hp_def]; unfold pBeta; ring
  rw [hexp_eq]
  have h1mp : 0 < 1 - p := by linarith
  have hJfac : 0 < J * (1 - p) := mul_pos hJ h1mp
  have step1 : (1 / (p * (1 - p))) * m * (1 - f p) * (J * (1 - p))
      ≤ fp' * (J * (1 - p)) := mul_le_mul_of_nonneg_right hpform (le_of_lt hJfac)
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1mpne : (1 - p) ≠ 0 := ne_of_gt h1mp
  have hsimp : (1 / (p * (1 - p))) * m * (1 - f p) * (J * (1 - p)) = (J / p) * m * (1 - f p) := by
    field_simp
  rw [hsimp] at step1
  have hinvle : 1 / β ≤ J / p := by
    rw [div_le_div_iff₀ hβ hp0]
    have := shr_pBeta_le_betaJ J β; rw [← hp_def] at this; nlinarith [this]
  have hmnn : 0 ≤ m * (1 - f p) := mul_nonneg hm (by linarith)
  have step0 : (1 / β) * m * (1 - f p) ≤ (J / p) * m * (1 - f p) := by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hinvle hmnn
  linarith [step0, step1]

lemma shr_meanfield_beta_crossProbReal {q : ℝ≥0} (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
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
  have hbr := shr_meanfield_beta J β 1 (deriv (crossPoly d n) p) (crossProbReal d (n + 1))
    hJ hβ hp0 hp1 (by norm_num) hf1 hf (by simpa using hpform)
  exact ⟨hbr.1, by simpa using hbr.2⟩

lemma shr_integrate_beta (J β β₀ : ℝ) (f : ℝ → ℝ) (hJ : 0 < J)
    (hβ₀ : 0 < β₀) (hββ₀ : β₀ < β)
    (hdiff : ∀ q ∈ Ico (pBeta J β₀) 1, DifferentiableAt ℝ f q)
    (hineq : ∀ q ∈ Ioo (pBeta J β₀) 1, (1 / (q * (1 - q))) * (1 - f q) ≤ deriv f q)
    (hf0 : 0 ≤ f (pBeta J β₀)) :
    (β - β₀) / β ≤ f (pBeta J β) := by
  set p₀ := pBeta J β₀ with hp₀
  set p := pBeta J β with hp
  have hp₀0 : 0 < p₀ := by
    rw [hp₀]; unfold pBeta
    have : Real.exp (-β₀ * J) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hp₀1 : p₀ < 1 := pBeta_lt_one J β₀
  have hp₀p : p₀ ≤ p := le_of_lt (pBeta_strictMono hJ hββ₀)
  have hp1 : p < 1 := pBeta_lt_one J β
  have hpf := profile_ge_of_diffineq p₀ hp₀0 hp₀1 f hdiff hineq hf0 hp₀p hp1
  exact pform_le_betaform J β β₀ p₀ (f p) hJ hβ₀ hββ₀ hp₀0 hp₀1
    (by rw [hp₀]; unfold pBeta; ring) hpf

/-! ## C. Subcritical decay -/

lemma shr_item3_beta (J β : ℝ) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d)))
    (hphi : phi d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ∃ c > 0, ∃ C > 0, ∀ n,
      crossProb d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) n
        ≤ C * Real.exp (-c * n) :=
  StatMech.Percolation.crossProb_exp_decay_of_phi_lt_one
    (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) S hoS hphi L hL hSbox

end Sharpness

end StatMech

