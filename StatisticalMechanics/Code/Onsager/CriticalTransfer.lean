/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.FreeEnergy
import Code.Ising.PressureBCIndep









namespace StatMech.Onsager

open StatMech.Ising

theorem ons_bond_abs_le_one {V : Type*}
    (s : ConfigSpace V) (e : Sym2 V) : |bond s e| ≤ 1 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [bond_mk, abs_mul]
      have hx := abs_spin_le_one s x
      have hy := abs_spin_le_one s y
      nlinarith [abs_nonneg (spin s x), abs_nonneg (spin s y)]

theorem ons_hamiltonian_zero_abs_le_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ConfigSpace V) :
    |hamiltonian G 0 s| ≤ G.edgeFinset.card := by
  unfold hamiltonian
  simp only [zero_mul, sub_zero, abs_neg]
  calc
    |∑ e ∈ G.edgeFinset, bond s e| ≤
        ∑ e ∈ G.edgeFinset, |bond s e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ G.edgeFinset, (1 : ℝ) :=
      Finset.sum_le_sum fun e _ => ons_bond_abs_le_one s e
    _ = G.edgeFinset.card := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem ons_Z_scaled_energy (beta : ℝ)
    {Omega : Type*} [Fintype Omega] (E : Omega → ℝ) :
    StatMech.Ising.Z 1 (fun s => beta * E s) =
      StatMech.Ising.Z beta E := by
  unfold StatMech.Ising.Z
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring

theorem ons_log_Z_lipschitz
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta gamma : ℝ) :
    |Real.log (ons_Z G beta) - Real.log (ons_Z G gamma)| ≤
      |beta - gamma| * G.edgeFinset.card := by
  let E : ConfigSpace V → ℝ := hamiltonian G 0
  have hdiff : ∀ s : ConfigSpace V,
      |beta * E s - gamma * E s| ≤
        |beta - gamma| * G.edgeFinset.card := by
    intro s
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (ons_hamiltonian_zero_abs_le_edges G s) (abs_nonneg _)
  have h := StatMech.Ising.logZ_dist_le 1
    (fun s => beta * E s) (fun s => gamma * E s)
    (|beta - gamma| * G.edgeFinset.card) hdiff
  rw [abs_one, one_mul, ons_Z_scaled_energy beta E,
    ons_Z_scaled_energy gamma E] at h
  simpa only [ons_Z, StatMech.Ising.isingZ_eq_Z] using h



theorem ons_torusPressure_lipschitz (L : ℕ) [Fact (2 < L)]
    (beta gamma : ℝ) :
    |ons_pressureFinite (onsTorusGraph L) beta -
        ons_pressureFinite (onsTorusGraph L) gamma| ≤
      2 * |beta - gamma| := by
  rw [ons_pressureFinite, ons_pressureFinite, ← sub_div, abs_div]
  have h := ons_log_Z_lipschitz (onsTorusGraph L) beta gamma
  rw [onsTorus_card_edges] at h
  rw [onsTorus_card_verts]
  have hL : (L : ℝ) ≠ 0 := by
    exact_mod_cast (show L ≠ 0 by have := (Fact.out : 2 < L); omega)
  push_cast at h ⊢
  rw [abs_of_nonneg (sq_nonneg (L : ℝ))]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) ^ 2)]
  calc
    |Real.log (ons_Z (onsTorusGraph L) beta) -
        Real.log (ons_Z (onsTorusGraph L) gamma)| ≤
      |beta - gamma| * (2 * (L : ℝ) ^ 2) := h
    _ = 2 * |beta - gamma| * (L : ℝ) ^ 2 := by ring



noncomputable def ons_torusPressureSeq (beta : ℝ) (L : ℕ) : ℝ :=
  if h : 2 < L then
    letI : Fact (2 < L) := ⟨h⟩
    ons_pressureFinite (onsTorusGraph L) beta
  else 0

theorem ons_torusPressureSeq_lipschitz (beta gamma : ℝ) (L : ℕ) :
    |ons_torusPressureSeq beta L - ons_torusPressureSeq gamma L| ≤
      2 * |beta - gamma| := by
  by_cases hL : 2 < L
  · letI : Fact (2 < L) := ⟨hL⟩
    simpa [ons_torusPressureSeq, hL] using
      ons_torusPressure_lipschitz L beta gamma
  · simp [ons_torusPressureSeq, hL]




theorem ons_free_energy_critical_of_noncritical
    (hcontinuous : ContinuousAt ons_pressure ons_betaC)
    (hnoncritical : ∀ beta : ℝ, 0 ≤ beta → beta ≠ ons_betaC →
      Filter.Tendsto (ons_torusPressureSeq beta)
        Filter.atTop (nhds (ons_pressure beta))) :
    Filter.Tendsto (ons_torusPressureSeq ons_betaC)
      Filter.atTop (nhds (ons_pressure ons_betaC)) := by
  let gamma : ℕ → ℝ := fun n => ons_betaC + 1 / ((n : ℝ) + 1)
  have hgamma : Filter.Tendsto gamma Filter.atTop (nhds ons_betaC) := by
    simpa only [gamma, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hpressure : Filter.Tendsto (fun n => ons_pressure (gamma n))
      Filter.atTop (nhds (ons_pressure ons_betaC)) :=
    hcontinuous.tendsto.comp hgamma
  rw [Metric.tendsto_atTop] at hpressure hgamma ⊢
  intro epsilon hepsilon
  obtain ⟨Npressure, hNpressure⟩ := hpressure (epsilon / 3) (by positivity)
  obtain ⟨Ngamma, hNgamma⟩ := hgamma (epsilon / 6) (by positivity)
  let n := max Npressure Ngamma
  have hnpressure :
      dist (ons_pressure (gamma n)) (ons_pressure ons_betaC) < epsilon / 3 :=
    hNpressure n (le_max_left _ _)
  have hngamma : dist (gamma n) ons_betaC < epsilon / 6 :=
    hNgamma n (le_max_right _ _)
  have hgpos : 0 < gamma n := by
    dsimp only [gamma]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hone : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hden
    linarith [ons_betaC_pos]
  have hgne : gamma n ≠ ons_betaC := by
    dsimp only [gamma]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hone : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hden
    linarith
  have hfixed := hnoncritical (gamma n) hgpos.le hgne
  rw [Metric.tendsto_atTop] at hfixed
  obtain ⟨Nfixed, hNfixed⟩ := hfixed (epsilon / 3) (by positivity)
  refine ⟨Nfixed, fun L hL => ?_⟩
  have hmiddle := hNfixed L hL
  have hfinite := ons_torusPressureSeq_lipschitz ons_betaC (gamma n) L
  rw [Real.dist_eq] at hmiddle hnpressure hngamma ⊢
  calc
    |ons_torusPressureSeq ons_betaC L - ons_pressure ons_betaC| ≤
        |ons_torusPressureSeq ons_betaC L - ons_torusPressureSeq (gamma n) L| +
          |ons_torusPressureSeq (gamma n) L - ons_pressure (gamma n)| +
          |ons_pressure (gamma n) - ons_pressure ons_betaC| := by
      calc
        |ons_torusPressureSeq ons_betaC L - ons_pressure ons_betaC| ≤
            |ons_torusPressureSeq ons_betaC L - ons_torusPressureSeq (gamma n) L| +
              |ons_torusPressureSeq (gamma n) L - ons_pressure ons_betaC| :=
          abs_sub_le _ _ _
        _ ≤ |ons_torusPressureSeq ons_betaC L - ons_torusPressureSeq (gamma n) L| +
            (|ons_torusPressureSeq (gamma n) L - ons_pressure (gamma n)| +
              |ons_pressure (gamma n) - ons_pressure ons_betaC|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ = _ := by ring
    _ < 2 * (epsilon / 6) + epsilon / 3 + epsilon / 3 := by
      gcongr
      calc
        |ons_torusPressureSeq ons_betaC L - ons_torusPressureSeq (gamma n) L| ≤
            2 * |ons_betaC - gamma n| := hfinite
        _ = 2 * |gamma n - ons_betaC| := by rw [abs_sub_comm]
        _ < 2 * (epsilon / 6) := by gcongr
    _ = epsilon := by ring

end StatMech.Onsager
