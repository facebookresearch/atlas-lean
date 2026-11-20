/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Code.Ising.Magnetization

open Set Filter Topology

namespace StatMech.Ising




def HasWeakSurfaceTensionLowerBound
    (J : ℝ) (M tau : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b →
    2 * J * (M a) ^ 2 * (b - a) ≤ tau b - tau a




theorem weakSurfaceTensionLowerBound_of_deriv
    (J : ℝ) (M tau : ℝ → ℝ)
    (hJ : 0 ≤ J)
    (hMnonneg : ∀ beta, 0 < beta → 0 ≤ M beta)
    (hMmono : MonotoneOn M (Ioi 0))
    (htauCont : ContinuousOn tau (Ici 0))
    (htauDiff : DifferentiableOn ℝ tau (Ioi 0))
    (hderiv : ∀ beta, 0 < beta →
      2 * J * (M beta) ^ 2 ≤ deriv tau beta) :
    HasWeakSurfaceTensionLowerBound J M tau := by
  intro a b ha hab
  rcases eq_or_lt_of_le hab with rfl | hablt
  · simp
  have hIcc : Icc a b ⊆ Ici (0 : ℝ) := by
    intro x hx
    exact ha.le.trans hx.1
  have hIoo : Ioo a b ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact ha.trans hx.1
  obtain ⟨c, hc, hcSlope⟩ := exists_deriv_eq_slope tau hablt
    (htauCont.mono hIcc) (htauDiff.mono hIoo)
  have haMem : a ∈ Ioi (0 : ℝ) := ha
  have hcMem : c ∈ Ioi (0 : ℝ) := hIoo hc
  have hMac : M a ≤ M c := hMmono haMem hcMem hc.1.le
  have hMa0 : 0 ≤ M a := hMnonneg a ha
  have hMc0 : 0 ≤ M c := hMnonneg c hcMem
  have hsq : (M a) ^ 2 ≤ (M c) ^ 2 := by nlinarith
  have hCderiv : 2 * J * (M a) ^ 2 ≤ deriv tau c := by
    calc
      2 * J * (M a) ^ 2 ≤ 2 * J * (M c) ^ 2 := by
        gcongr
      _ ≤ deriv tau c := hderiv c hcMem
  calc
    2 * J * (M a) ^ 2 * (b - a) ≤ deriv tau c * (b - a) := by
      gcongr
    _ = tau b - tau a := by
      rw [hcSlope]
      field_simp





theorem weakSurfaceTensionLowerBound_of_pointwise_tendsto
    (J : ℝ) (M tau : ℝ → ℝ) (tauN : ℕ → ℝ → ℝ)
    (hlim : ∀ beta,
      Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
    (hweak : ∀ n, HasWeakSurfaceTensionLowerBound J M (tauN n)) :
    HasWeakSurfaceTensionLowerBound J M tau := by
  intro a b ha hab
  have hright : Tendsto (fun n => tauN n b - tauN n a) atTop
      (nhds (tau b - tau a)) := (hlim b).sub (hlim a)
  exact ge_of_tendsto hright
    (Filter.Eventually.of_forall fun n => hweak n a b ha hab)



theorem surfaceTensionUpperBound_of_pointwise_tendsto
    (J : ℝ) (M tau : ℝ → ℝ) (tauN : ℕ → ℝ → ℝ)
    (hlim : ∀ beta,
      Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
    (hupper : ∀ n beta, 0 ≤ beta →
      tauN n beta ≤ 2 * J * beta * (M beta) ^ 2) :
    ∀ beta, 0 ≤ beta → tau beta ≤ 2 * J * beta * (M beta) ^ 2 := by
  intro beta hbeta
  exact le_of_tendsto (hlim beta)
    (Filter.Eventually.of_forall fun n => hupper n beta hbeta)




theorem weakSurfaceTensionLowerBound_of_finite_deriv_and_pointwise_tendsto
    (J : ℝ) (M tau : ℝ → ℝ) (tauN : ℕ → ℝ → ℝ)
    (hJ : 0 ≤ J)
    (hMnonneg : ∀ beta, 0 < beta → 0 ≤ M beta)
    (hMmono : MonotoneOn M (Ioi 0))
    (hlim : ∀ beta,
      Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
    (htauNCont : ∀ n, ContinuousOn (tauN n) (Ici 0))
    (htauNDiff : ∀ n, DifferentiableOn ℝ (tauN n) (Ioi 0))
    (hderiv : ∀ n beta, 0 < beta →
      2 * J * (M beta) ^ 2 ≤ deriv (tauN n) beta) :
    HasWeakSurfaceTensionLowerBound J M tau := by
  apply weakSurfaceTensionLowerBound_of_pointwise_tendsto J M tau tauN hlim
  intro n
  exact weakSurfaceTensionLowerBound_of_deriv J M (tauN n) hJ
    hMnonneg hMmono (htauNCont n) (htauNDiff n) (hderiv n)




def HasOrderedMagnetizationRegime (M : ℝ → ℝ) (betaC : ℝ) : Prop :=
  0 < betaC ∧
    (∀ beta, 0 ≤ beta → beta ≤ betaC → M beta = 0) ∧
    (∀ beta, betaC < beta → 0 < M beta)





theorem surfaceTension_pos_iff_ordered_of_weak_bounds
    (J betaC : ℝ) (M tau : ℝ → ℝ)
    (hJ : 0 < J)
    (hregime : HasOrderedMagnetizationRegime M betaC)
    (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
    (hupper : ∀ beta, 0 ≤ beta →
      tau beta ≤ 2 * J * beta * (M beta) ^ 2)
    (hweak : HasWeakSurfaceTensionLowerBound J M tau) :
    ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) := by
  intro beta hbeta
  constructor
  · intro htau
    by_contra hnot
    have hle : beta ≤ betaC := not_lt.mp hnot
    have hMzero := hregime.2.1 beta hbeta hle
    have hup := hupper beta hbeta
    rw [hMzero] at hup
    norm_num at hup
    exact (not_lt_of_ge hup) htau
  · intro hcb
    let a := (betaC + beta) / 2
    have hca : betaC < a := by dsimp [a]; linarith
    have hab : a < beta := by dsimp [a]; linarith
    have ha0 : 0 < a := hregime.1.trans hca
    have hMa : 0 < M a := hregime.2.2 a hca
    have hinc := hweak a beta ha0 hab.le
    have hpositive : 0 < 2 * J * (M a) ^ 2 * (beta - a) := by positivity
    have htauA : 0 ≤ tau a := htauNonneg a ha0.le
    linarith




theorem surfaceTension_pos_iff_ordered_of_deriv
    (J betaC : ℝ) (M tau : ℝ → ℝ)
    (hJ : 0 < J)
    (hregime : HasOrderedMagnetizationRegime M betaC)
    (hMnonneg : ∀ beta, 0 < beta → 0 ≤ M beta)
    (hMmono : MonotoneOn M (Ioi 0))
    (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
    (htauCont : ContinuousOn tau (Ici 0))
    (htauDiff : DifferentiableOn ℝ tau (Ioi 0))
    (hupper : ∀ beta, 0 ≤ beta →
      tau beta ≤ 2 * J * beta * (M beta) ^ 2)
    (hderiv : ∀ beta, 0 < beta →
      2 * J * (M beta) ^ 2 ≤ deriv tau beta) :
    ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) := by
  apply surfaceTension_pos_iff_ordered_of_weak_bounds
    J betaC M tau hJ hregime htauNonneg hupper
  exact weakSurfaceTensionLowerBound_of_deriv J M tau hJ.le
    hMnonneg hMmono htauCont htauDiff hderiv



theorem isingSurfaceTension_pos_iff_ordered_reduction
    (d : ℕ) (J betaC : ℝ) (tau : ℝ → ℝ)
    (hJ : 0 < J)
    (hregime : HasOrderedMagnetizationRegime (magnetization d) betaC)
    (hMnonneg : ∀ beta, 0 < beta → 0 ≤ magnetization d beta)
    (hMmono : MonotoneOn (magnetization d) (Ioi 0))
    (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
    (htauCont : ContinuousOn tau (Ici 0))
    (htauDiff : DifferentiableOn ℝ tau (Ioi 0))
    (hupper : ∀ beta, 0 ≤ beta →
      tau beta ≤ 2 * J * beta * (magnetization d beta) ^ 2)
    (hderiv : ∀ beta, 0 < beta →
      2 * J * (magnetization d beta) ^ 2 ≤ deriv tau beta) :
    ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) :=
  surfaceTension_pos_iff_ordered_of_deriv J betaC (magnetization d) tau
    hJ hregime hMnonneg hMmono htauNonneg htauCont htauDiff hupper hderiv

end StatMech.Ising
