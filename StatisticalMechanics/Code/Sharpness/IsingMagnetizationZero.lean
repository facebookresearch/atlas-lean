/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Sharpness.IsingSusceptibilityPlus
import Code.Sharpness.BcEqIsing

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators StatMech

namespace StatMech
namespace Sharpness

open Ising Lattice Percolation ConfigSpace
open StatMech.FK

variable {d : ℕ}

private theorem spin_mean_eq_two_spinUp_sub_one
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (x : Site d) :
    (∫ omega, spin omega x ∂mu) =
      2 * mu.real (fmu_multiOpen ({x} : Finset (Site d))) - 1 := by
  have hcoord : Integrable (fun omega => pstc_coordBcf x omega) mu :=
    (pstc_coordBcf x).integrable mu
  calc
    (∫ omega, spin omega x ∂mu) =
        ∫ omega, (2 * pstc_coordBcf x omega - 1) ∂mu := by
      apply integral_congr_ae
      filter_upwards with omega
      by_cases hx : omega x = true <;>
        simp [spin, pstc_coordBcf_apply, hx] <;> norm_num
    _ = 2 * (∫ omega, pstc_coordBcf x omega ∂mu) - 1 := by
      rw [integral_sub (hcoord.const_mul 2) (integrable_const 1),
        integral_const_mul, integral_const]
      simp
    _ = _ := by
      rw [ibs_integral_coordBcf]
      congr 2
      congr 1
      ext omega
      simp [fmu_multiOpen]

private theorem spin_pair_mean_eq_spinUp
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (x y : Site d) :
    (∫ omega, spin omega x * spin omega y ∂mu) =
      4 * mu.real
          (fmu_multiOpen ({x} : Finset (Site d)) ∩
            fmu_multiOpen ({y} : Finset (Site d)))
        - 2 * mu.real (fmu_multiOpen ({x} : Finset (Site d)))
        - 2 * mu.real (fmu_multiOpen ({y} : Finset (Site d))) + 1 := by
  let cx : ConfigSpace (Site d) →ᵇ ℝ := pstc_coordBcf x
  let cy : ConfigSpace (Site d) →ᵇ ℝ := pstc_coordBcf y
  have hcx : Integrable (fun omega => cx omega) mu := cx.integrable mu
  have hcy : Integrable (fun omega => cy omega) mu := cy.integrable mu
  have hcxy : Integrable (fun omega => cx omega * cy omega) mu :=
    (cx * cy).integrable mu
  let A := fmu_multiOpen ({x} : Finset (Site d))
  let B := fmu_multiOpen ({y} : Finset (Site d))
  have hcxy_int : (∫ omega, cx omega * cy omega ∂mu) = mu.real (A ∩ B) := by
    have heq : (fun omega => cx omega * cy omega) =
        (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
      funext omega
      simp only [cx, cy, pstc_coordBcf_apply, A, B]
      by_cases hx : omega x = true <;> by_cases hy : omega y = true <;>
        simp [hx, hy, fmu_multiOpen]
    rw [heq, integral_indicator_const]
    · simp [Measure.real]
    · exact ((ipe_multiOpen_isClopen ({x} : Finset (Site d))).inter
          (ipe_multiOpen_isClopen ({y} : Finset (Site d)))).isClosed.measurableSet
  have hcx_int : (∫ omega, cx omega ∂mu) = mu.real A := by
    rw [show A = {omega : ConfigSpace (Site d) | omega x = true} by
      ext omega; simp [A, fmu_multiOpen]]
    exact ibs_integral_coordBcf x mu
  have hcy_int : (∫ omega, cy omega ∂mu) = mu.real B := by
    rw [show B = {omega : ConfigSpace (Site d) | omega y = true} by
      ext omega; simp [B, fmu_multiOpen]]
    exact ibs_integral_coordBcf y mu
  calc
    (∫ omega, spin omega x * spin omega y ∂mu) =
        ∫ omega, (4 * (cx omega * cy omega) - 2 * cx omega -
          2 * cy omega + 1) ∂mu := by
      apply integral_congr_ae
      filter_upwards with omega
      by_cases hx : omega x = true <;> by_cases hy : omega y = true <;>
        simp [spin, cx, cy, pstc_coordBcf_apply, hx, hy] <;> norm_num
    _ = 4 * (∫ omega, cx omega * cy omega ∂mu)
          - 2 * (∫ omega, cx omega ∂mu)
          - 2 * (∫ omega, cy omega ∂mu) + 1 := by
      have hsub1 : Integrable
          (fun omega => 4 * (cx omega * cy omega) - 2 * cx omega) mu :=
        (hcxy.const_mul 4).sub (hcx.const_mul 2)
      have hsub2 : Integrable
          (fun omega => 4 * (cx omega * cy omega) - 2 * cx omega -
            2 * cy omega) mu := hsub1.sub (hcy.const_mul 2)
      rw [integral_add hsub2 (integrable_const 1),
        integral_sub hsub1 (hcy.const_mul 2),
        integral_sub (hcxy.const_mul 4) (hcx.const_mul 2),
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const]
      simp
    _ = _ := by rw [hcxy_int, hcx_int, hcy_int]


theorem magnetization_sq_le_plusCorr (beta : ℝ) (hbeta : 0 ≤ beta)
    (x y : Site d) :
    magnetization d beta ^ 2 ≤ plusCorr d beta x y := by
  let mu : Measure (ConfigSpace (Site d)) := plusState d beta 0
  haveI : IsProbabilityMeasure mu := (plusState d beta 0).2
  let A := fmu_multiOpen ({x} : Finset (Site d))
  let B := fmu_multiOpen ({y} : Finset (Site d))
  have hfkg : mu.real A * mu.real B ≤ mu.real (A ∩ B) := by
    simpa [mu, A, B] using
      ipe_plusState_fkg_multiOpen (d := d) hbeta 0
        ({x} : Finset (Site d)) ({y} : Finset (Site d))
  have hmx : (∫ omega, spin omega x ∂mu) = magnetization d beta := by
    let g : Multiplicative (Site d) := Multiplicative.ofAdd x
    have hti := iptp_plusState_isTranslationInvariant (d := d) hbeta
      (by norm_num : (0 : ℝ) ≤ 0)
    calc
      (∫ omega, spin omega x ∂mu) =
          ∫ omega, spin omega x ∂Measure.map (ConfigSpace.shift g) mu := by
            rw [hti.map_eq g]
      _ = ∫ omega, spin (ConfigSpace.shift g omega) x ∂mu := by
        change (∫ omega, spinBCF x omega ∂Measure.map (ConfigSpace.shift g) mu) = _
        rw [integral_map (continuous_shift g).measurable.aemeasurable
          (spinBCF x).continuous.aestronglyMeasurable]
        simp only [spinBCF_apply]
      _ = ∫ omega, spin omega (Percolation.origin d) ∂mu := by
        apply integral_congr_ae
        filter_upwards with omega
        have hxg : g • Percolation.origin d = x := by
          ext i
          simp [g, Percolation.origin]
        rw [← hxg, iptp_spin_shift]
      _ = magnetization d beta := rfl
  have hmy : (∫ omega, spin omega y ∂mu) = magnetization d beta := by
    let g : Multiplicative (Site d) := Multiplicative.ofAdd y
    have hti := iptp_plusState_isTranslationInvariant (d := d) hbeta
      (by norm_num : (0 : ℝ) ≤ 0)
    calc
      (∫ omega, spin omega y ∂mu) =
          ∫ omega, spin omega y ∂Measure.map (ConfigSpace.shift g) mu := by
            rw [hti.map_eq g]
      _ = ∫ omega, spin (ConfigSpace.shift g omega) y ∂mu := by
        change (∫ omega, spinBCF y omega ∂Measure.map (ConfigSpace.shift g) mu) = _
        rw [integral_map (continuous_shift g).measurable.aemeasurable
          (spinBCF y).continuous.aestronglyMeasurable]
        simp only [spinBCF_apply]
      _ = ∫ omega, spin omega (Percolation.origin d) ∂mu := by
        apply integral_congr_ae
        filter_upwards with omega
        have hyg : g • Percolation.origin d = y := by
          ext i
          simp [g, Percolation.origin]
        rw [← hyg, iptp_spin_shift]
      _ = magnetization d beta := rfl
  have hxid := spin_mean_eq_two_spinUp_sub_one mu x
  have hyid := spin_mean_eq_two_spinUp_sub_one mu y
  have hxyid := spin_pair_mean_eq_spinUp mu x y
  rw [hmx] at hxid
  rw [hmy] at hyid
  unfold plusCorr
  change (magnetization d beta) ^ 2 ≤ ∫ omega, spin omega x * spin omega y ∂mu
  calc
    magnetization d beta ^ 2 =
        (2 * mu.real A - 1) * (2 * mu.real B - 1) := by
      rw [← hxid, ← hyid]
      ring
    _ ≤ 4 * mu.real (A ∩ B) - 2 * mu.real A - 2 * mu.real B + 1 := by
      nlinarith [hfkg]
    _ = ∫ omega, spin omega x * spin omega y ∂mu := hxyid.symm

private theorem site_ray_injective (hd : 1 ≤ d) :
    ∃ e : Site d, e ≠ 0 ∧ Function.Injective (fun n : ℕ => n • e) := by
  let i : Fin d := ⟨0, hd⟩
  let e : Site d := fun j => if j = i then 1 else 0
  have he : e ≠ 0 := by
    intro h
    have := congrFun h i
    simp [e] at this
  refine ⟨e, he, ?_⟩
  intro n m hnm
  have hcoord := congrFun hnm i
  change (n : ℤ) * e i = (m : ℤ) * e i at hcoord
  simp [e] at hcoord
  exact_mod_cast hcoord


theorem magnetization_eq_zero_of_plusCorr_summable
    (hd : 1 ≤ d) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsum : Summable (plusCorr d beta (Percolation.origin d))) :
    magnetization d beta = 0 := by
  obtain ⟨e, _he, hinj⟩ := site_ray_injective (d := d) hd
  have hseq : Summable
      (fun n : ℕ => plusCorr d beta (Percolation.origin d) (n • e)) := by
    simpa only [Function.comp_apply] using hsum.comp_injective hinj
  have hzero := hseq.tendsto_atTop_zero
  have hlower : ∀ n : ℕ,
      magnetization d beta ^ 2 ≤
        plusCorr d beta (Percolation.origin d) (n • e) :=
    fun n => magnetization_sq_le_plusCorr beta hbeta _ _
  have hsquare : magnetization d beta ^ 2 ≤ 0 :=
    ge_of_tendsto hzero (Filter.Eventually.of_forall hlower)
  nlinarith [sq_nonneg (magnetization d beta)]





theorem bc_eq_ising_of_sqrt_and_susceptibility
    (hd : 1 ≤ d)
    (hsqrt : ∀ beta, tildeBetaCIsing d ≤ beta →
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
        magnetization d beta) :
    betaC d = tildeBetaCIsing d := by
  have hpos : ∀ beta, tildeBetaCIsing d < beta →
      0 < magnetization d beta :=
    posMag_of_meanfield_sqrt_nonneg (d := d) hsqrt
  have hbdd : BddBelow (positiveMagnetizationSet d) := by
    refine ⟨0, ?_⟩
    show ∀ beta ∈ positiveMagnetizationSet d, 0 ≤ beta
    intro beta hbeta
    exact (mem_positiveMagnetizationSet.mp hbeta).1
  have hne : (positiveMagnetizationSet d).Nonempty := by
    refine ⟨tildeBetaCIsing d + 1, ?_⟩
    show tildeBetaCIsing d + 1 ∈ positiveMagnetizationSet d
    rw [mem_positiveMagnetizationSet]
    exact ⟨by linarith [tildeBetaCIsing_nonneg (d := d)],
      hpos _ (by linarith)⟩
  apply le_antisymm (bc_le_tildeBc_ising hbdd hpos)
  unfold betaC
  apply le_csInf hne
  intro beta hbeta
  change 0 ≤ beta ∧ 0 < magnetization d beta at hbeta
  by_contra hnot
  have hlt : beta < tildeBetaCIsing d := lt_of_not_ge hnot
  have hbeta' := mem_positiveMagnetizationSet.mp hbeta
  obtain ⟨_S, _ho, _hphi, hsum⟩ :=
    finite_susceptibility_of_lt_tildeBetaCIsing hbeta'.1 hlt
  have hz := magnetization_eq_zero_of_plusCorr_summable hd beta hbeta'.1 hsum
  rw [hz] at hbeta'
  exact (lt_irrefl 0 hbeta'.2).elim

end Sharpness
end StatMech

