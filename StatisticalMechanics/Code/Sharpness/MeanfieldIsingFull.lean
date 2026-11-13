/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Sharpness.MeanfieldIsing
import Code.Sharpness.TildeBc
import Code.Sharpness.MeanfieldIsingFinite

open MeasureTheory Real Set Filter Topology

namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising







variable {d : ℕ}







theorem si4_phiIsing_ge_one_above_tildeBc (d : ℕ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hbdd : BddAbove (tildeBetaCIsingSet d)) (hβ : tildeBetaCIsing d < β) :
    ∀ S : Finset (Site d), origin d ∈ S → 1 ≤ phiIsing d β S := by
  intro S hS
  by_contra h
  rw [not_le] at h
  
  
  have hmem : β ∈ tildeBetaCIsingSet d := ⟨hβ0, S, hS, h⟩
  have hle := le_csSup hbdd hmem
  unfold tildeBetaCIsing at hβ
  linarith

















theorem si4_mfd_drop_infphi (β infφ cn un εn : ℝ) (hβ : 0 < β) (hcn : 0 ≤ cn)
    (hinf : 1 ≤ infφ) (hun : un ≤ 1) :
    2 * cn * ((1 / β) * (1 - un) - εn) ≤ 2 * cn * ((1 / β) * (infφ * (1 - un)) - εn) := by
  have hβnn : (0 : ℝ) ≤ 1 / β := by positivity
  have h2cn : (0 : ℝ) ≤ 2 * cn := by linarith
  apply mul_le_mul_of_nonneg_left _ h2cn
  have hstep : (1 / β) * (1 - un) ≤ (1 / β) * (infφ * (1 - un)) := by
    apply mul_le_mul_of_nonneg_left _ hβnn
    nlinarith [sub_nonneg.mpr hun]
  linarith
















theorem si4_mfd_limit_passage (β infφ : ℝ) (hβ : 0 < β) (hinf : 1 ≤ infφ) (u u' : ℝ)
    (un un' cn εn : ℕ → ℝ)
    (hun : Tendsto un atTop (𝓝 u)) (hun' : Tendsto un' atTop (𝓝 u'))
    (hcn : Tendsto cn atTop (𝓝 1)) (hεn : Tendsto εn atTop (𝓝 0))
    (hcnn : ∀ n, 0 ≤ cn n) (hunle : ∀ n, un n ≤ 1)
    (hfin : ∀ n, 2 * cn n * ((1 / β) * (infφ * (1 - un n)) - εn n) ≤ un' n) :
    (2 / β) * (1 - u) ≤ u' := by
  
  have hdrop : ∀ n, 2 * cn n * ((1 / β) * (1 - un n) - εn n) ≤ un' n := fun n =>
    le_trans (si4_mfd_drop_infphi β infφ (cn n) (un n) (εn n) hβ (hcnn n) hinf (hunle n))
      (hfin n)
  
  have hlhs : Tendsto (fun n => 2 * cn n * ((1 / β) * (1 - un n) - εn n)) atTop
      (𝓝 (2 * 1 * ((1 / β) * (1 - u) - 0))) := by
    apply Tendsto.mul
    · exact Tendsto.mul tendsto_const_nhds hcn
    · exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub hun)).sub hεn
  have hlim : (2 / β) * (1 - u) = 2 * 1 * ((1 / β) * (1 - u) - 0) := by ring
  rw [hlim]
  exact le_of_tendsto_of_tendsto' hlhs hun' hdrop































theorem si4_meanfield_lower_bound_of_finiteVolume (β₀ : ℝ) (hβ₀ : 0 < β₀) (m : ℝ → ℝ)
    (infφ : ℝ) (hinf : 1 ≤ infφ)
    (un un' cn εn : ℝ → ℕ → ℝ)
    (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
    (hzero : m β₀ = 0) (hnonneg : ∀ β ∈ Ici β₀, 0 ≤ m β)
    (hu : ∀ β ∈ Ioi β₀, Tendsto (un β) atTop (𝓝 ((m β) ^ 2)))
    (hderiv : ∀ β ∈ Ioi β₀, Tendsto (un' β) atTop (𝓝 (deriv (fun β => (m β) ^ 2) β)))
    (hc : ∀ β ∈ Ioi β₀, Tendsto (cn β) atTop (𝓝 1))
    (hε : ∀ β ∈ Ioi β₀, Tendsto (εn β) atTop (𝓝 0))
    (hcnn : ∀ β ∈ Ioi β₀, ∀ n, 0 ≤ cn β n)
    (hunle : ∀ β ∈ Ioi β₀, ∀ n, un β n ≤ 1)
    (hfin : ∀ β ∈ Ioi β₀, ∀ n,
      2 * cn β n * ((1 / β) * (infφ * (1 - un β n)) - εn β n) ≤ un' β n)
    {β : ℝ} (hβ : β₀ ≤ β) :
    Real.sqrt (1 - (β₀ / β) ^ 2) ≤ m β := by
  
  have hineq : ∀ β ∈ Ioi β₀,
      (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β := by
    intro β hβint
    have hβpos : 0 < β := lt_trans hβ₀ (mem_Ioi.mp hβint)
    exact si4_mfd_limit_passage β infφ hβpos hinf ((m β) ^ 2)
      (deriv (fun β => (m β) ^ 2) β) (un β) (un' β) (cn β) (εn β)
      (hu β hβint) (hderiv β hβint) (hc β hβint) (hε β hβint)
      (hcnn β hβint) (hunle β hβint) (hfin β hβint)
  
  exact meanfield_lower_bound β₀ hβ₀ m hdiff hineq hzero hnonneg hβ





theorem meanfield_lower_bound_of_initial_nonneg
    (β₀ : ℝ) (hβ₀ : 0 < β₀) (m : ℝ → ℝ)
    (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
    (hineq : ∀ β ∈ Ioi β₀,
      (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β)
    (hnonneg : ∀ β ∈ Ici β₀, 0 ≤ m β)
    {β : ℝ} (hβ : β₀ ≤ β) :
    Real.sqrt (1 - (β₀ / β) ^ 2) ≤ m β := by
  have hβpos : 0 < β := lt_of_lt_of_le hβ₀ hβ
  have hgw := meanfield_one_minus_le β₀ hβ₀ (fun β => (m β) ^ 2)
    hdiff hineq hβ
  have hinit0 := hnonneg β₀ (mem_Ici.mpr le_rfl)
  have hratio0 : 0 ≤ (β₀ / β) ^ 2 := sq_nonneg _
  have h2 : 1 - (β₀ / β) ^ 2 ≤ (m β) ^ 2 := by
    have hfactor : (β₀ / β) ^ 2 * (1 - (m β₀) ^ 2) ≤
        (β₀ / β) ^ 2 := by
      nlinarith [sq_nonneg (m β₀)]
    linarith
  calc
    Real.sqrt (1 - (β₀ / β) ^ 2)
        ≤ Real.sqrt ((m β) ^ 2) := Real.sqrt_le_sqrt h2
    _ = m β := Real.sqrt_sq (hnonneg β (mem_Ici.mpr hβ))









noncomputable def sctInfiniteFieldMag (d : ℕ) (beta h : ℝ) : ℝ :=
  ⨆ n : ℕ, sctOriginMag d beta h n





theorem sct_infiniteField_meanfield_inequality_of_deriv_tendsto
    (d : ℕ) (beta h : ℝ)
    (hbdd : BddAbove (tildeBetaCIsingSet d))
    (habove : tildeBetaCIsing d < beta) (hh : 0 < h)
    (hderiv : Tendsto
      (fun n : ℕ => deriv
        (fun b => (sctOriginMag d b h (n + 1)) ^ 2) beta)
      atTop
      (nhds (deriv (fun b => (sctInfiniteFieldMag d b h) ^ 2) beta))) :
    (2 / beta) * (1 - (sctInfiniteFieldMag d beta h) ^ 2) ≤
      deriv (fun b => (sctInfiniteFieldMag d b h) ^ 2) beta := by
  have hzero : (0 : ℝ) ∈ tildeBetaCIsingSet d := by
    refine ⟨le_rfl, {origin d}, by simp, ?_⟩
    simp [phiIsing]
  have htc0 : 0 ≤ tildeBetaCIsing d := by
    unfold tildeBetaCIsing
    exact le_csSup hbdd hzero
  have hbeta : 0 < beta := lt_of_le_of_lt htc0 habove
  have hphi : ∀ S : Finset (Site d), origin d ∈ S →
      1 ≤ phiIsing d beta S :=
    si4_phiIsing_ge_one_above_tildeBc d beta hbeta.le hbdd habove
  let un : ℕ → ℝ := fun n => (sctOriginMag d beta h (n + 1)) ^ 2
  let un' : ℕ → ℝ := fun n =>
    deriv (fun b => (sctOriginMag d b h (n + 1)) ^ 2) beta
  let cn : ℕ → ℝ := fun n => sctLatticeC d beta h (n + 1)
  let epsn : ℕ → ℝ := fun n =>
    sctBoundaryCovarianceError d beta h (n + 1)
  have hmag := sctOriginMag_tendsto_iSup d beta h hbeta.le hh.le
  have hun : Tendsto un atTop
      (nhds ((sctInfiniteFieldMag d beta h) ^ 2)) := by
    exact (hmag.comp (tendsto_add_atTop_nat 1)).pow 2
  have hcn : Tendsto cn atTop (nhds 1) := by
    exact (sctLatticeC_tendsto_one d beta h hbeta hh).comp
      (tendsto_add_atTop_nat 1)
  have heps : Tendsto epsn atTop (nhds 0) := by
    exact (sctBoundaryCovarianceError_tendsto_zero d beta h hbeta hh).comp
      (tendsto_add_atTop_nat 1)
  apply si4_mfd_limit_passage beta 1 hbeta (le_refl 1)
    ((sctInfiniteFieldMag d beta h) ^ 2)
    (deriv (fun b => (sctInfiniteFieldMag d b h) ^ 2) beta)
    un un' cn epsn hun hderiv hcn heps
  · intro n
    exact sctLatticeC_nonneg beta h hbeta hh
  · intro n
    have hm0 : 0 ≤ sctOriginMag d beta h (n + 1) :=
      (sctOriginMag_pos d beta h hbeta hh (n + 1)).le
    have hm1 : sctOriginMag d beta h (n + 1) ≤ 1 :=
      sctOriginMag_le_one d beta h (n + 1)
    dsimp [un]
    nlinarith
  · intro n
    exact sct_finite_meanfield_inequality_concrete beta h 1
      (Nat.succ_le_succ (Nat.zero_le n)) hbeta hh hphi

end Sharpness

end StatMech
