/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetDiscreteContraction





namespace StatMech.FrontierD

open Finset

noncomputable section

theorem sum_fin_eq_zero_of_rev_neg {n : Nat} {f : Fin n → Real}
    (hf : ∀ j, f j.rev = -f j) :
    ∑ j, f j = 0 := by
  have hrev := Equiv.sum_comp Fin.revPerm f
  change (∑ j : Fin n, f j.rev) = ∑ j, f j at hrev
  have hneg : (∑ j : Fin n, f j.rev) = -∑ j, f j := by
    simp_rw [hf, Finset.sum_neg_distrib]
  linarith [hrev]

theorem sixVertexFiniteRootDensity_neg_of_symmetric
    {c : Real} {N n : Nat} {p : Fin n → Real}
    (hp : SixVertexRootSymmetric p) (x : Real) :
    sixVertexFiniteRootDensity c N n p (-x) =
      sixVertexFiniteRootDensity c N n p x := by
  unfold sixVertexFiniteRootDensity
  have hsum :
      (∑ k, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
        sixVertexThetaDerivativeDenominator c (-x) (p k)) =
      ∑ k, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
        sixVertexThetaDerivativeDenominator c x (p k) := by
    calc
      _ = ∑ k : Fin n, 4 * sixVertexDelta c *
          sixVertexBetheIntegratingFactor c (p k.rev) /
            sixVertexThetaDerivativeDenominator c (-x) (p k.rev) := by
        exact (Equiv.sum_comp Fin.revPerm (fun k : Fin n =>
          4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
            sixVertexThetaDerivativeDenominator c (-x) (p k))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hp]
        unfold sixVertexBetheIntegratingFactor
          sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
        simp only [Real.cos_neg, Real.sin_neg]
        ring
  rw [hsum]

theorem sixVertexEvenChargeHalfIndex_rev (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    (sixVertexEvenChargeHalfIndex s k j).rev =
      sixVertexEvenChargeHalfIndex s k j.rev := by
  apply Fin.ext
  simp [sixVertexEvenChargeHalfIndex, Fin.rev]
  have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s) k
  omega

theorem sixVertexOddChargeLowerHalfIndex_rev (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    sixVertexOddChargeLowerHalfIndex s k j.rev =
      (sixVertexOddChargeUpperHalfIndex s k j).rev := by
  apply Fin.ext
  simp [sixVertexOddChargeLowerHalfIndex,
    sixVertexOddChargeUpperHalfIndex, Fin.rev]
  have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k
  omega

theorem sixVertexOddChargeUpperHalfIndex_rev (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    sixVertexOddChargeUpperHalfIndex s k j.rev =
      (sixVertexOddChargeLowerHalfIndex s k j).rev := by
  apply Fin.ext
  simp [sixVertexOddChargeLowerHalfIndex,
    sixVertexOddChargeUpperHalfIndex, Fin.rev]
  have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k
  omega

theorem sixVertexEvenChargeBetheOffset_rev
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexEvenChargeBetheOffset hc s k j.rev =
      -sixVertexEvenChargeBetheOffset hc s k j := by
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let p := sixVertexHalfFilledBetheRoots hc (2 * s + k)
  have hq := (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k).2.1 j
  have hp := (sixVertexHalfFilledBetheRoots_mem_open hc (2 * s + k)).2.1
    (sixVertexEvenChargeHalfIndex s k j)
  change q j.rev = -q j at hq
  change p (sixVertexEvenChargeHalfIndex s k j).rev =
    -p (sixVertexEvenChargeHalfIndex s k j) at hp
  unfold sixVertexEvenChargeBetheOffset
  change (sixVertexFourWidth (2 * s) k : Real) *
      (q j.rev - p (sixVertexEvenChargeHalfIndex s k j.rev)) =
    -((sixVertexFourWidth (2 * s) k : Real) *
      (q j - p (sixVertexEvenChargeHalfIndex s k j)))
  rw [← sixVertexEvenChargeHalfIndex_rev, hq, hp]
  ring

theorem sixVertexOddChargeBetheOffset_rev
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    sixVertexOddChargeBetheOffset hc s k j.rev =
      -sixVertexOddChargeBetheOffset hc s k j := by
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let p := sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
  let il := sixVertexOddChargeLowerHalfIndex s k j
  let iu := sixVertexOddChargeUpperHalfIndex s k j
  have hq := (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s + 1) k).2.1 j
  have hpL := (sixVertexHalfFilledBetheRoots_mem_open hc
    (2 * s + 1 + k)).2.1 il
  have hpU := (sixVertexHalfFilledBetheRoots_mem_open hc
    (2 * s + 1 + k)).2.1 iu
  change q j.rev = -q j at hq
  change p il.rev = -p il at hpL
  change p iu.rev = -p iu at hpU
  unfold sixVertexOddChargeBetheOffset
  change (sixVertexFourWidth (2 * s + 1) k : Real) *
      (q j.rev -
        (p (sixVertexOddChargeLowerHalfIndex s k j.rev) +
          p (sixVertexOddChargeUpperHalfIndex s k j.rev)) / 2) =
    -((sixVertexFourWidth (2 * s + 1) k : Real) *
      (q j - (p il + p iu) / 2))
  rw [hq, sixVertexOddChargeLowerHalfIndex_rev,
    sixVertexOddChargeUpperHalfIndex_rev, hpU, hpL]
  ring



theorem sum_evenChargeWeightedOffsetError_div_weight_density_eq_zero
    {c : Real} (hc : 2 < c) (s k : Nat) {tau : Real → Real}
    (htau : Function.Odd tau) (a : Real) :
    ∑ j, (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k j) *
        sixVertexEvenChargeBetheOffset hc s k j -
        a * tau (sixVertexFixedChargeBetheRoots hc (2 * s) k j)) /
      (sixVertexRootDensityWeight c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k j) *
        sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k j)) = 0 := by
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let rho := sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
    (sixVertexFixedChargeBetheParticleCount (2 * s) k) q
  let eps := sixVertexEvenChargeBetheOffset hc s k
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) → Real :=
    fun j => (rho (q j) * eps j - a * tau (q j)) /
      (sixVertexRootDensityWeight c (q j) * rho (q j))
  change ∑ j, f j = 0
  apply sum_fin_eq_zero_of_rev_neg
  intro j
  have hq := (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k).2.1 j
  have hrho := sixVertexFiniteRootDensity_neg_of_symmetric
    (c := c) (N := sixVertexFourWidth (2 * s) k)
    (p := q) (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k).2.1
    (q j)
  change q j.rev = -q j at hq
  have heps : eps j.rev = -eps j :=
    sixVertexEvenChargeBetheOffset_rev hc s k j
  change rho (-q j) = rho (q j) at hrho
  dsimp [f]
  change (rho (q j.rev) * eps j.rev - a * tau (q j.rev)) /
      (sixVertexRootDensityWeight c (q j.rev) * rho (q j.rev)) = _
  rw [hq, heps, htau,
    sixVertexRootDensityWeight_neg, hrho]
  ring


theorem sum_oddChargeWeightedOffsetError_div_weight_density_eq_zero
    {c : Real} (hc : 2 < c) (s k : Nat) {tau : Real → Real}
    (htau : Function.Odd tau) (a : Real) :
    ∑ j, (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) *
        sixVertexOddChargeBetheOffset hc s k j -
        a * tau (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)) /
      (sixVertexRootDensityWeight c
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) *
        sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)) = 0 := by
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let rho := sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
    (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q
  let eps := sixVertexOddChargeBetheOffset hc s k
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) → Real :=
    fun j => (rho (q j) * eps j - a * tau (q j)) /
      (sixVertexRootDensityWeight c (q j) * rho (q j))
  change ∑ j, f j = 0
  apply sum_fin_eq_zero_of_rev_neg
  intro j
  have hq := (sixVertexFixedChargeBetheRoots_mem_open hc
    (2 * s + 1) k).2.1 j
  have hrho := sixVertexFiniteRootDensity_neg_of_symmetric
    (c := c) (N := sixVertexFourWidth (2 * s + 1) k)
    (p := q) (sixVertexFixedChargeBetheRoots_mem_open hc
      (2 * s + 1) k).2.1 (q j)
  change q j.rev = -q j at hq
  have heps : eps j.rev = -eps j :=
    sixVertexOddChargeBetheOffset_rev hc s k j
  change rho (-q j) = rho (q j) at hrho
  dsimp [f]
  change (rho (q j.rev) * eps j.rev - a * tau (q j.rev)) /
      (sixVertexRootDensityWeight c (q j.rev) * rho (q j.rev)) = _
  rw [hq, heps, htau,
    sixVertexRootDensityWeight_neg, hrho]
  ring

end

end StatMech.FrontierD
