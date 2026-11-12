/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetTaylor





namespace StatMech.FrontierD

open Finset

noncomputable section


def sixVertexEvenChargeAlignedHalfRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) → Real :=
  fun j => sixVertexHalfFilledBetheRoots hc (2 * s + k)
    (sixVertexEvenChargeHalfIndex s k j)



def sixVertexEvenChargeOffsetBoundarySource
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) : Real :=
  (∑ l, sixVertexTheta c
      (sixVertexEvenChargeAlignedHalfRoots hc s k j)
      (sixVertexHalfFilledBetheRoots hc (2 * s + k) l)) -
    ∑ l, sixVertexTheta c
      (sixVertexEvenChargeAlignedHalfRoots hc s k j)
      (sixVertexEvenChargeAlignedHalfRoots hc s k l)



def sixVertexEvenChargeOffsetNodalResidual
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) : Real :=
  let N : Real := sixVertexFourWidth (2 * s) k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let eps := sixVertexEvenChargeBetheOffset hc s k
  eps j - sixVertexEvenChargeOffsetBoundarySource hc s k j +
    (1 / N) * ∑ l, (
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)

theorem sixVertexEvenChargeBetheOffset_eq_boundary_add_commonDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexEvenChargeBetheOffset hc s k j =
      sixVertexEvenChargeOffsetBoundarySource hc s k j +
        ∑ l, (sixVertexTheta c
          (sixVertexEvenChargeAlignedHalfRoots hc s k j)
          (sixVertexEvenChargeAlignedHalfRoots hc s k l) -
        sixVertexTheta c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k j)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k l)) := by
  rw [sixVertexEvenChargeBetheOffset_eq_thetaDifference]
  unfold sixVertexEvenChargeOffsetBoundarySource
    sixVertexEvenChargeAlignedHalfRoots
  rw [Finset.sum_sub_distrib]
  ring



theorem abs_sixVertexEvenChargeOffsetNodalResidual_le
    {c : Real} (hc : 2 < c) (s k : Nat) {B : Real} (hB : 0 ≤ B)
    (hoffset : ∀ j, |sixVertexEvenChargeBetheOffset hc s k j| ≤ B)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    |sixVertexEvenChargeOffsetNodalResidual hc s k j| ≤
      4 * sixVertexThetaTaylorBound c * B ^ 2 /
        sixVertexFourWidth (2 * s) k := by
  let N := sixVertexFourWidth (2 * s) k
  let n := sixVertexFixedChargeBetheParticleCount (2 * s) k
  let p := sixVertexEvenChargeAlignedHalfRoots hc s k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let eps := sixVertexEvenChargeBetheOffset hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hn : n ≤ N := by
    have htwice := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k
    dsimp [n, N]
    omega
  have hoffset' : ∀ l, |(N : Real) * (q l - p l)| ≤ B := by
    intro l
    simpa [N, q, p, eps, sixVertexEvenChargeAlignedHalfRoots,
      sixVertexEvenChargeBetheOffset] using hoffset l
  have htaylor := abs_sum_sixVertexTheta_sub_linearization_le
    hc hN hn hB hoffset' j
  let R : Fin n → Real := fun l =>
    sixVertexTheta c (p j) (p l) - sixVertexTheta c (q j) (q l) -
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) *
            (p j - q j) +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) *
            (p l - q l))
  change |∑ l, R l| ≤ 4 * sixVertexThetaTaylorBound c * B ^ 2 / N at htaylor
  have hNreal : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hpoint (l : Fin n) :
      p l - q l = -(eps l) / N := by
    change p l - q l = -((N : Real) * (q l - p l)) / N
    field_simp [hNreal]
    ring
  have hcommon : eps j - sixVertexEvenChargeOffsetBoundarySource hc s k j =
      ∑ l, (sixVertexTheta c (p j) (p l) -
        sixVertexTheta c (q j) (q l)) := by
    have h := sixVertexEvenChargeBetheOffset_eq_boundary_add_commonDifference
      hc s k j
    change eps j = sixVertexEvenChargeOffsetBoundarySource hc s k j +
      ∑ l, (sixVertexTheta c (p j) (p l) -
        sixVertexTheta c (q j) (q l)) at h
    linarith
  have hresidual : sixVertexEvenChargeOffsetNodalResidual hc s k j =
      ∑ l, R l := by
    change eps j - sixVertexEvenChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
      ∑ l, R l
    rw [hcommon, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    dsimp [R]
    rw [hpoint j, hpoint l]
    field_simp [hNreal]
    ring
  rw [hresidual]
  exact htaylor


def sixVertexOddChargeAlignedHalfRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) → Real :=
  fun j =>
    (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
          (sixVertexOddChargeLowerHalfIndex s k j) +
        sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
          (sixVertexOddChargeUpperHalfIndex s k j)) / 2



def sixVertexOddChargeOffsetBoundarySource
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) : Real :=
  let pl := sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
  ((∑ l, sixVertexTheta c
        (pl (sixVertexOddChargeLowerHalfIndex s k j)) (pl l)) +
      (∑ l, sixVertexTheta c
        (pl (sixVertexOddChargeUpperHalfIndex s k j)) (pl l))) / 2 -
    ∑ l, sixVertexTheta c
      (sixVertexOddChargeAlignedHalfRoots hc s k j)
      (sixVertexOddChargeAlignedHalfRoots hc s k l)


def sixVertexOddChargeOffsetNodalResidual
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) : Real :=
  let N : Real := sixVertexFourWidth (2 * s + 1) k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let eps := sixVertexOddChargeBetheOffset hc s k
  eps j - sixVertexOddChargeOffsetBoundarySource hc s k j +
    (1 / N) * ∑ l, (
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)

theorem sixVertexOddChargeBetheOffset_eq_boundary_add_commonDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    sixVertexOddChargeBetheOffset hc s k j =
      sixVertexOddChargeOffsetBoundarySource hc s k j +
        ∑ l, (sixVertexTheta c
          (sixVertexOddChargeAlignedHalfRoots hc s k j)
          (sixVertexOddChargeAlignedHalfRoots hc s k l) -
        sixVertexTheta c
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)) := by
  rw [sixVertexOddChargeBetheOffset_eq_thetaDifference]
  unfold sixVertexOddChargeOffsetBoundarySource
  dsimp only
  rw [Finset.sum_sub_distrib]
  ring



theorem abs_sixVertexOddChargeOffsetNodalResidual_le
    {c : Real} (hc : 2 < c) (s k : Nat) {B : Real} (hB : 0 ≤ B)
    (hoffset : ∀ j, |sixVertexOddChargeBetheOffset hc s k j| ≤ B)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    |sixVertexOddChargeOffsetNodalResidual hc s k j| ≤
      4 * sixVertexThetaTaylorBound c * B ^ 2 /
        sixVertexFourWidth (2 * s + 1) k := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := sixVertexFixedChargeBetheParticleCount (2 * s + 1) k
  let p := sixVertexOddChargeAlignedHalfRoots hc s k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let eps := sixVertexOddChargeBetheOffset hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hn : n ≤ N := by
    have htwice := sixVertexFixedChargeBetheParticleCount_twice_le
      (2 * s + 1) k
    dsimp [n, N]
    omega
  have hoffset' : ∀ l, |(N : Real) * (q l - p l)| ≤ B := by
    intro l
    simpa [N, q, p, eps, sixVertexOddChargeAlignedHalfRoots,
      sixVertexOddChargeBetheOffset] using hoffset l
  have htaylor := abs_sum_sixVertexTheta_sub_linearization_le
    hc hN hn hB hoffset' j
  let R : Fin n → Real := fun l =>
    sixVertexTheta c (p j) (p l) - sixVertexTheta c (q j) (q l) -
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) *
            (p j - q j) +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) *
            (p l - q l))
  change |∑ l, R l| ≤ 4 * sixVertexThetaTaylorBound c * B ^ 2 / N at htaylor
  have hNreal : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hpoint (l : Fin n) :
      p l - q l = -(eps l) / N := by
    change p l - q l = -((N : Real) * (q l - p l)) / N
    field_simp [hNreal]
    ring
  have hcommon : eps j - sixVertexOddChargeOffsetBoundarySource hc s k j =
      ∑ l, (sixVertexTheta c (p j) (p l) -
        sixVertexTheta c (q j) (q l)) := by
    have h := sixVertexOddChargeBetheOffset_eq_boundary_add_commonDifference
      hc s k j
    change eps j = sixVertexOddChargeOffsetBoundarySource hc s k j +
      ∑ l, (sixVertexTheta c (p j) (p l) -
        sixVertexTheta c (q j) (q l)) at h
    linarith
  have hresidual : sixVertexOddChargeOffsetNodalResidual hc s k j =
      ∑ l, R l := by
    change eps j - sixVertexOddChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
      ∑ l, R l
    rw [hcommon, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    dsimp [R]
    rw [hpoint j, hpoint l]
    field_simp [hNreal]
    ring
  rw [hresidual]
  exact htaylor



theorem abs_sixVertexEvenChargeOffsetNodalResidual_le_of_densityClose
    {c : Real} (hc : 2 < c) (s k : Nat)
    {rho : Real → Real} {EP EQ lower : Real}
    (hEP : 0 ≤ EP) (hEQ : 0 ≤ EQ) (hlower : 0 < lower)
    (hfixedLower : ∀ x, lower ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) x)
    (hhalfClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          ((2 * s + k + 1) + (2 * s + k + 1))
          (sixVertexHalfFilledBetheRoots hc (2 * s + k)) y - rho y)| ≤
        EP / sixVertexFourWidth (2 * s) k)
    (hfixedClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k) y - rho y)| ≤
        EQ / sixVertexFourWidth (2 * s) k)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    |sixVertexEvenChargeOffsetNodalResidual hc s k j| ≤
      4 * sixVertexThetaTaylorBound c *
        ((((EP + EQ) /
          ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c)) / lower) * Real.pi) ^ 2 /
          sixVertexFourWidth (2 * s) k := by
  let K := ((EP + EQ) /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)) / lower
  let B := K * Real.pi
  have hK : 0 ≤ K := by
    dsimp [K]
    have hwmin : 0 < (sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c := div_pos
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
    exact div_nonneg (div_nonneg (add_nonneg hEP hEQ) hwmin.le) hlower.le
  have hB : 0 ≤ B := mul_nonneg hK Real.pi_pos.le
  have hoffset : ∀ l, |sixVertexEvenChargeBetheOffset hc s k l| ≤ B := by
    intro l
    have hlin := abs_sixVertexEvenChargeBetheOffset_le_mul_abs_halfRoot
      hc s k hEP hEQ hlower hfixedLower hhalfClose hfixedClose l
    have hroot := (sixVertexHalfFilledBetheRoots_mem_open hc (2 * s + k)).2.2
      (sixVertexEvenChargeHalfIndex s k l)
    have habs : |sixVertexHalfFilledBetheRoots hc (2 * s + k)
        (sixVertexEvenChargeHalfIndex s k l)| ≤ Real.pi :=
      abs_le.mpr ⟨hroot.1.le, hroot.2.le⟩
    exact hlin.trans (mul_le_mul_of_nonneg_left habs hK)
  simpa [B, K] using
    abs_sixVertexEvenChargeOffsetNodalResidual_le hc s k hB hoffset j



theorem abs_sixVertexOddChargeOffsetNodalResidual_le_of_densityClose
    {c : Real} (hc : 2 < c) (s k : Nat)
    {rho : Real → Real} {EP EQ lowerP lowerQ : Real}
    (hEP : 0 ≤ EP) (hEQ : 0 ≤ EQ)
    (hlowerP : 0 < lowerP) (hlowerQ : 0 < lowerQ)
    (hhalfLower : ∀ x, lowerP ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) x)
    (hfixedLower : ∀ x, lowerQ ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) x)
    (hhalfClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
          (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) y - rho y)| ≤
        EP / sixVertexFourWidth (2 * s + 1) k)
    (hfixedClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) y - rho y)| ≤
        EQ / sixVertexFourWidth (2 * s + 1) k)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    |sixVertexOddChargeOffsetNodalResidual hc s k j| ≤
      4 * sixVertexThetaTaylorBound c *
        (((((EP + EQ) /
            ((sixVertexAnisotropyMagnitude c - 1) /
              sixVertexRootDensityScale c)) / lowerQ) * Real.pi +
          (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
            (4 * lowerP ^ 2 * lowerQ)) ^ 2) /
        sixVertexFourWidth (2 * s + 1) k := by
  let K := ((EP + EQ) /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)) / lowerQ
  let E := (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
    (4 * lowerP ^ 2 * lowerQ)
  let B := K * Real.pi + E
  have hK : 0 ≤ K := by
    dsimp [K]
    have hwmin : 0 < (sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c := div_pos
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
    exact div_nonneg (div_nonneg (add_nonneg hEP hEQ) hwmin.le) hlowerQ.le
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hK Real.pi_pos.le) hE
  have hNreal : (1 : Real) ≤ sixVertexFourWidth (2 * s + 1) k := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k)
  have hoffset : ∀ l, |sixVertexOddChargeBetheOffset hc s k l| ≤ B := by
    intro l
    have hlin :=
      abs_sixVertexOddChargeBetheOffset_le_mul_abs_halfAverage_add
        hc s k hEP hEQ hlowerP hlowerQ hhalfLower hfixedLower
        hhalfClose hfixedClose l
    let pl := sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
      (sixVertexOddChargeLowerHalfIndex s k l)
    let pu := sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
      (sixVertexOddChargeUpperHalfIndex s k l)
    have hpl := (sixVertexHalfFilledBetheRoots_mem_open hc
      (2 * s + 1 + k)).2.2 (sixVertexOddChargeLowerHalfIndex s k l)
    have hpu := (sixVertexHalfFilledBetheRoots_mem_open hc
      (2 * s + 1 + k)).2.2 (sixVertexOddChargeUpperHalfIndex s k l)
    have havg : |(pl + pu) / 2| ≤ Real.pi := by
      rw [abs_le]
      constructor <;> dsimp [pl, pu] <;> linarith
    have hmidterm :
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
            (4 * lowerP ^ 2 * lowerQ * sixVertexFourWidth (2 * s + 1) k) ≤
          E := by
      dsimp [E]
      have hnum : 0 ≤ (sixVertexFiniteRootDensityLipschitzConstant c : Real) :=
        NNReal.coe_nonneg _
      apply div_le_div_of_nonneg_left hnum
      · positivity
      · have hdenpos : 0 < 4 * lowerP ^ 2 * lowerQ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hNreal hdenpos.le]
    exact hlin.trans (add_le_add
      (mul_le_mul_of_nonneg_left havg hK) hmidterm)
  simpa [B, K, E] using
    abs_sixVertexOddChargeOffsetNodalResidual_le hc s k hB hoffset j

end

end StatMech.FrontierD
