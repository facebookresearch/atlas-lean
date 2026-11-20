/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetWeightedResidual









namespace StatMech.FrontierD

open Finset

noncomputable section




theorem abs_empiricalContinuousOffsetKernel_mul_le_of_zeroMass
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    {p : Fin n → Real} {rho e : Fin n → Real} {i : Fin n}
    {E rowBound reciprocalMass : Real}
    (hrho : ∀ j, 0 < rho j)
    (hE : 0 ≤ E) (he : ∀ j, |e j| ≤ E)
    (hmass : (1 / (N : Real)) * ∑ j,
      e j / (sixVertexRootDensityWeight c (p j) * rho j) = 0)
    (hrow : (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p i) (p j) / rho j ≤ rowBound)
    (hreciprocal : reciprocalMass ≤ (1 / (N : Real)) * ∑ j,
      1 / (sixVertexRootDensityWeight c (p j) * rho j)) :
    |(1 / (N : Real)) * ∑ j,
        sixVertexContinuousOffsetKernel c (p i) (p j) / rho j * e j| ≤
      (rowBound -
        sixVertexRootDensityKernelFloor c * reciprocalMass) * E := by
  let floor := sixVertexRootDensityKernelFloor c
  let w : Fin n → Real := fun j => sixVertexRootDensityWeight c (p j)
  let H : Fin n → Real := fun j =>
    (sixVertexRootDensityKernel c (p i) (p j) - floor) / (w j * rho j)
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hfloor : 0 < floor := sixVertexRootDensityKernelFloor_pos hc
  have hw (j : Fin n) : 0 < w j := sixVertexRootDensityWeight_pos hc _
  have hH (j : Fin n) : 0 ≤ H j := by
    exact div_nonneg
      (sub_nonneg.mpr (sixVertexRootDensityKernelFloor_le hc _ _))
      (mul_nonneg (hw j).le (hrho j).le)
  have hkernel (j : Fin n) :
      sixVertexContinuousOffsetKernel c (p i) (p j) / rho j =
        sixVertexRootDensityKernel c (p i) (p j) / (w j * rho j) := by
    unfold sixVertexContinuousOffsetKernel
    dsimp [w]
    field_simp [(hrho j).ne',
      (sixVertexRootDensityWeight_pos hc (p j)).ne']
  have hdecomp :
      (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p i) (p j) / rho j * e j =
        (1 / (N : Real)) * ∑ j, H j * e j := by
    simp_rw [hkernel]
    have hpoint (j : Fin n) :
        sixVertexRootDensityKernel c (p i) (p j) / (w j * rho j) * e j =
          H j * e j + floor *
            (e j / (sixVertexRootDensityWeight c (p j) * rho j)) := by
      dsimp [H, w]
      field_simp [(hrho j).ne',
        (sixVertexRootDensityWeight_pos hc (p j)).ne']
      ring
    have hsum :
        (∑ j, sixVertexRootDensityKernel c (p i) (p j) /
              (w j * rho j) * e j) =
          (∑ j, H j * e j) + floor *
            ∑ j, e j /
              (sixVertexRootDensityWeight c (p j) * rho j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hpoint j
    rw [hsum]
    calc
      (1 / (N : Real)) *
          ((∑ j, H j * e j) + floor * ∑ j,
            e j / (sixVertexRootDensityWeight c (p j) * rho j)) =
        (1 / (N : Real)) * (∑ j, H j * e j) +
          floor * ((1 / (N : Real)) * ∑ j,
            e j / (sixVertexRootDensityWeight c (p j) * rho j)) := by ring
      _ = (1 / (N : Real)) * ∑ j, H j * e j := by
        rw [hmass]
        ring
  rw [hdecomp, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / (N : Real)))]
  calc
    (1 / (N : Real)) * |∑ j, H j * e j| ≤
        (1 / (N : Real)) * ∑ j, |H j * e j| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ = (1 / (N : Real)) * ∑ j, H j * |e j| := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (hH j)]
    _ ≤ (1 / (N : Real)) * ∑ j, H j * E := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (he j) (hH j)
    _ = ((1 / (N : Real)) * ∑ j, H j) * E := by
      rw [show (∑ j, H j * E) = (∑ j, H j) * E by
        rw [Finset.sum_mul]]
      ring
    _ ≤ (rowBound - floor * reciprocalMass) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      have hmassIdentity :
          (1 / (N : Real)) * ∑ j, H j =
            (1 / (N : Real)) * ∑ j,
                sixVertexContinuousOffsetKernel c (p i) (p j) / rho j -
              floor * ((1 / (N : Real)) * ∑ j,
                1 / (sixVertexRootDensityWeight c (p j) * rho j)) := by
        have hpointMass (j : Fin n) :
            H j = sixVertexContinuousOffsetKernel c (p i) (p j) / rho j -
              floor *
                (1 / (sixVertexRootDensityWeight c (p j) * rho j)) := by
          rw [hkernel]
          dsimp [H, w]
          field_simp [(hrho j).ne',
            (sixVertexRootDensityWeight_pos hc (p j)).ne']
        calc
          (1 / (N : Real)) * ∑ j, H j =
              (1 / (N : Real)) * ∑ j,
                (sixVertexContinuousOffsetKernel c (p i) (p j) / rho j -
                  floor * (1 /
                    (sixVertexRootDensityWeight c (p j) * rho j))) := by
                congr 1
                exact Finset.sum_congr rfl fun j _ => hpointMass j
          _ = _ := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
            ring
      rw [hmassIdentity]
      exact sub_le_sub hrow
        (mul_le_mul_of_nonneg_left hreciprocal hfloor.le)

end

end StatMech.FrontierD
