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



theorem discreteOffsetError_le_of_zeroMass
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    {p : Fin n -> Real} {rho e : Fin n -> Real}
    {eta rowBound reciprocalMass : Real}
    (hn : 0 < n)
    (hrho : forall j, 0 < rho j)
    (hmass : (1 / (N : Real)) * ∑ j,
      e j / (sixVertexRootDensityWeight c (p j) * rho j) = 0)
    (hrow : forall i, (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p i) (p j) / rho j <= rowBound)
    (hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ j,
      1 / (sixVertexRootDensityWeight c (p j) * rho j))
    (hdefect : forall i,
      |2 * Real.pi * e i + (1 / (N : Real)) * ∑ j,
        sixVertexContinuousOffsetKernel c (p i) (p j) / rho j * e j| <= eta)
    (hmargin : 0 < 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass)) :
    forall i, |e i| <= eta /
      (2 * Real.pi -
        (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass)) := by
  classical
  let K := rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass
  let margin := 2 * Real.pi - K
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image univ (fun i => |e i|)
    (Finset.univ_nonempty : univ.Nonempty)
  let E := |e imax|
  have hE : 0 <= E := abs_nonneg _
  have he (j : Fin n) : |e j| <= E := hmax j (mem_univ j)
  let I := (1 / (N : Real)) * ∑ j,
    sixVertexContinuousOffsetKernel c (p imax) (p j) / rho j * e j
  have hcontract : |I| <= K * E := by
    exact abs_empiricalContinuousOffsetKernel_mul_le_of_zeroMass
      hc hN hrho hE he hmass (hrow imax) hreciprocal
  have hmain : 2 * Real.pi * E <= eta + K * E := by
    have hpi : 0 <= 2 * Real.pi := by positivity
    calc
      2 * Real.pi * E = |2 * Real.pi * e imax| := by
        rw [abs_mul, abs_of_nonneg hpi]
      _ = |(2 * Real.pi * e imax + I) - I| := by ring_nf
      _ <= |2 * Real.pi * e imax + I| + |I| := abs_sub _ _
      _ <= eta + K * E := add_le_add (hdefect imax) hcontract
  have hEbound : E <= eta / margin := by
    apply (le_div_iff₀ hmargin).2
    dsimp [margin, K]
    linarith
  intro i
  exact (he i).trans hEbound

end

end StatMech.FrontierD
