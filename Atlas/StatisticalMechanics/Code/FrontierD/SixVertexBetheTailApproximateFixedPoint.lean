/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailConvolution








namespace StatMech.FrontierD

noncomputable section

theorem abs_finiteRootDensity_continuousEquationResidual_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (x : Real) :
    |sixVertexRootDensityWeight c x *
          sixVertexFiniteRootDensity c N (n + 1) p x -
        (sixVertexRootDensityWeight c x / (2 * Real.pi) -
          (1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              sixVertexRootDensityKernel c x y *
                sixVertexFiniteRootDensity c N (n + 1) p y)| <=
      (sixVertexRootDensityKernelLipschitzBound c *
        sixVertexFiniteRootDensityUniformBound c *
          (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) *
            (2 * Real.pi)) / (2 * Real.pi) := by
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  let S := (∑ j, sixVertexRootDensityKernel c x (p j)) / (N : Real)
  let I := ∫ y in -Real.pi..Real.pi,
    sixVertexRootDensityKernel c x y * rho y
  let E := sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c *
      (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) *
        (2 * Real.pi)
  have hNreal : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : 0 < 2 * Real.pi := by positivity
  have hquad : |S - I| <= E := by
    exact abs_empiricalKernel_sub_finiteDensityIntegral_le_tail
      hc htail hN hhalf hopen hsol x
  have hdisc := sixVertexRootDensityWeight_mul_finiteRootDensity
    hc hN p x
  have hdisc' : sixVertexRootDensityWeight c x * rho x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        S / (2 * Real.pi) := by
    dsimp [rho, S]
    rw [hdisc]
    field_simp [hNreal, Real.pi_ne_zero]
  have hrewrite :
      sixVertexRootDensityWeight c x * rho x -
          (sixVertexRootDensityWeight c x / (2 * Real.pi) -
            (1 / (2 * Real.pi)) * I) =
        (I - S) / (2 * Real.pi) := by
    rw [hdisc']
    ring
  change |sixVertexRootDensityWeight c x * rho x -
      (sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * I)| <= E / (2 * Real.pi)
  rw [hrewrite, abs_div, abs_of_pos hpi]
  exact div_le_div_of_nonneg_right (by simpa [abs_sub_comm] using hquad) hpi.le

end

end StatMech.FrontierD
