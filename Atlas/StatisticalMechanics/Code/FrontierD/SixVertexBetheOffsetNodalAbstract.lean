/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetDiscreteStability









namespace StatMech.FrontierD

open Finset

noncomputable section

theorem abs_densityOffset_sub_continuous_le_of_data
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : 0 < n)
    {p : Fin n -> Real} {rho eps : Fin n -> Real}
    {a : Real} (ha : 0 <= a) {tau : Real -> Real}
    {aligned : Fin n -> Real} {boundary residual : Fin n -> Real}
    {rowBound reciprocalMass residualError boundaryError sourceMoveError
      testError : Real}
    (hrho : forall j, 0 < rho j)
    (hpIcc : forall j, p j ∈ Set.Icc (-Real.pi) Real.pi)
    (hmass : (1 / (N : Real)) * ∑ j,
      (rho j * eps j - a * tau (p j)) /
        (sixVertexRootDensityWeight c (p j) * rho j) = 0)
    (hrow : forall i, (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p i) (p j) / rho j <= rowBound)
    (hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ j,
      1 / (sixVertexRootDensityWeight c (p j) * rho j))
    (hlinear : forall i,
      2 * Real.pi * (rho i * eps i) + (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p i) (p j) * eps j =
        residual i + boundary i)
    (hresidual : forall i, |residual i| <= residualError)
    (hboundary : forall i,
      |boundary i - a * sixVertexContinuousOffsetSource c (aligned i)| <=
        boundaryError)
    (hsourceMove : forall i,
      |a * (sixVertexContinuousOffsetSource c (aligned i) -
        sixVertexContinuousOffsetSource c (p i))| <= sourceMoveError)
    (hquad : forall i,
      |(∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) * tau (p j) /
            rho j) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c (p i) y * tau y| <= testError)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    (hmargin : 0 < 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass))
    (i : Fin n) :
    |rho i * eps i - a * tau (p i)| <=
      (residualError + boundaryError + sourceMoveError + a * testError) /
        (2 * Real.pi -
          (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass)) := by
  let e : Fin n -> Real := fun j => rho j * eps j - a * tau (p j)
  let eta := residualError + boundaryError + sourceMoveError + a * testError
  have hdefect (l : Fin n) :
      |2 * Real.pi * e l + (1 / (N : Real)) * ∑ j,
        sixVertexContinuousOffsetKernel c (p l) (p j) / rho j * e j| <=
          eta := by
    let empiricalTau :=
      (∑ j, sixVertexContinuousOffsetKernel c (p l) (p j) * tau (p j) /
        rho j) / (N : Real)
    let integralTau := ∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c (p l) y * tau y
    have hempirical :
        (1 / (N : Real)) * ∑ j,
            sixVertexContinuousOffsetKernel c (p l) (p j) / rho j * e j =
          (1 / (N : Real)) * ∑ j,
              sixVertexContinuousOffsetKernel c (p l) (p j) * eps j -
            a * empiricalTau := by
      have hsum :
        (∑ j, sixVertexContinuousOffsetKernel c (p l) (p j) / rho j *
            (rho j * eps j - a * tau (p j))) =
          (∑ j, sixVertexContinuousOffsetKernel c (p l) (p j) * eps j) -
            a * ∑ j, (sixVertexContinuousOffsetKernel c (p l) (p j) *
              tau (p j) / rho j) := by
        calc
          _ = ∑ j, (sixVertexContinuousOffsetKernel c (p l) (p j) * eps j -
                a * (sixVertexContinuousOffsetKernel c (p l) (p j) *
                  tau (p j) / rho j)) := by
                  apply sum_congr rfl
                  intro j _
                  field_simp [(hrho j).ne']
          _ = (∑ j, sixVertexContinuousOffsetKernel c (p l) (p j) * eps j) -
              ∑ j, a * (sixVertexContinuousOffsetKernel c (p l) (p j) *
                tau (p j) / rho j) := by rw [sum_sub_distrib]
          _ = _ := by rw [mul_sum]
      change (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) / rho j *
            (rho j * eps j - a * tau (p j)) = _
      rw [hsum]
      dsimp [empiricalTau]
      ring
    have htau := htauEq (p l) (hpIcc l)
    have htauScaled :
        2 * Real.pi * (a * tau (p l)) =
          a * sixVertexContinuousOffsetSource c (p l) - a * integralTau := by
      change 2 * Real.pi * tau (p l) =
        sixVertexContinuousOffsetSource c (p l) - integralTau at htau
      calc
        2 * Real.pi * (a * tau (p l)) =
            a * (2 * Real.pi * tau (p l)) := by ring
        _ = a * (sixVertexContinuousOffsetSource c (p l) - integralTau) := by
          rw [htau]
        _ = _ := by ring
    have hidentity :
        2 * Real.pi * e l + (1 / (N : Real)) * ∑ j,
            sixVertexContinuousOffsetKernel c (p l) (p j) / rho j * e j =
          residual l +
            (boundary l - a * sixVertexContinuousOffsetSource c (aligned l)) +
            a * (sixVertexContinuousOffsetSource c (aligned l) -
              sixVertexContinuousOffsetSource c (p l)) +
            a * (integralTau - empiricalTau) := by
      have hlin := hlinear l
      dsimp [e]
      rw [hempirical]
      calc
        2 * Real.pi * (rho l * eps l - a * tau (p l)) +
            ((1 / (N : Real)) * ∑ j,
              sixVertexContinuousOffsetKernel c (p l) (p j) * eps j -
              a * empiricalTau) =
            (2 * Real.pi * (rho l * eps l) + (1 / (N : Real)) * ∑ j,
              sixVertexContinuousOffsetKernel c (p l) (p j) * eps j) -
              2 * Real.pi * (a * tau (p l)) - a * empiricalTau := by ring
        _ = (residual l + boundary l) -
            (a * sixVertexContinuousOffsetSource c (p l) - a * integralTau) -
              a * empiricalTau := by rw [hlin, htauScaled]
        _ = _ := by ring
    rw [hidentity]
    have hfour (A B C F : Real) :
        |A + B + C + F| <= |A| + |B| + |C| + |F| := by
      calc
        |A + B + C + F| <= |A + B + C| + |F| := abs_add_le _ _
        _ <= (|A + B| + |C|) + |F| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ <= ((|A| + |B|) + |C|) + |F| :=
          add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    calc
      |_ + _ + _ + _| <= |residual l| +
          |boundary l - a * sixVertexContinuousOffsetSource c (aligned l)| +
          |a * (sixVertexContinuousOffsetSource c (aligned l) -
            sixVertexContinuousOffsetSource c (p l))| +
          |a * (integralTau - empiricalTau)| := hfour _ _ _ _
      _ <= residualError + boundaryError + sourceMoveError + a * testError := by
        apply add_le_add
        · exact add_le_add (add_le_add (hresidual l) (hboundary l))
            (hsourceMove l)
        · rw [abs_mul, abs_of_nonneg ha, abs_sub_comm]
          exact mul_le_mul_of_nonneg_left (hquad l) ha
      _ = eta := rfl
  have hstable := discreteOffsetError_le_of_zeroMass hc hN hn hrho hmass
    hrow hreciprocal hdefect hmargin i
  simpa [e, eta] using hstable




theorem reciprocalWeightDensityMass_le_of_lower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hnN : n <= N) (hquarter : N <= 4 * n) {p : Fin n -> Real}
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N n p x) :
    sixVertexRootDensityScale c /
        (4 * (sixVertexAnisotropyMagnitude c + 1) *
          sixVertexFiniteRootDensityUniformBound c) <=
      (1 / (N : Real)) * ∑ j,
        1 / (sixVertexRootDensityWeight c (p j) *
          sixVertexFiniteRootDensity c N n p (p j)) := by
  let U := sixVertexFiniteRootDensityUniformBound c
  let A := sixVertexRootDensityScale c /
    (sixVertexAnisotropyMagnitude c + 1)
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hU : 0 < U := by
    dsimp [U, sixVertexFiniteRootDensityUniformBound]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (sixVertexRootDensityScale_pos hc)
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
  have hdensityPos (j : Fin n) :
      0 < sixVertexFiniteRootDensity c N n p (p j) :=
    hlower.trans_le (hdensity _)
  have hdensityUpper (j : Fin n) :
      sixVertexFiniteRootDensity c N n p (p j) <= U :=
    (le_abs_self _).trans
      (abs_sixVertexFiniteRootDensity_le hc hN hnN p (p j))
  have hterm (j : Fin n) : A / U <=
      1 / (sixVertexRootDensityWeight c (p j) *
        sixVertexFiniteRootDensity c N n p (p j)) := by
    have hw := sixVertexRootDensity_reciprocalWeight_lower hc (p j)
    change A <= 1 / sixVertexRootDensityWeight c (p j) at hw
    have hrho : 1 / U <=
        1 / sixVertexFiniteRootDensity c N n p (p j) :=
      one_div_le_one_div_of_le (hdensityPos j) (hdensityUpper j)
    have hmul := mul_le_mul hw hrho (one_div_pos.mpr hU).le
      (one_div_pos.mpr (sixVertexRootDensityWeight_pos hc (p j))).le
    calc
      A / U = A * (1 / U) := by ring
      _ <= (1 / sixVertexRootDensityWeight c (p j)) *
          (1 / sixVertexFiniteRootDensity c N n p (p j)) := hmul
      _ = _ := by
        field_simp [(sixVertexRootDensityWeight_pos hc (p j)).ne',
          (hdensityPos j).ne']
  have hsum : (n : Real) * (A / U) <= ∑ j : Fin n,
      1 / (sixVertexRootDensityWeight c (p j) *
        sixVertexFiniteRootDensity c N n p (p j)) := by
    calc
      (n : Real) * (A / U) = ∑ _j : Fin n, A / U := by simp
      _ <= _ := Finset.sum_le_sum fun j _ => hterm j
  have hratio : (1 / 4 : Real) <= (n : Real) / N := by
    apply (le_div_iff₀ hNreal).2
    have hquarterReal : (N : Real) <= 4 * (n : Real) := by
      exact_mod_cast hquarter
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 <= (1 / (N : Real)))
  rw [show sixVertexRootDensityScale c /
      (4 * (sixVertexAnisotropyMagnitude c + 1) *
        sixVertexFiniteRootDensityUniformBound c) = A / (4 * U) by
    dsimp [A, U]
    field_simp [hU.ne',
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc] :
        sixVertexAnisotropyMagnitude c + 1 ≠ 0)]
    ]
  calc
    A / (4 * U) = (1 / 4 : Real) * (A / U) := by ring
    _ <= ((n : Real) / N) * (A / U) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = (1 / (N : Real)) * ((n : Real) * (A / U)) := by ring
    _ <= _ := hscaled

end

end StatMech.FrontierD
