/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.TuringPatterns

/-! A continuum-unstable mode need not occur in the Neumann spectrum. -/

namespace MathlibExtTest.Analysis.PDE.SemilinearFlow.Instability

/-! ### Boundary case: unstable continuum wavenumber absent from the domain spectrum -/

open MathlibExt.Biology.Dynamics.TuringPatterns in
/-- **Continuum instability without domain instability.** For the Schnakenberg kinetics at
`a = 1/10`, `b = 9/10` with `d_u = 1`, `d_v = 9`, the continuum wavenumber `k = 1/√3` is
unstable, yet on `[0, 1]` with Neumann boundary conditions no admissible wavenumber `n π` is.
An unstable continuum wavenumber therefore yields no Neumann Fourier mode that could supply the
eigenvalue hypothesis of `exists_escape_of_semigroup` on this domain. -/
example : IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 (Real.sqrt (1 / 3)) ∧
    ∀ n : ℕ,
      ¬ IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 (neumannWavenumber 1 n) := by
  have htr : (schnakenbergJacobian (1 / 10) (9 / 10)).trace < 0 :=
    (trace_schnakenbergJacobian_neg_iff (by norm_num)).2 (by norm_num)
  have hdet : 0 < (schnakenbergJacobian (1 / 10) (9 / 10)).det := by
    rw [det_schnakenbergJacobian (by norm_num)]; norm_num
  refine ⟨?_, fun n => ?_⟩
  · rw [isUnstableMode_iff_dispersionDet_neg htr zero_le_one (by norm_num),
      Real.sq_sqrt (by norm_num), dispersionDet, det_schnakenbergJacobian (by norm_num)]
    norm_num [schnakenbergJacobian]
  refine not_isUnstableMode_neumannWavenumber_of_le one_pos (by norm_num) htr hdet one_pos ?_ n
  have hΔ : bandDiscriminant (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 ≤ 4 := by
    rw [bandDiscriminant, det_schnakenbergJacobian (by norm_num)]
    norm_num [schnakenbergJacobian]
  have hs : Real.sqrt (bandDiscriminant (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hΔ
  have hpi : (2 : ℝ) ^ 2 ≤ (Real.pi / 1) ^ 2 := by
    rw [div_one]
    exact pow_le_pow_left₀ (by norm_num) Real.two_le_pi 2
  unfold bandUpper
  norm_num [schnakenbergJacobian] at hs ⊢
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

end MathlibExtTest.Analysis.PDE.SemilinearFlow.Instability
