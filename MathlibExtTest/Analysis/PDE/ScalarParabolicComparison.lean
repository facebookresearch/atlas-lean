/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.ScalarParabolicComparison

/-!
# Tests for scalar parabolic nonnegativity

Checked consumers of `parabolic_solution_nonneg`:

- a constant nonnegative profile with constant reaction and the matching
  source `K * a`;
- the steady linear profile `c t x = x`, whose spatial derivative is `1`
  and whose second spatial derivative is `0`.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.ScalarParabolicComparison

/-- Constant profile: `c = a ≥ 0`, `k = K ≥ 0` and `s = K * a` satisfy
`c_t - D * c_xx + k * c = s`, so the conclusion is `0 ≤ a` at every point
of the cylinder. -/
example {D L T K a : ℝ} (hD : 0 < D) (hL : 0 < L) (hT : 0 < T)
    (hK : 0 ≤ K) (ha : 0 ≤ a) {t x : ℝ}
    (ht : t ∈ Set.Icc 0 T) (hx : x ∈ Set.Icc 0 L) : 0 ≤ a := by
  exact parabolic_solution_nonneg hD hL hT
    (c := fun _ _ => a) (ct := fun _ _ => 0) (cx := fun _ _ => 0)
    (cxx := fun _ _ => 0) (k := fun _ _ => K) (s := fun _ _ => K * a)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (by simpa using continuousOn_const)
    (fun _ _ _ _ => by simp)
    (fun _ _ _ _ => hK)
    (fun _ _ _ _ => mul_nonneg hK ha)
    (fun _ _ => ha) (fun _ _ => ha) (fun _ _ => ha) ht hx

/-- Steady linear profile: `c t x = x` solves `c_t - D * c_xx = 0`, with
nonnegative initial data `x` on `[0, L]` and boundary values `0` and `L`;
the conclusion recovers `0 ≤ x` on the cylinder. -/
example {D L T : ℝ} (hD : 0 < D) (hL : 0 < L) (hT : 0 < T)
    {t x : ℝ} (ht : t ∈ Set.Icc 0 T) (hx : x ∈ Set.Icc 0 L) : 0 ≤ x := by
  exact parabolic_solution_nonneg hD hL hT
    (c := fun _ y => y) (ct := fun _ _ => 0) (cx := fun _ _ => 1)
    (cxx := fun _ _ => 0) (k := fun _ _ => 0) (s := fun _ _ => 0)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (fun _ _ _ _ => hasDerivAt_id' _)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    continuousOn_snd
    (fun _ _ _ _ => by simp)
    (fun _ _ _ _ => le_refl 0)
    (fun _ _ _ _ => le_refl 0)
    (fun y hy => hy.1) (fun _ _ => le_refl 0) (fun _ _ => hL.le) ht hx

end MathlibExt.Analysis.PDE.ScalarParabolicComparison
