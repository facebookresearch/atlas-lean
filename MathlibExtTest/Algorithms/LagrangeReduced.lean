/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.LagrangeReduced

@[expose] public section

/-- The two coordinate axes form a Lagrange-reduced pair, and some
combination attains the bound. -/
example : ∃ w : Fin 2 → ℝ,
    vdot (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
        (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
      ≤ (4 / 3) * vdot w w :=
  ⟨_, lagrange_short (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
    (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)
    (by simp [vdot]) (by simp [vdot]) (by simp [vdot]) 1 0 (by simp)⟩

end
