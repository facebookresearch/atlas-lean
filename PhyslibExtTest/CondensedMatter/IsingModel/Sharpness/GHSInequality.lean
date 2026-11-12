/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.GHSInequality

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.GHSUnconditional`

On the triangle `⊤ : SimpleGraph (Fin 3)`:
* `ghs_signDominance`: the predicate `GHSSignDominance` holds at `β = 1`, `h = 1/2`;
* `ghs_magnetization_concaveOn` at `β = 1`, used as the midpoint inequality
  `(m(0) + m(2)) / 2 ≤ m(1)` for the magnetization `m(h) = ⟨σ_0⟩_h`;
* `ghs_susceptibility_le_inv_field` at `β = 1`, `h = 2`: the field derivative of `⟨σ_0⟩` is
  `β` times the sum of covariances, and it is at most `1 / h = 1/2`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.GHSUnconditional

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Sharpness _root_.StatMech.Walls

/-- The triangle, the complete graph on three vertices. -/
abbrev triangle : SimpleGraph (Fin 3) := ⊤

-- The GHS sign condition on the triangle.
example : GHSSignDominance triangle 1 (1 / 2) 0 :=
  ghs_signDominance triangle 1 (1 / 2) zero_le_one (by norm_num) 0

-- GHS concavity of `h ↦ ⟨σ_0⟩_h`, at the midpoint of `[0, 2]`.
example : (isingExpectation triangle 1 0 (fun s => spin s 0)
      + isingExpectation triangle 1 2 (fun s => spin s 0)) / 2
    ≤ isingExpectation triangle 1 1 (fun s => spin s 0) := by
  have hc := ghs_magnetization_concaveOn triangle 1 zero_le_one 0
  have := hc.2 (show (0 : ℝ) ∈ Set.Ici 0 from le_rfl) (show (2 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at this
  rw [show (1 / 2 : ℝ) * 0 + 1 / 2 * 2 = 1 by norm_num] at this
  linarith

-- The susceptibility identity and the GHS bound `χ ≤ 1 / h` at `β = 1`, `h = 2`.
example : deriv (fun t => isingExpectation triangle 1 t (fun s => spin s 0)) 2 ≤ 1 / 2 ∧
    deriv (fun t => isingExpectation triangle 1 t (fun s => spin s 0)) 2 =
      1 * ∑ x, (isingExpectation triangle 1 2 (fun s => spin s 0 * spin s x) -
        isingExpectation triangle 1 2 (fun s => spin s 0) *
          isingExpectation triangle 1 2 (fun s => spin s x)) :=
  have h := ghs_susceptibility_le_inv_field triangle 1 2 zero_le_one (by norm_num) 0
  ⟨h.2, h.1⟩

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.GHSUnconditional
