/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Lp.SchauderBasis

@[expose] public section

namespace MathlibExt.Analysis.Normed.Lp.SchauderBasisTest

open MathlibExt.Analysis.Normed.Lp.SchauderBasis
open Filter
open scoped ENNReal Topology

/-- The `0`-th basis vector of the `ℓ² (ℕ, ℝ)` Schauder basis is the unit vector. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp) 0
      = lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ) :=
  lpUnconditionalSchauderBasis_apply hp 0

/-- Biorthogonality: the `0`-th coordinate of the `1`-st basis vector is `0`. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp).coord 0
        (lp.single (E := fun _ : ℕ => ℝ) 2 1 (3 : ℝ)) = 0 := by
  rw [lpUnconditionalSchauderBasis_coord_apply]
  exact lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 1 (3 : ℝ) (by norm_num)

/-- Biorthogonality: the `1`-st coordinate of the `1`-st basis vector is `1` times the value. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp).coord 1
        (lp.single (E := fun _ : ℕ => ℝ) 2 1 (3 : ℝ)) = 3 := by
  rw [lpUnconditionalSchauderBasis_coord_apply]
  exact lp.single_apply_self _ _ _

/-- The same coordinate computation over `ℂ`: the basis is not `ℝ`-specific. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℂ) (p := 2) hp).coord 0
        (lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ)) = 1 := by
  rw [lpUnconditionalSchauderBasis_coord_apply]
  exact lp.single_apply_self _ _ _

/-- Projecting `5 • e 0 + 7 • e 2` onto the coordinates `{0, 2}` is the identity. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp).proj {0, 2}
        (lp.single (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ)
          + lp.single (E := fun _ : ℕ => ℝ) 2 2 (7 : ℝ))
      = lp.single (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ)
          + lp.single (E := fun _ : ℕ => ℝ) 2 2 (7 : ℝ) := by
  simp [← lp.single_smul]

/-- Projecting `5 • e 0 + 7 • e 2` onto the coordinate `{0}` drops the `e 2` part. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp).proj {0}
        (lp.single (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ)
          + lp.single (E := fun _ : ℕ => ℝ) 2 2 (7 : ℝ))
      = lp.single (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ) := by
  simp [← lp.single_smul]

/-- The expansion sums to the vector: the `tsum` form of the Schauder expansion. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))]
    (x : lp (fun _ : ℕ => ℝ) 2) :
    ∑' i, (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp).coord i x
        • (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp) i = x :=
  (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp).expansion x |>.tsum_eq

/-- The basis projections are contractive on vectors. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))]
    (x : lp (fun _ : ℕ => ℝ) 2) :
    ‖(lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp).proj {0} x‖ ≤ ‖x‖ :=
  norm_lpSchauderBasis_proj_apply_le hp {0} x

/-- Every unconditional basis projection has operator norm at most `1`. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    ‖(lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := ℝ) (p := 2) hp).proj {0, 1}‖ ≤ 1 :=
  norm_lpSchauderBasis_proj_le hp {0, 1}

/-- The classical partial sums converge to the vector. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))]
    (x : lp (fun _ : ℕ => ℝ) 2) :
    Tendsto (fun n => (lpSchauderBasis (𝕜 := ℝ) (p := 2) hp).proj n x) atTop (𝓝 x) :=
  SchauderBasis.tendsto_proj _ x

/-- The classical `n = 2` partial sum truncates after the first two coordinates. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    (lpSchauderBasis (𝕜 := ℝ) (p := 2) hp).proj 2
        (lp.single (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ)
          + lp.single (E := fun _ : ℕ => ℝ) 2 2 (7 : ℝ))
      = lp.single (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ) := by
  simp [← lp.single_smul, Finset.sum_range_succ]

/-- Every classical partial-sum projection has operator norm at most `1`. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    ‖(lpSchauderBasis (𝕜 := ℝ) (p := 2) hp).proj 3‖ ≤ 1 :=
  norm_lpSchauderBasis_classical_proj_le hp 3

end MathlibExt.Analysis.Normed.Lp.SchauderBasisTest
