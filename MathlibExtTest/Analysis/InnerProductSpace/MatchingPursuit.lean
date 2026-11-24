/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.MatchingPursuit
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for matching pursuit
-/

open scoped InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.MatchingPursuit

namespace MathlibExtTest.Analysis.InnerProductSpace.MatchingPursuit

/-- The constant sequence of the first standard basis vector of `ℝ²` is a family of unit
vectors, so the energy identity applies; one step removes the first coordinate. -/
example : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := by simp

/-- Energy conservation instantiated on `ℝ²` with a constant unit atom. -/
example (f : EuclideanSpace ℝ (Fin 2)) (m : ℕ) :
    ‖f‖ ^ 2 = ∑ n ∈ Finset.range m,
        ‖⟪(fun _ => EuclideanSpace.single 0 1 : ℕ → EuclideanSpace ℝ (Fin 2)) n,
          residue (𝕜 := ℝ) (fun _ => EuclideanSpace.single 0 1) f n⟫_ℝ‖ ^ 2 +
      ‖residue (𝕜 := ℝ) (fun _ => EuclideanSpace.single 0 1) f m‖ ^ 2 :=
  norm_sq_eq_sum_add_norm_sq_residue _ (fun _ => by simp) f m

/-- One step of matching pursuit with the atom `e₀` removes exactly the first coordinate. -/
example : residue (𝕜 := ℝ) (fun _ => EuclideanSpace.single 0 1)
      (!₂[3, 4] : EuclideanSpace ℝ (Fin 2)) 1 = !₂[0, 4] := by
  ext i
  fin_cases i <;> simp [residue_succ, EuclideanSpace.inner_single_left]

/-- The weak greedy selection rule of Mallat and Zhang (equation (11)), as used in
`MatchingPursuitWanted.tendsto_residue_starProjection_orthogonal`, is satisfiable: with a
one-atom dictionary and `α = 1`, selecting that atom at every step satisfies it. -/
example (f : EuclideanSpace ℝ (Fin 2)) (n : ℕ) :
    (1 : ℝ) * ⨆ _ : Unit,
        ‖⟪(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)),
          residue (𝕜 := ℝ) (fun _ => EuclideanSpace.single 0 1) f n⟫_ℝ‖ ≤
      ‖⟪(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)),
          residue (𝕜 := ℝ) (fun _ => EuclideanSpace.single 0 1) f n⟫_ℝ‖ := by
  simp

end MathlibExtTest.Analysis.InnerProductSpace.MatchingPursuit
