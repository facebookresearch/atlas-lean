/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ZeroSumMinimax

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Pure best responses in finite zero-sum matrix games

In the matrix game `A : Matrix (Fin m) (Fin n) ℝ`, with the conventions of
`MathlibExt.GameTheory.ZeroSumMinimax`, mixed strategies are points of standard simplices and the
row player receives `p.weights ⬝ᵥ (A *ᵥ q.weights)`. A pure strategy is a vertex
`StdSimplex.single i`. Against a fixed column strategy `q` the payoff is linear in `p`, so a row
`i` that maximizes `(A *ᵥ q.weights) i` is a best response to `q` against every mixed row
strategy at once.

## Main results

* `single_weights_dotProduct`: the payoff of the pure row strategy `i` is `(A *ᵥ q.weights) i`.
* `exists_pure_best_response`: against every column strategy, some pure row strategy does at
  least as well as every mixed row strategy.
-/

@[expose] public section

namespace MathlibExt.GameTheory.ZeroSumBestResponse

open Matrix Convexity

/-- Pairing the pure strategy `i` with a vector picks out its `i`-th entry. -/
theorem single_weights_dotProduct {m : ℕ} (i : Fin m) (v : Fin m → ℝ) :
    (StdSimplex.single (R := ℝ) i).weights ⬝ᵥ v = v i := by
  simp [StdSimplex.single, Finsupp.single_eq_pi_single, single_dotProduct]

/-- **Pure best responses exist.** In the matrix game `A`, against any column strategy `q`, some
row `i` does at least as well as every mixed row strategy `p`; the same `i` works for all `p`. -/
theorem exists_pure_best_response {m n : ℕ} [Nonempty (Fin m)]
    (A : Matrix (Fin m) (Fin n) ℝ) (q : StdSimplex ℝ (Fin n)) :
    ∃ i : Fin m, ∀ p : StdSimplex ℝ (Fin m),
      p.weights ⬝ᵥ (A *ᵥ q.weights) ≤
        (StdSimplex.single (R := ℝ) i).weights ⬝ᵥ (A *ᵥ q.weights) := by
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (A *ᵥ q.weights)
    Finset.univ_nonempty
  refine ⟨i₀, fun p => ?_⟩
  rw [single_weights_dotProduct]
  calc p.weights ⬝ᵥ (A *ᵥ q.weights)
      = ∑ i, p.weights i * (A *ᵥ q.weights) i := rfl
    _ ≤ ∑ i, p.weights i * (A *ᵥ q.weights) i₀ :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hmax i (Finset.mem_univ i)) (p.weights_nonneg i)
    _ = (A *ᵥ q.weights) i₀ := by
        rw [← Finset.sum_mul, StdSimplex.total_of_fintype p, one_mul]

end MathlibExt.GameTheory.ZeroSumBestResponse

end
