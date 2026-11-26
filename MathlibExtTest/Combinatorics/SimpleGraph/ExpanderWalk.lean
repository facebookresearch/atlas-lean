/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.ExpanderWalk
public import MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander

@[expose] public section

open MathlibExt.Combinatorics.SpectralExpander

namespace MathlibExtTest.Combinatorics.SimpleGraph.ExpanderWalk

/-- The hitting property on `K₄` (`λ = 1 / 3`) for `B = {0}` (`μ = 1 / 4`): a walk with `t` steps
stays at vertex `0` throughout with probability at most `(1/4 + (1/3)(3/4)) ^ (t + 1) = 2⁻⁽ᵗ⁺¹⁾`. -/
example (t : ℕ) :
    walkProb (⊤ : SimpleGraph (Fin 4)) 3
        MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander.k4.1 (by norm_num) t
        (fun w => ∀ i, w i ∈ ({0} : Finset (Fin 4))) ≤
      (1 / 2) ^ (t + 1) := by
  have h := walkProb_forall_mem_le
    MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander.k4 (by norm_num) {0} t
  have e : ((({0} : Finset (Fin 4)).card : ℝ) / Fintype.card (Fin 4) +
      1 / 3 * (1 - (({0} : Finset (Fin 4)).card : ℝ) / Fintype.card (Fin 4))) = 1 / 2 := by
    norm_num
  rwa [e] at h

/-- Logarithmic diameter on `K₄`: `(1/3)² · 4 < 1`, so any two vertices are joined by a walk of
length exactly `2` (also between a vertex and itself). -/
example (s t : Fin 4) : ∃ p : (⊤ : SimpleGraph (Fin 4)).Walk s t, p.length = 2 :=
  exists_walk_length_eq_of_pow_mul_lt
    MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander.k4 (by norm_num) (by norm_num) s t

end MathlibExtTest.Combinatorics.SimpleGraph.ExpanderWalk
