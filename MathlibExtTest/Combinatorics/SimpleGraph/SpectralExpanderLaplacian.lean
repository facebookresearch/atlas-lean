/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SpectralExpanderLaplacian
public import MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander

@[expose] public section

open Matrix MathlibExt.Combinatorics.SpectralExpander

namespace MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpanderLaplacian

/-- Edge expansion of `K₄` from its spectral parameter `λ = 1 / 3`: for `S = {0, 1}`,
`3 (1 - 1/3) · 2 · 2 = 8 ≤ 4 e(S, V \ S)`, so `e(S, V \ S) ≥ 2`; the true count is `4`. -/
example :
    (3 : ℝ) * (1 - 1 / 3) * ({0, 1} : Finset (Fin 4)).card *
        (Finset.univ \ ({0, 1} : Finset (Fin 4))).card ≤
      (Fintype.card (Fin 4) : ℝ) *
        ((⊤ : SimpleGraph (Fin 4)).interedges {0, 1} (Finset.univ \ {0, 1})).card :=
  mul_card_mul_card_compl_le_card_interedges
    MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander.k4 _

/-- The Laplacian Rayleigh bound on `K₄`: `xᵀ L x ≥ 3 (1 - 1/3) xᵀ x = 2 xᵀ x` for `x ⊥ 1`
(the true value is `4 xᵀ x`, the non-trivial Laplacian eigenvalue of `K₄`). -/
example (x : Fin 4 → ℝ) (hx : x ⬝ᵥ 1 = 0) :
    (3 : ℝ) * (1 - 1 / 3) * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((⊤ : SimpleGraph (Fin 4)).lapMatrix ℝ *ᵥ x) :=
  mul_dotProduct_le_lapMatrix MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander.k4 x hx

/-- The independent-set bound is tight on `K₄`: `λ / (1 + λ) · N = 1` for `λ = 1 / 3`, `N = 4`,
and single vertices are independent. -/
example : (1 + 1 / 3 : ℝ) * ({0} : Finset (Fin 4)).card ≤ 1 / 3 * Fintype.card (Fin 4) :=
  one_add_mul_card_le_of_isIndepSet MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander.k4
    (by norm_num) (by simp [SimpleGraph.IsIndepSet])

end MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpanderLaplacian
