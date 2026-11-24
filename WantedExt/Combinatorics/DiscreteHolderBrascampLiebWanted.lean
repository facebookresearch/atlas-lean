/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The discrete Hölder–Brascamp–Lieb inequality for subgroups of `ℤ^d`

Christ, Demmel, Knight, Scanlon and Yelick (*Communication lower bounds and optimal algorithms
for programs that reference arrays, Part 1*, arXiv:1308.0068, 2013, Theorem 3.2) characterise
the exponents `s ∈ [0, 1]^m` for which every finite set `E ⊆ ℤ^d` satisfies
`|E| ≤ ∏ⱼ |φⱼ(E)|^{sⱼ}`, for group homomorphisms `φⱼ : ℤ^d → ℤ^{dⱼ}`: exactly those with
`rank H ≤ ∑ⱼ sⱼ rank φⱼ(H)` for every subgroup `H ≤ ℤ^d`. This is the discrete Hölder–Brascamp–Lieb
(HBL) inequality behind their communication lower bound `Ω(|Z| / M^{s_HBL - 1})` for programs whose
array subscripts are affine in the loop indices (their Theorem 4.1). The three coordinate
projections `ℤ³ → ℤ²` with `s = (1/2, 1/2, 1/2)` give the discrete Loomis–Whitney inequality.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.DiscreteHolderBrascampLiebWanted

/-- **Discrete Hölder–Brascamp–Lieb inequality.** Let `φⱼ : ℤ^d → ℤ^{dⱼ}` (`j = 1, …, m`) be
group homomorphisms and `s ∈ [0, 1]^m`. Then `rank H ≤ ∑ⱼ sⱼ rank φⱼ(H)` for all subgroups
`H ≤ ℤ^d` if and only if `|E| ≤ ∏ⱼ |φⱼ(E)|^{sⱼ}` for all nonempty finite sets `E ⊆ ℤ^d`
(Christ, Demmel, Knight, Scanlon and Yelick, arXiv:1308.0068, Theorem 3.2). The rank of a
subgroup of `ℤ^k` is its rank as a free `ℤ`-module. -/
theorem_wanted rank_le_iff_card_le_prod {d m : ℕ} (dj : Fin m → ℕ)
    (φ : (j : Fin m) → (Fin d → ℤ) →+ (Fin (dj j) → ℤ)) (s : Fin m → ℝ)
    (hs : ∀ j, s j ∈ Set.Icc (0 : ℝ) 1) :
    (∀ H : AddSubgroup (Fin d → ℤ),
        (Module.finrank ℤ H : ℝ) ≤ ∑ j, s j * (Module.finrank ℤ (H.map (φ j)) : ℝ)) ↔
      ∀ E : Finset (Fin d → ℤ), E.Nonempty →
        (E.card : ℝ) ≤ ∏ j, ((E.image (φ j)).card : ℝ) ^ s j

end MathlibExt.Combinatorics.DiscreteHolderBrascampLiebWanted
