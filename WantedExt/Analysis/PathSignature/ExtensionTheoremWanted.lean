/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.PathSignature.FactorialEstimate

/-!
# Lyons's extension theorem (wanted)

A multiplicative functional of degree `⌊p⌋` and finite `p`-variation (a `p`-rough path) extends
uniquely to a multiplicative functional of every degree with finite `p`-variation, and with the
factorial control `ω^{i/p} / (β (i/p)!)` in every degree once `β` is large enough (T. Lyons,
*Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14 (1998), Theorem 2.2.1).
So the first `⌊p⌋` levels determine all higher "iterated integrals" of a rough path, and in
particular its signature (Boedihardjo, Geng, Lyons and Yang, Adv. Math. 293 (2016),
arXiv:1406.7871, Proposition 2.1, which quotes it for weakly geometric rough paths). The
statements use the coordinates and `ℓ¹` tensor norms of
`MathlibExt.Analysis.PathSignature.RoughPath`.
-/

@[expose] public section

namespace MathlibExt.Analysis.PathSignature.ExtensionTheoremWanted

open MathlibExt.Analysis.PathSignature

/-- **Lyons's extension theorem: existence and uniqueness.** Let `p ≥ 1`, let `J` be an interval
and let `X` be a multiplicative functional of degree `⌊p⌋` on `J` with finite `p`-variation. Then
there is a multiplicative functional `Y` of every degree, agreeing with `X` on the levels
`0, …, ⌊p⌋`, with finite `p`-variation in every degree; and any multiplicative functional of some
degree `m` with finite `p`-variation that agrees with `X` up to level `⌊p⌋` agrees with `Y` up to
level `m` (T. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14
(1998), Theorem 2.2.1). -/
theorem_wanted exists_unique_extension {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 ≤ p)
    {J : Set ℝ} (hJ : J.OrdConnected) (X : ℝ → ℝ → List ι → ℝ)
    (hX : IsMultiplicativeFunctional ⌊p⌋₊ X J) (hXp : HasFinitePVariation p ⌊p⌋₊ X J) :
    ∃ Y : ℝ → ℝ → List ι → ℝ,
      (∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ ⌊p⌋₊ → Y s t w = X s t w) ∧
      (∀ m, IsMultiplicativeFunctional m Y J ∧ HasFinitePVariation p m Y J) ∧
      ∀ (m : ℕ) (Z : ℝ → ℝ → List ι → ℝ),
        (∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ ⌊p⌋₊ → Z s t w = X s t w) →
        IsMultiplicativeFunctional m Z J → HasFinitePVariation p m Z J →
        ∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ m → Z s t w = Y s t w

end MathlibExt.Analysis.PathSignature.ExtensionTheoremWanted
