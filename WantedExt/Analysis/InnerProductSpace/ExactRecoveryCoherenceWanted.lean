/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition

/-!
# Coherence implies the Exact Recovery Condition (wanted)

The Exact Recovery Condition of `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition`
asks, for every atom `ψ` outside the optimal support, for coefficients `a` of the orthogonal
projection of `ψ` onto the span of the optimal atoms with `‖a‖₁ < 1`. J. A. Tropp (*Greed is
good: algorithmic results for sparse approximation*, IEEE Trans. Inform. Theory 50 (2004),
2231–2242, Theorem 3.5 and Corollary 3.6) shows that it holds for every support of size `m` as
soon as the dictionary is incoherent: if the atoms have unit norm and pairwise inner products at
most `μ` in modulus, then `(2m - 1) μ < 1`, that is `m < (μ⁻¹ + 1) / 2`, suffices. Then OMP and
basis pursuit recover every `m`-term superposition. The proof, through a Neumann series for the
inverse Gram matrix, is deferred.
-/

@[expose] public section

open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCoherenceWanted

/-- **Coherence implies the Exact Recovery Condition** (J. A. Tropp, *Greed is good: algorithmic
results for sparse approximation*, IEEE Trans. Inform. Theory 50 (2004), Theorem 3.5 with the
bound `μ₁(k) ≤ k μ`, as in Corollary 3.6). Let `D` be a dictionary of unit vectors in an inner
product space whose coherence is at most `μ`: `|⟨D i, D j⟩| ≤ μ` for `i ≠ j`. Let `Λ` be a finite
set of `m` indices with `(2m - 1) μ < 1`. Then for every index `ω ∉ Λ` there are coefficients
`a` with `∑_{i ∈ Λ} aᵢ D i = P_K (D ω)`, where `K` is the span of the atoms indexed by `Λ`, and
`∑_{i ∈ Λ} |aᵢ| < 1`. -/
theorem_wanted exists_erc_of_coherence {𝕜 E κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (D : κ → E) (hD : ∀ i, ‖D i‖ = 1) {μ : ℝ}
    (hμ : ∀ i j, i ≠ j → ‖⟪D i, D j⟫_𝕜‖ ≤ μ) (Λ : Finset κ)
    (hm : (2 * (Λ.card : ℝ) - 1) * μ < 1) {ω : κ} (hω : ω ∉ Λ) :
    ∃ a : Λ → 𝕜,
      ∑ i, a i • D i = (Submodule.span 𝕜 (Set.range fun i : Λ => D i)).starProjection (D ω) ∧
        ∑ i, ‖a i‖ < 1

end MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCoherenceWanted
