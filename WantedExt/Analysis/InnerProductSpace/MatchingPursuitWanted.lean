/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import MathlibExt.Analysis.InnerProductSpace.MatchingPursuit

/-!
# Convergence of matching pursuit (wanted)

Matching pursuit (`MathlibExt.Analysis.InnerProductSpace.MatchingPursuit`) chooses at step `n`
an atom `g_{γₙ}` of a dictionary `D = (g_γ)_{γ ∈ Γ}` of unit vectors with
`|⟨g_{γₙ}, Rⁿ f⟩| ≥ α sup_γ |⟨g_γ, Rⁿ f⟩|` for a fixed optimality factor `0 < α ≤ 1`
(S. Mallat and Z. Zhang, *Matching pursuits with time-frequency dictionaries*, IEEE Trans.
Signal Process. 41 (1993), Section III, equation (11)). Their Theorem 1, proved in their
Appendix A by transposing a result of L. K. Jones on projection pursuit, states that the
residues converge to the orthogonal projection of `f` on the orthogonal complement `W` of the
closed span `V` of the dictionary. With the energy identity (17) this gives
`P_V f = ∑ₙ ⟨g_{γₙ}, Rⁿ f⟩ g_{γₙ}` and `‖P_V f‖² = ∑ₙ |⟨g_{γₙ}, Rⁿ f⟩|²`, equations
(19)–(20). The proof is deferred.
-/

@[expose] public section

open scoped InnerProductSpace
open Filter Topology MathlibExt.Analysis.InnerProductSpace.MatchingPursuit

namespace MathlibExt.Analysis.InnerProductSpace.MatchingPursuitWanted

/-- **Convergence of matching pursuit** (S. Mallat and Z. Zhang, *Matching pursuits with
time-frequency dictionaries*, IEEE Trans. Signal Process. 41 (1993), Theorem 1). Let `H` be a
Hilbert space, `D : Γ → H` a dictionary of unit vectors and `0 < α ≤ 1`. If the selected
indices `γₙ` satisfy the weak greedy rule
`α · sup_γ |⟨D γ, Rⁿ f⟩| ≤ |⟨D γₙ, Rⁿ f⟩|` (equation (11)) for every `n`, then the residues
`R^m f` converge to the orthogonal projection of `f` on the orthogonal complement of the span of
the dictionary (equation (18)). (The orthogonal complement of the span equals that of its
closure.) -/
theorem_wanted tendsto_residue_starProjection_orthogonal
    {𝕜 H Γ : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : Γ → H) (hD : ∀ γ, ‖D γ‖ = 1) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (γs : ℕ → Γ) (f : H)
    (hsel : ∀ n, α * ⨆ γ, ‖⟪D γ, residue (𝕜 := 𝕜) (D ∘ γs) f n⟫_𝕜‖ ≤
      ‖⟪D (γs n), residue (𝕜 := 𝕜) (D ∘ γs) f n⟫_𝕜‖) :
    Tendsto (fun m => residue (𝕜 := 𝕜) (D ∘ γs) f m) atTop
      (𝓝 ((Submodule.span 𝕜 (Set.range D))ᗮ.starProjection f))

end MathlibExt.Analysis.InnerProductSpace.MatchingPursuitWanted
