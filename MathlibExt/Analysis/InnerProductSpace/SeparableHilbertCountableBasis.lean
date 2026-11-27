/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Bases

@[expose] public section

open Metric TopologicalSpace
open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.SeparableHilbertCountableBasis

/-!
# A separable Hilbert space admits a countable Hilbert basis

This is the converse of the book's corollary that a Hilbert space with a
countable Hilbert basis is separable. The book states the forward direction
(Corollary, April 13, 2021) and, for infinite-dimensional separable Hilbert
spaces, the isometric isomorphism with `ℓ²` (Theorem, April 13, 2021), whose
proof passes through a countable orthonormal basis. The v1 formalization of
that theorem (`HilbertSpace.separable_hilbert_isomorphic_ell2`) instead takes
a Hilbert basis indexed by `ℕ` as a hypothesis, so the existence of a
countable basis from separability alone was not ported.

The key step, which is not in the pinned Mathlib, is that an orthonormal
family in a separable inner product space is countable: distinct orthonormal
vectors are at distance `√2`, so the open balls of radius `1 / 2` around them
are pairwise disjoint, and a separable space admits only countably many
pairwise disjoint nonempty open sets
(`Pairwise.countable_of_isOpen_disjoint`). Combining this with Mathlib's
`exists_hilbertBasis` (every Hilbert space admits some Hilbert basis) gives
a Hilbert basis indexed by a countable type.

Note the completeness hypothesis: `exists_hilbertBasis` needs `CompleteSpace`,
so this direction, unlike the forward direction, is stated for Hilbert spaces
rather than pre-Hilbert spaces.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`,
`HilbertSpace.separable_of_countable_hilbertBasis` (converse direction) and
`HilbertSpace.separable_hilbert_isomorphic_ell2` (April 13, 2021).
-/

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **An orthonormal family in a separable space is countable.** Let $H$ be a separable inner
product space over $\mathbb{R}$ or $\mathbb{C}$. If $(v_i)_{i \in \iota}$ is an orthonormal family
in $H$, then the index set $\iota$ is countable.

Distinct orthonormal vectors are at distance $\sqrt{2}$, so the open balls of radius $1/2$ around
them are pairwise disjoint. -/
theorem countable_of_orthonormal [SeparableSpace H] {ι : Type*} {v : ι → H}
    (hv : Orthonormal 𝕜 v) : Countable ι := by
  have hdist : ∀ {i j : ι}, i ≠ j → (1 : ℝ) ≤ dist (v i) (v j) := by
    intro i j hij
    rw [dist_eq_norm]
    have hsq : ‖v i - v j‖ ^ 2 = 2 := by
      have h := norm_sub_sq (𝕜 := 𝕜) (v i) (v j)
      rw [hv.norm_eq_one i, hv.norm_eq_one j] at h
      simp only [hv.inner_eq_zero hij, map_zero] at h
      norm_num at h
      exact h
    nlinarith [norm_nonneg (v i - v j), hsq]
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => ball (v i) (1 / 2 : ℝ)) ?_ ?_ ?_
  · intro i j hij
    exact ball_disjoint_ball (by
      have h := hdist hij
      linarith)
  · intro i
    exact isOpen_ball
  · intro i
    exact ⟨v i, mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)⟩

/-- **A separable Hilbert space admits a countable Hilbert basis.** Let $H$ be a separable Hilbert
space over $\mathbb{R}$ or $\mathbb{C}$. Then $H$ has a Hilbert basis $(e_i)_{i \in \iota}$ (an
orthonormal family whose linear span is dense in $H$) indexed by a countable set $\iota$. -/
theorem exists_countable_hilbertBasis [CompleteSpace H] [SeparableSpace H] :
    ∃ (ι : Type u) (_ : Countable ι), Nonempty (HilbertBasis ι 𝕜 H) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis 𝕜 H
  exact ⟨↥w, countable_of_orthonormal b.orthonormal, ⟨b⟩⟩

end MathlibExt.Analysis.InnerProductSpace.SeparableHilbertCountableBasis
