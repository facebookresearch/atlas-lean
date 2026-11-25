/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.CountableBasisFiniteDimensional

/-!
# A Banach space with a countable Hamel basis is finite-dimensional

A complete normed space cannot have a countably infinite Hamel basis:
write the space as the countable union of the spans of the basis vectors
over finite subfamilies. Each such span is finite-dimensional, hence
closed, so by the Baire category theorem one of them has nonempty
interior; a submodule with nonempty interior is the whole space, and the
space is therefore spanned by finitely many basis vectors.

Source: this combines two statements from
`v1/Atlas/IntroductionToFunctionalAnalysis/code/`:
the Baire Category Theorem in `BaireCategory.lean`
(`BaireCategory.baire_category_theorem`, February 23, 2021 lecture) and
the definition of a Hamel basis in `HahnBanach.lean`
(`HahnBanach.IsHamelBasis`, February 25, 2021 lecture).
Neither v1 statement is ported here; the theorem is a new consequence of
the two, proved from scratch. It is not in the pinned Mathlib: Mathlib has
the Baire theorem (`nonempty_interior_of_iUnion_of_closed`) and the
finite-dimensionality of finite spans separately, but no lemma combining
them into finite-dimensionality of a space with a countable basis.
-/

/-- **A Banach space with a countable Hamel basis is finite-dimensional.**
If `E` is a complete normed space over `𝕜 = ℝ, ℂ` admitting a Hamel basis
indexed by a countable type, then `E` is finite-dimensional. Completeness
is essential: it is what the Baire category argument uses. -/
theorem finiteDimensional_of_countable_basis {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {ι : Type*} [Countable ι] (b : Module.Basis ι 𝕜 E) : FiniteDimensional 𝕜 E := by
  have hcover : ⋃ s : Finset ι, (Submodule.span 𝕜 (b '' (s : Set ι)) : Set E) =
      Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    set S := (b.repr x).support with hS
    have hx : x = Finsupp.linearCombination 𝕜 (b : ι → E) (b.repr x) :=
      (b.linearCombination_repr x).symm
    have hsum : (b.repr x).sum (fun i a => a • b i) ∈
        Submodule.span 𝕜 (b '' ↑(b.repr x).support) := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨S, ?_⟩
    rw [hx, Finsupp.linearCombination_apply]
    exact hsum
  have hclosed : ∀ s : Finset ι,
      IsClosed (Submodule.span 𝕜 (b '' (s : Set ι)) : Set E) := by
    intro s
    have hfin : (b '' (s : Set ι)).Finite := s.finite_toSet.image b
    have hfd : FiniteDimensional 𝕜 ↥(Submodule.span 𝕜 (b '' (s : Set ι))) :=
      FiniteDimensional.span_of_finite 𝕜 hfin
    exact Submodule.closed_of_finiteDimensional _
  obtain ⟨s, hs⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have htop : Submodule.span 𝕜 (b '' (s : Set ι)) = ⊤ :=
    Submodule.eq_top_of_nonempty_interior' _ hs
  have hfd : FiniteDimensional 𝕜 ↥(Submodule.span 𝕜 (b '' (s : Set ι))) :=
    FiniteDimensional.span_of_finite 𝕜 (s.finite_toSet.image b)
  rw [htop] at hfd
  exact FiniteDimensional.of_surjective (⊤ : Submodule 𝕜 E).subtype
    (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)

/-- **An infinite-dimensional Banach space has no countable Hamel basis.** Let $E$ be a complete
normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If $E$ is not finite-dimensional,
then no Hamel basis of $E$ is indexed by a countable set. -/
theorem not_countable_basis_of_not_finiteDimensional {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) {ι : Type*} (b : Module.Basis ι 𝕜 E) :
    ¬ Countable ι := by
  intro hcount
  have := hcount
  exact hE (finiteDimensional_of_countable_basis b)

end MathlibExt.Analysis.FunctionalAnalysis.CountableBasisFiniteDimensional
