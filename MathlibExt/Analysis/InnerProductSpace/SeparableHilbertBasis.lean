/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Bases

@[expose] public section

open TopologicalSpace Set

namespace MathlibExt.Analysis.InnerProductSpace.SeparableHilbertBasis

/-!
# A Hilbert space with a countable Hilbert basis is separable

If a Hilbert space admits a Hilbert basis indexed by a countable type, then
it is separable: the range of the basis is countable, hence separable; the
linear span of a separable set is separable; and the span of a Hilbert basis
is dense, so the countable dense set witnessing separability of the span is
already dense in the whole space.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`,
`HilbertSpace.separable_of_countable_hilbertBasis` (Corollary, April 13, 2021).

Audit note: this statement is not in the pinned Mathlib. Mathlib has the
two ingredients separately — `HilbertBasis.dense_span` (the span of a
Hilbert basis is dense) and `TopologicalSpace.IsSeparable.span` (the span
of a separable set is separable) — but no lemma combining them into
separability of the ambient space, and no `SeparableSpace` conclusion for a
space with a countable Hilbert basis anywhere in Mathlib or MathlibExt.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **A Hilbert space with a countable orthonormal basis is separable.**
If `H` admits a Hilbert basis indexed by a countable type, then `H` is
separable. No completeness hypothesis is needed: it is the density of the
span of the basis, not completeness, that is used. -/
theorem separableSpace_of_countable_hilbertBasis {ι : Type*} [Countable ι]
    (b : HilbertBasis ι 𝕜 H) : SeparableSpace H := by
  have hsep : IsSeparable (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) :=
    (Set.countable_range (b : ι → H)).isSeparable.span
  obtain ⟨c, hc_count, hc_sub⟩ := hsep
  refine SeparableSpace.mk ⟨c, hc_count, ?_⟩
  rw [dense_iff_closure_eq]
  have hspan :
      closure (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) = Set.univ := by
    have h := congrArg (fun s : Submodule 𝕜 H => (s : Set H)) b.dense_span
    simp only [Submodule.topologicalClosure_coe, Submodule.top_coe] at h
    exact h
  have hsub :
      closure (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) ⊆ closure c :=
    closure_minimal hc_sub isClosed_closure
  rw [hspan] at hsub
  exact Set.eq_univ_of_univ_subset hsub

end MathlibExt.Analysis.InnerProductSpace.SeparableHilbertBasis
