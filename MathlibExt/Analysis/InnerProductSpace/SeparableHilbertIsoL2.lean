/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Basic.Denumerable
public import Mathlib.Topology.Bases
public import MathlibExt.Analysis.InnerProductSpace.SeparableHilbertCountableBasis

@[expose] public section

/-!
# An infinite-dimensional separable Hilbert space is isometrically isomorphic to `ℓ²`

The book states (Theorem, April 13, 2021) that if `H` is an infinite-dimensional
separable Hilbert space, then `H` is isometrically isomorphic to `ℓ²`, the space of
square-summable sequences. The v1 formalization
(`HilbertSpace.separable_hilbert_isomorphic_ell2`) instead takes a Hilbert basis
indexed by `ℕ` as a hypothesis, so the existence of such a basis from separability
and infinite-dimensionality alone was not ported.

The countable Hilbert basis is provided by
`SeparableHilbertCountableBasis.exists_countable_hilbertBasis` in
`MathlibExt.Analysis.InnerProductSpace.SeparableHilbertCountableBasis`
(an orthonormal family in a separable space is countable, since distinct
orthonormal vectors are at distance `√2`).

The new steps here are:

* a Hilbert basis of an infinite-dimensional space has an infinite index type
  (a finite index type would give a finite basis, hence finite dimension);
* a countable infinite index type is equivalent to `ℕ`, so the basis can be
  reindexed to `ℕ`, and its `repr` is the required isometric isomorphism.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`,
`HilbertSpace.separable_hilbert_isomorphic_ell2` (April 13, 2021).
-/

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open Metric TopologicalSpace

namespace MathlibExt.Analysis.InnerProductSpace.SeparableHilbertIsoL2

/-- **A Hilbert basis of an infinite-dimensional space has infinite index type.**
A finite index type would give a finite basis, hence finite dimension. -/
private theorem infinite_of_not_finiteDimensional [CompleteSpace H] [SeparableSpace H]
    (hInf : ¬FiniteDimensional 𝕜 H) {ι : Type u} [Countable ι] (b : HilbertBasis ι 𝕜 H) :
    Infinite ι := by
  by_contra hfin
  have hFinite : Finite ι := Finite.of_not_infinite hfin
  classical
  have hFintype : Fintype ι := Fintype.ofFinite ι
  exact hInf (Module.Basis.finiteDimensional_of_finite b.toOrthonormalBasis.toBasis)

/-- **An infinite-dimensional separable Hilbert space admits a Hilbert basis indexed by
$\mathbb{N}$.** Let $H$ be a separable Hilbert space over $\mathbb{R}$ or $\mathbb{C}$ that is not
finite-dimensional. Then $H$ has a Hilbert basis $(e_n)_{n \in \mathbb{N}}$ indexed by the natural
numbers.

A countable Hilbert basis of $H$ has an infinite index set, which is therefore in bijection with
$\mathbb{N}$; reindexing along this bijection gives the basis. -/
theorem exists_hilbertBasis_nat [CompleteSpace H] [SeparableSpace H]
    (hInf : ¬FiniteDimensional 𝕜 H) : Nonempty (HilbertBasis ℕ 𝕜 H) := by
  obtain ⟨ι, hι, ⟨b⟩⟩ :=
    SeparableHilbertCountableBasis.exists_countable_hilbertBasis (𝕜 := 𝕜) (H := H)
  have hCountable : Countable ι := hι
  have hInfinite : Infinite ι := infinite_of_not_finiteDimensional hInf b
  obtain ⟨e⟩ : Nonempty (ι ≃ ℕ) :=
    @nonempty_equiv_of_countable ι ℕ hCountable hInfinite inferInstance inferInstance
  refine ⟨HilbertBasis.mk (v := b ∘ e.symm)
    (b.orthonormal.comp e.symm e.symm.injective) ?_⟩
  have hrange : Set.range (b ∘ e.symm) = Set.range b := by
    ext x
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e.symm n, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp⟩
  rw [hrange]
  exact b.dense_span.ge

/-- **An infinite-dimensional separable Hilbert space is isometrically isomorphic to
$\ell^2$.** Let $H$ be a separable Hilbert space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$
that is not finite-dimensional. Then there is a $\mathbb{K}$-linear isometric isomorphism from
$H$ onto $\ell^2(\mathbb{N}, \mathbb{K})$, the space of square-summable sequences in $\mathbb{K}$.

The isomorphism sends a vector to its coefficients with respect to a Hilbert basis of $H$ indexed
by $\mathbb{N}$, so it preserves norms and inner products. -/
theorem separable_hilbert_iso_l2 [CompleteSpace H] [SeparableSpace H]
    (hInf : ¬FiniteDimensional 𝕜 H) :
    Nonempty (H ≃ₗᵢ[𝕜] lp (fun _ : ℕ => 𝕜) 2) := by
  obtain ⟨b⟩ := exists_hilbertBasis_nat hInf
  exact ⟨b.repr⟩

end MathlibExt.Analysis.InnerProductSpace.SeparableHilbertIsoL2
