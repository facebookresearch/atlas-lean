/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A full-rank discrete submodule is a lattice (ATLAS Lemma 14.3, slice)

Source: ATLAS `NumberTheoryI`, Lemma 14.3 (Geometry of Numbers). The book's
Lemma 14.3 states that a subgroup `G ⊆ V ≃ ℝⁿ` is finitely generated if and
only if it is discrete, in which case `G ≃ ℤᵐ` for some `m ≤ n`, and `G` is
cocompact if and only if `m = n`.

This module ports **only the full-rank clause** of that lemma: a discrete
`ℤ`-submodule `L` of a finite-dimensional real normed space `E` spans `E`
(hence is a `ℤ`-lattice, `IsZLattice ℝ L`) if and only if its `ℤ`-rank equals
the `ℝ`-dimension of `E`. The finitely-generated / `≃ ℤᵐ` / cocompactness
parts of Lemma 14.3 are not proved here.

The reverse direction is Mathlib's `ZLattice.rank`; the new content is the
forward direction: restrict `L` to the submodule `L₀` of its own real span,
where `L₀` is a lattice by construction, and compare ranks.

Source-to-API map: v1 `GeometryOfNumbers.discrete_full_rank_iff_zlattice`
(`v1/Atlas/NumberTheoryI/code/GeometryOfNumbers.lean`, line 35) becomes
`Submodule.discrete_full_rank_iff_isZLattice` below.
-/

@[expose] public section

namespace Submodule

/-- **A discrete subgroup is a lattice iff it has full rank.** Let $E$ be a finite-dimensional
real normed space and let $L \subseteq E$ be a $\mathbb{Z}$-submodule (an additive subgroup) that
is discrete in the subspace topology. Then the $\mathbb{Z}$-rank of $L$ equals $\dim_{\mathbb{R}} E$
if and only if $L$ is a $\mathbb{Z}$-lattice in $E$, that is, $L$ spans $E$ over $\mathbb{R}$.

Source: ATLAS `NumberTheoryI`, Lemma 14.3 (full-rank clause only). -/
theorem discrete_full_rank_iff_isZLattice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ E ↔ IsZLattice ℝ L := by
  constructor
  · intro h
    constructor
    let W := span ℝ (L : Set E)
    let f := W.subtype
    let L₀ : Submodule ℤ W := L.comap (f.restrictScalars ℤ)
    have h_img : f '' L₀ = L := by
      rw [← LinearMap.coe_restrictScalars ℤ f, ← Submodule.map_coe (f.restrictScalars ℤ),
        Submodule.map_comap_eq_self]
      exact fun x hx ↦ LinearMap.mem_range.mpr ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
    have : DiscreteTopology L₀ := by
      refine DiscreteTopology.preimage_of_continuous_injective (L : Set E) ?_
        (injective_subtype _)
      exact LinearMap.continuous_of_finiteDimensional f
    have : IsZLattice ℝ L₀ := ⟨by
      rw [← (Submodule.map_injective_of_injective (injective_subtype _)).eq_iff,
        Submodule.map_span, Submodule.map_top, range_subtype, h_img]⟩
    have h_surj : L₀.map (f.restrictScalars ℤ) = L := by
      rw [Submodule.map_comap_eq_self]
      exact fun x hx ↦ LinearMap.mem_range.mpr ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
    have equiv : L₀ ≃ₗ[ℤ] L :=
      (L₀.equivMapOfInjective (f.restrictScalars ℤ) Subtype.val_injective).trans
        (LinearEquiv.ofEq _ _ h_surj)
    exact Submodule.eq_top_of_finrank_eq
      (by linarith [equiv.finrank_eq, ZLattice.rank ℝ L₀])
  · intro h
    exact ZLattice.rank ℝ L (hs := h)

end Submodule
