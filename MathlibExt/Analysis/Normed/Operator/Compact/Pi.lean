/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Order.Filter.Finite

/-!
# Compact functions into dependent products

Let `X` be a topological space with a distinguished zero and `Y_i` topological spaces. A
function `f : X → ∏i Y_i` is a compact operator when it maps some neighborhood of zero into a
compact set.

Such a function has compact coordinate maps `x ↦ f(x)_i` for arbitrary indices. For a finite
index type, compactness of every coordinate is also sufficient. No continuity of `f`,
preservation of zero or algebraic structure on the target spaces is required.
-/

public section

open Set Filter
open scoped Topology

universe uX uI uB

variable {X : Type uX} [Zero X] [TopologicalSpace X]
variable {ι : Type uI} {β : ι → Type uB} [∀ i, TopologicalSpace (β i)]

/-- **Compact coordinate of a function into a product.** Let `X` be a topological space with
zero, `Y_i` any family of topological spaces, and `f : X → ∏i Y_i` map a neighborhood of
zero into a compact set. For every index `i`, the coordinate function `x ↦ f(x)_i` is a
compact operator in the same neighborhood sense. The index type may be infinite. -/
theorem IsCompactOperator.eval {f : X → ∀ i, β i}
    (hf : IsCompactOperator f) (i : ι) :
    IsCompactOperator (fun x => f x i) := by
  rcases hf with ⟨K, hK, hPreimage⟩
  refine ⟨Function.eval i '' K, hK.image (continuous_apply i), ?_⟩
  exact Filter.mem_of_superset hPreimage fun x hx => ⟨f x, hx, rfl⟩

/-- **Compactness of a finite product function from its coordinates.** Let `X` be a
topological space with zero, `Y_i` topological spaces indexed by a finite type, and `f : X
→ ∏i Y_i` any function. It maps a neighborhood of zero into a compact set exactly when
each coordinate map does. Continuity or linearity of `f` is not required. -/
theorem isCompactOperator_pi_iff [Finite ι] (f : X → ∀ i, β i) :
    IsCompactOperator f ↔ ∀ i, IsCompactOperator (fun x => f x i) := by
  constructor
  · intro hf i
    exact hf.eval i
  · intro hCoordinates
    have hWitnesses : ∀ i, ∃ K : Set (β i), IsCompact K ∧
        (fun x => f x i) ⁻¹' K ∈ (𝓝 0 : Filter X) := hCoordinates
    let K (i : ι) : Set (β i) := Classical.choose (hWitnesses i)
    have hK : ∀ i, IsCompact (K i) :=
      fun i => (Classical.choose_spec (hWitnesses i)).1
    have hNeighborhoods : ∀ i, (fun x => f x i) ⁻¹' K i ∈ (𝓝 0 : Filter X) :=
      fun i => (Classical.choose_spec (hWitnesses i)).2
    refine ⟨{y : ∀ i, β i | ∀ i, y i ∈ K i}, isCompact_pi_infinite hK, ?_⟩
    have hPreimage : f ⁻¹' {y : ∀ i, β i | ∀ i, y i ∈ K i} =
        ⋂ i, (fun x => f x i) ⁻¹' K i := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hPreimage]
    exact Filter.iInter_mem.mpr hNeighborhoods
