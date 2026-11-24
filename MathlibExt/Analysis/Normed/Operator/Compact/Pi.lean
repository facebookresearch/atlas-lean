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
# Compact operators into dependent products

Coordinate extraction works for arbitrary products. For a finite product,
coordinate compactness is also sufficient: finitely many source neighborhoods
can be synchronized and the product of the coordinate witnesses is compact.

These statements use the stock predicate on arbitrary functions, with only
a zero and topology on the source and topologies on the components. They do
not require target algebra, continuity of the function or preservation of zero.
-/

public section

open Set Filter
open scoped Topology

universe uX uI uB

variable {X : Type uX} [Zero X] [TopologicalSpace X]
variable {ι : Type uI} {β : ι → Type uB} [∀ i, TopologicalSpace (β i)]

/-- Each coordinate of a compact operator into a dependent product is compact.
The index type need not be finite. -/
theorem IsCompactOperator.eval {f : X → ∀ i, β i}
    (hf : IsCompactOperator f) (i : ι) :
    IsCompactOperator (fun x => f x i) := by
  rcases hf with ⟨K, hK, hPreimage⟩
  refine ⟨Function.eval i '' K, hK.image (continuous_apply i), ?_⟩
  exact Filter.mem_of_superset hPreimage fun x hx => ⟨f x, hx, rfl⟩

/-- An arbitrary function into a finite dependent product is a compact operator
if and only if each coordinate is a compact operator. -/
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
