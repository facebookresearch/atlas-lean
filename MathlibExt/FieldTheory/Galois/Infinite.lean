/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Topological closure of subgroups of an infinite Galois group

For an infinite Galois extension `K / k`, the topological closure (for the
Krull topology) of a subgroup `H` of `Gal(K/k)` is the fixing subgroup of its
fixed field.
-/

@[expose] public section

namespace InfiniteGalois

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **The closure of a Galois subgroup is the fixing group of its fixed field.** Let $K/k$ be a
Galois extension, not necessarily finite, and give $\operatorname{Gal}(K/k)$ the Krull topology.
For every subgroup $H$ of $\operatorname{Gal}(K/k)$ with fixed field $K^H$, the closure of $H$
equals the subgroup of $\operatorname{Gal}(K/k)$ consisting of the automorphisms that fix $K^H$
pointwise. -/
theorem topologicalClosure_eq_fixingSubgroup_fixedField [IsGalois k K]
    (H : Subgroup Gal(K/k)) :
    H.topologicalClosure = (IntermediateField.fixedField H).fixingSubgroup := by
  apply le_antisymm
  · exact Subgroup.topologicalClosure_minimal H
      ((IntermediateField.le_iff_le _ _).mp le_rfl) (fixingSubgroup_isClosed _)
  · have hmono : H ≤ H.topologicalClosure := Subgroup.le_topologicalClosure H
    have hfix : IntermediateField.fixedField H.topologicalClosure ≤
        IntermediateField.fixedField H :=
      IntermediateField.fixedField_le hmono
    have hle : (IntermediateField.fixedField H).fixingSubgroup ≤
        (IntermediateField.fixedField H.topologicalClosure).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le hfix
    rwa [fixingSubgroup_fixedField
      ⟨H.topologicalClosure, H.isClosed_topologicalClosure⟩] at hle

end InfiniteGalois
