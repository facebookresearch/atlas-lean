/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Fin.Basic

/-!
# Consistently ordered matrices

Young's consistent ordering is a property of the off-diagonal support in a fixed order of
indices. Its definition is combinatorial, unlike Varga's spectral condition that the eigenvalues
of `α L + α⁻¹ U` are independent of nonzero `α`, with `L` and `U` the strict lower and upper
parts of the Jacobi iteration matrix. Consistent ordering gives a bipartition by layer parity;
bipartiteness of the support alone does not depend on the index order.

## References

* Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd ed., SIAM, 2003, §4.2.5,
  Definition 4.13, Example 4.2 and form (4.42).
-/

@[expose] public section

namespace MetaMathlibExt.Matrix

variable {ι R : Type*} [LinearOrder ι] [Zero R]

/-- A square matrix is consistently ordered in Young's sense if its indices can be labeled by
layers such that each off-diagonal edge from a smaller index to a larger one increases the layer
by exactly one. Two distinct indices are adjacent if either corresponding entry is nonzero; the
diagonal is ignored. On a finite index type the fibers of the occurring labels give the partition
into layers. See Saad, *Iterative Methods for Sparse Linear Systems*, §4.2.5, Definition 4.13. -/
def IsConsistentlyOrdered (A : Matrix ι ι R) : Prop :=
  ∃ layer : ι → ℕ, ∀ ⦃i j⦄, i < j → (A i j ≠ 0 ∨ A j i ≠ 0) → layer j = layer i + 1

/-- A block-tridiagonal matrix with diagonal diagonal blocks is consistently ordered when the
blocks occur consecutively in index order. The monotone block map is the layer labeling, and
`hzero` allows off-diagonal entries only between successive blocks. Singleton blocks give
ordinary tridiagonal matrices, and two blocks give Saad's form (4.42). -/
theorem IsConsistentlyOrdered.of_block_tridiagonal {p : ℕ} {A : Matrix ι ι R}
    (block : ι → Fin p) (hblock : Monotone block)
    (hzero : ∀ ⦃i j⦄, i ≠ j → (block i : ℕ) + 1 ≠ (block j : ℕ) →
      (block j : ℕ) + 1 ≠ (block i : ℕ) → A i j = 0) :
    IsConsistentlyOrdered A := by
  refine ⟨fun i ↦ (block i : ℕ), ?_⟩
  intro i j hij hadj
  have hle : (block i : ℕ) ≤ (block j : ℕ) := hblock hij.le
  have hrev : (block j : ℕ) + 1 ≠ (block i : ℕ) := by omega
  by_contra h
  have hf : (block i : ℕ) + 1 ≠ (block j : ℕ) := Ne.symm h
  exact hadj.elim (fun hne ↦ hne (hzero hij.ne hf hrev))
    (fun hne ↦ hne (hzero hij.ne.symm hrev hf))

/-- The undirected off-diagonal support of a consistently ordered matrix is bipartite (Young's
Property A): the parity of the layer label gives a proper two-coloring. -/
theorem IsConsistentlyOrdered.colorable_support {A : Matrix ι ι R}
    (hA : IsConsistentlyOrdered A) :
    (SimpleGraph.fromRel (fun i j ↦ A i j ≠ 0)).Colorable 2 := by
  obtain ⟨layer, hlayer⟩ := hA
  refine ⟨SimpleGraph.Coloring.mk (fun i ↦ ⟨layer i % 2, Nat.mod_lt _ (by decide)⟩) ?_⟩
  intro i j hadj hcolor
  obtain ⟨hne, hsupp⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
  have hmod : layer i % 2 = layer j % 2 := congrArg Fin.val hcolor
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep := hlayer hlt hsupp
    omega
  · have hstep := hlayer hgt hsupp.symm
    omega

end MetaMathlibExt.Matrix
