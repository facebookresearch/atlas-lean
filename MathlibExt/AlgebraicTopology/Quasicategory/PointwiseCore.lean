/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseEquivalence
public import MathlibExt.AlgebraicTopology.Quasicategory.Core

/-!
# The pointwise core of a function object

A simplex of a function object into a quasicategory lies in its core exactly
when every source-vertex evaluation lies in the target core. This is the
all-degree form of the pointwise edge equivalence criterion.

The condition characterizes the pointwise core subcomplex without introducing
a parallel public core construction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite MonoidalClosed
open scoped Simplicial

universe u

namespace SSet

private lemma edge_isEquivalence_map_iff {X Y : SSet.{u}}
    {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) (f : X ⟶ Y) :
    (e.map f).IsEquivalence ↔ (Edge.mk' (f.app (op ⦋1⦌) e.edge)).IsEquivalence :=
  Edge.isEquivalence_iff_of_edge_eq rfl

/-- The core of a function object into a quasicategory is detected in every
degree by evaluations at all vertices of its arbitrary source. -/
theorem mem_core_ihom_iff_forall_eval_vertex {A Q : SSet.{u}}
    [Quasicategory Q] {n : SimplexCategoryᵒᵖ} (s : ((ihom A).obj Q).obj n) :
    s ∈ (core ((ihom A).obj Q)).obj n ↔
      ∀ a : A _⦋0⦌,
        (((pre (yonedaEquiv.symm a)).app Q ≫ (evalDeltaZeroIso Q).hom).app n s) ∈
          (core Q).obj n := by
  constructor
  · intro hs a φ
    have h := (Edge.isEquivalence_iff_forall_eval_vertex
      (Edge.mk' (((ihom A).obj Q).map φ.op s))).1 (hs φ) a
    have h' := (edge_isEquivalence_map_iff _ _).1 h
    change (Edge.mk' (((pre (yonedaEquiv.symm a)).app Q ≫
      (evalDeltaZeroIso Q).hom).app (op ⦋1⦌) (((ihom A).obj Q).map φ.op s))).IsEquivalence at h'
    rw [NatTrans.naturality_apply] at h'
    exact h'
  · intro hs φ
    apply (Edge.isEquivalence_iff_forall_eval_vertex
      (Edge.mk' (((ihom A).obj Q).map φ.op s))).2
    intro a
    apply (edge_isEquivalence_map_iff _ _).2
    change (Edge.mk' (((pre (yonedaEquiv.symm a)).app Q ≫
      (evalDeltaZeroIso Q).hom).app (op ⦋1⦌) (((ihom A).obj Q).map φ.op s))).IsEquivalence
    rw [NatTrans.naturality_apply]
    exact hs a φ

end SSet
