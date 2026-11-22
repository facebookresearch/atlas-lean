/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseEquivalence

/-!
# Public clients for pointwise equivalences

These clients use an arbitrary source simplicial set, apply the criterion to
isomorphisms in the homotopy category, detect a noninvertible component, and
check the case of a source with no vertices.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory MonoidalClosed
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.PointwiseEquivalenceTest

open SSet


variable {A C : SSet.{u}} [Quasicategory C]
  {F G : ((ihom A).obj C) _⦋0⦌}

/-- The public criterion supplies the literal homotopy-category isomorphism. -/
example (E : Edge F G)
    (h : ∀ a : A _⦋0⦌,
      ((E.map ((pre (yonedaEquiv.symm a)).app C)).map
        (evalDeltaZeroIso C).hom).IsEquivalence) : IsIso E.toHoHom :=
  (E.isEquivalence_iff_forall_eval_vertex).mpr h

/-- One noninvertible component prevents the edge from being an equivalence. -/
example (E : Edge F G) (a : A _⦋0⦌)
    (h : ¬ ((E.map ((pre (yonedaEquiv.symm a)).app C)).map
      (evalDeltaZeroIso C).hom).IsEquivalence) : ¬ E.IsEquivalence := by
  intro hE
  exact h ((E.isEquivalence_iff_forall_eval_vertex).mp hE a)

/-- With no source vertices, the criterion has no evaluation obligations. -/
example [IsEmpty (A _⦋0⦌)] (E : Edge F G) : E.IsEquivalence := by
  apply (E.isEquivalence_iff_forall_eval_vertex).mpr
  intro a
  exact isEmptyElim a


end MathlibExtTest.AlgebraicTopology.Quasicategory.PointwiseEquivalenceTest
