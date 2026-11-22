/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseCore

/-!
# Pointwise Core Test
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite MonoidalClosed
open scoped Simplicial

universe u

namespace SSet

-- The public statement uses the actual evaluation composite in every degree.
example {A Q : SSet.{u}} [Quasicategory Q] {n : SimplexCategoryᵒᵖ}
    (s : ((ihom A).obj Q).obj n) :
    s ∈ (core ((ihom A).obj Q)).obj n ↔
      ∀ a : A _⦋0⦌,
        (((pre (yonedaEquiv.symm a)).app Q ≫ (evalDeltaZeroIso Q).hom).app n s) ∈
          (core Q).obj n :=
  mem_core_ihom_iff_forall_eval_vertex s

-- Degree zero retains every functor vertex without a source nonemptiness premise.
example {A Q : SSet.{u}} [Quasicategory Q] (s : ((ihom A).obj Q) _⦋0⦌) :
    ∀ a : A _⦋0⦌,
      (((pre (yonedaEquiv.symm a)).app Q ≫ (evalDeltaZeroIso Q).hom).app (op ⦋0⦌) s) ∈
        (core Q).obj (op ⦋0⦌) :=
  (mem_core_ihom_iff_forall_eval_vertex s).1 (mem_core_obj_zero s)


end SSet
