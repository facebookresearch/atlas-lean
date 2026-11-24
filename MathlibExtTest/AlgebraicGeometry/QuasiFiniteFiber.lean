/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.QuasiFiniteFiber

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

-- Consumer with the original binders.
example {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hx : ¬ f.QuasiFiniteAt x) :
    ∃ Z : Set X, IsClosed Z ∧ IsIrreducible Z ∧ x ∈ Z ∧ Z ≠ {x} ∧
      Z ⊆ f.base ⁻¹' closure {f.base x} :=
  f.exists_isClosed_isIrreducible_subset_preimage_closure_of_not_quasiFiniteAt x hx

-- Higher-universe consumer.
example {X Y : Scheme.{1}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hx : ¬ f.QuasiFiniteAt x) :
    ∃ Z : Set X, IsClosed Z ∧ IsIrreducible Z ∧ x ∈ Z ∧ Z ≠ {x} ∧
      Z ⊆ f.base ⁻¹' closure {f.base x} :=
  f.exists_isClosed_isIrreducible_subset_preimage_closure_of_not_quasiFiniteAt x hx

-- Boundary: the singleton `{x}` meets every clause of the conclusion except
-- the nontriviality clause `Z ≠ {x}`, so that clause carries the content.
example {X : Scheme.{u}} (x : X) : ¬ (({x} : Set X) ≠ {x}) := by simp
