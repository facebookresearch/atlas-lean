/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FinrankComp

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

-- Consumer with the original binders.
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f]
    [IsFinite g] [Flat g] (m : ℕ) (hf : ∀ y : Y, f.finrank y = m) (z : Z) :
    (f ≫ g).finrank z = m * g.finrank z :=
  AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const f g m hf z

-- Higher-universe consumer.
example {X Y Z : Scheme.{2}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f]
    [IsFinite g] [Flat g] (m : ℕ) (hf : ∀ y : Y, f.finrank y = m) (z : Z) :
    (f ≫ g).finrank z = m * g.finrank z :=
  AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const f g m hf z

-- Boundary: when `m = 0`, the composite has rank `0` at every point,
-- showing the constant-rank hypothesis is what carries the factor.
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f]
    [IsFinite g] [Flat g] (hf : ∀ y : Y, f.finrank y = 0) (z : Z) :
    (f ≫ g).finrank z = 0 := by
  rw [AlgebraicGeometry.Scheme.Hom.finrank_comp_of_finrank_eq_const f g 0 hf z]
  simp
