/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition

/-! # Tests for `FundamentalGroup.mapOfEq` composition and identity laws -/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace PiOneMapCompositionTests

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The identity law fires as a simp lemma. -/
example (x : X) (h : (ContinuousMap.id X) x = x) (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq (ContinuousMap.id X) h p = p := by
  simp only [FundamentalGroup.mapOfEq_id, MonoidHom.id_apply]

/-- Plain `simp` discharges the identity law, guarding `@[simp]` registration. -/
example (x : X) (h : (ContinuousMap.id X) x = x)
    (p q : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq (ContinuousMap.id X) h (p * q) = p * q := by
  simp

/-- The identity law with an explicit non-`rfl` proof. -/
example (x : X) (h : (ContinuousMap.id X) x = x) :
    FundamentalGroup.mapOfEq (ContinuousMap.id X) h = MonoidHom.id _ :=
  FundamentalGroup.mapOfEq_id x h

/-- The composition law on plain continuous maps. -/
example {x : X} {y : Y} {z : Z} (f : C(X, Y)) (g : C(Y, Z))
    (h1 : f x = y) (h2 : g y = z) (h : (g.comp f) x = z) :
    FundamentalGroup.mapOfEq (g.comp f) h =
      (FundamentalGroup.mapOfEq g h2).comp (FundamentalGroup.mapOfEq f h1) :=
  FundamentalGroup.mapOfEq_comp f g h1 h2 h

/-- Composing two identity maps induces the identity homomorphism. -/
example (x : X) :
    FundamentalGroup.mapOfEq
        ((ContinuousMap.id X).comp (ContinuousMap.id X)) rfl =
      MonoidHom.id (FundamentalGroup X x) := by
  have h1 : (ContinuousMap.id X) x = x := rfl
  have h : ((ContinuousMap.id X).comp (ContinuousMap.id X)) x = x := rfl
  have hcomp := FundamentalGroup.mapOfEq_comp (ContinuousMap.id X)
    (ContinuousMap.id X) h1 h1 h
  rw [FundamentalGroup.mapOfEq_id, MonoidHom.comp_id] at hcomp
  exact hcomp

/-- The composition law applies to `TopCat` homs, the π₁-diagram-chasing use case. -/
example {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {x : X} {y : Y} {z : Z} (h1 : f.hom x = y) (h2 : g.hom y = z)
    (h : (g.hom.comp f.hom) x = z) :
    FundamentalGroup.mapOfEq (g.hom.comp f.hom) h =
      (FundamentalGroup.mapOfEq g.hom h2).comp
        (FundamentalGroup.mapOfEq f.hom h1) :=
  FundamentalGroup.mapOfEq_comp f.hom g.hom h1 h2 h

end PiOneMapCompositionTests

end
