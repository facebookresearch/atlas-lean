/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData

/-!
# Restricting strong deformation data

A commuting monic square and factorizations of the global retraction and
homotopy determine strong deformation data on the smaller map. Cancellation
proves the retraction, both endpoints and stationarity on the whole cylinder.
The resulting data retain the two supplied maps.

This is the categorical restriction calculation in Cisinski, Lemma 2.4.38
(2026), and Proposition 1.3.40 (2006). The calculation applies to every
functorial precylinder.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe v u

namespace HomotopicalAlgebra.Precylinder.StrongDeformationData

variable {C : Type u} [Category.{v} C] {P : Precylinder (𝟭 C)}
variable {Z X V Y : C} {i : X ⟶ Y}

/-- Restrict strong deformation data using a commuting monic square and
the actual factorizations of its retraction and whole homotopy. -/
def restrict (D : P.StrongDeformationData i)
    (a : Z ⟶ X) (b : Z ⟶ V) (j : V ⟶ Y) [Mono a] [Mono j]
    (w : a ≫ i = b ≫ j)
    (rV : V ⟶ Z) (hr : rV ≫ a = j ≫ D.retraction)
    (hV : P.I.obj V ⟶ V) (hH : P.I.map j ≫ D.homotopy.h = hV ≫ j) :
    P.StrongDeformationData b where
  retraction := rV
  retract := by
    apply (cancel_mono a).1
    calc
      (b ≫ rV) ≫ a = b ≫ (j ≫ D.retraction) := by
        rw [Category.assoc, hr]
      _ = (a ≫ i) ≫ D.retraction := by
        rw [← Category.assoc, ← w]
      _ = 𝟙 Z ≫ a := by
        rw [Category.assoc, D.retract, Category.comp_id, Category.id_comp]
  homotopy :=
    { h := hV
      h₀ := by
        apply (cancel_mono j).1
        calc
          ((P.app V).i₀ ≫ hV) ≫ j =
              (P.app V).i₀ ≫ (P.I.map j ≫ D.homotopy.h) := by
            rw [Category.assoc, ← hH]
          _ = j ≫ ((P.app Y).i₀ ≫ D.homotopy.h) := by
            simpa only [Functor.id_map, Category.assoc] using
              congrArg (fun k ↦ k ≫ D.homotopy.h) (P.i₀.naturality j).symm
          _ = 𝟙 V ≫ j := by
            rw [D.homotopy.h₀, Category.comp_id, Category.id_comp]
      h₁ := by
        apply (cancel_mono j).1
        calc
          ((P.app V).i₁ ≫ hV) ≫ j =
              (P.app V).i₁ ≫ (P.I.map j ≫ D.homotopy.h) := by
            rw [Category.assoc, ← hH]
          _ = j ≫ ((P.app Y).i₁ ≫ D.homotopy.h) := by
            simpa only [Functor.id_map, Category.assoc] using
              congrArg (fun k ↦ k ≫ D.homotopy.h) (P.i₁.naturality j).symm
          _ = j ≫ (D.retraction ≫ i) := by rw [D.homotopy.h₁]
          _ = (rV ≫ a) ≫ i := by rw [hr, Category.assoc]
          _ = (rV ≫ b) ≫ j := by rw [Category.assoc, w, Category.assoc]
      stationary := by
        apply (cancel_mono j).1
        calc
          (P.I.map b ≫ hV) ≫ j =
              P.I.map b ≫ (P.I.map j ≫ D.homotopy.h) := by
            rw [Category.assoc, ← hH]
          _ = P.I.map (b ≫ j) ≫ D.homotopy.h := by
            rw [Functor.map_comp, Category.assoc]
          _ = P.I.map (a ≫ i) ≫ D.homotopy.h := by rw [w]
          _ = P.I.map a ≫ ((P.app X).π ≫ i) := by
            rw [Functor.map_comp, Category.assoc, D.stationary]
          _ = (P.app Z).π ≫ (a ≫ i) := by
            simpa only [Functor.id_map, Category.assoc] using
              congrArg (fun k ↦ k ≫ i) (P.π.naturality a)
          _ = ((P.app Z).π ≫ b ≫ 𝟙 V) ≫ j := by
            rw [w, Category.comp_id, Category.assoc] }

end HomotopicalAlgebra.Precylinder.StrongDeformationData
