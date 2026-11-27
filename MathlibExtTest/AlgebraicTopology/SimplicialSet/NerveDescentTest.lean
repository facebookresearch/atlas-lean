/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveDescent

/-! # Descent into nerves and evaluation at vertices: tests

These tests exercise the public API of the neutral module
`MathlibExt.AlgebraicTopology.SimplicialSet.NerveDescent`: descent of
maps into nerves and its formulas at independent object and morphism
universes, detection on `2`-truncations, evaluation of maps and
edges at a vertex, mixed-universe clients (`Type 0` and
`ULiftHom.{1} (Fin 2)`), and — in the equal-universe adjunction
section — the nerve-adjunction transpose, unit, and counit. They
deliberately do not import Joyal categorical equivalences.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open SimplexCategory.Truncated SimplicialObject.Truncated
open scoped Simplicial

universe v u s

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace NerveDescentTest

section DescentFormulas

variable {Z X Y : SSet.{max u v}} {D E : Type u}
variable [Category.{v} D] [Category.{v} E]
variable (g : Z ⟶ CategoryTheory.nerve D) (z : Z _⦋0⦌)
variable {x y : Z _⦋0⦌} (e : SSet.Edge x y)

example : (SSet.descNerve g).obj (SSet.HomotopyCategory.mk z) =
    CategoryTheory.nerveEquiv (g.app (op ⦋0⦌) z) :=
  SSet.descNerve_obj_mk g z

example : (SSet.descNerve g).map (SSet.HomotopyCategory.homMk e) =
    CategoryTheory.nerve.homEquiv (e.map g) :=
  SSet.descNerve_map_homMk g e

example (f : X ⟶ Y) (h : Y ⟶ CategoryTheory.nerve D) :
    SSet.descNerve (f ≫ h) =
      SSet.mapHomotopyCategory f ⋙ SSet.descNerve h :=
  SSet.descNerve_precomp f h

example (K : D ⥤ E) :
    SSet.descNerve (g ≫ CategoryTheory.nerveMap K) =
      SSet.descNerve g ⋙ K :=
  SSet.descNerve_postcomp_nerveMap g K

/-- Descent determines the classifying map into a nerve. -/
example (a b : Z ⟶ CategoryTheory.nerve D)
    (h : SSet.descNerve a = SSet.descNerve b) : a = b :=
  SSet.descNerve_injective h

example : Function.Injective
    (fun g : Z ⟶ CategoryTheory.nerve D => SSet.descNerve g) :=
  SSet.descNerve_injective

example : SSet.nerveTruncEquiv Z D g = (SSet.truncation 2).map g :=
  SSet.nerveTruncEquiv_apply g

/-- The truncated descent itself, at a mixed-universe target. -/
example {V : SSet.Truncated.{1} 2}
    (φ : V ⟶ (SSet.truncation 2).obj (CategoryTheory.nerve (ULiftHom.{1} (Fin 2))))
    (x : V _⦋0⦌₂) :
    (SSet.descOfTruncation φ).obj (SSet.Truncated.HomotopyCategory.mk x) =
      CategoryTheory.nerveEquiv (φ.app _ x) :=
  SSet.descOfTruncation_obj_mk φ x

example {V : SSet.Truncated.{1} 2}
    (φ : V ⟶ (SSet.truncation 2).obj (CategoryTheory.nerve (ULiftHom.{1} (Fin 2))))
    {x₀ x₁ : V _⦋0⦌₂} (e : SSet.Truncated.Edge x₀ x₁) :
    (SSet.descOfTruncation φ).map (SSet.Truncated.HomotopyCategory.homMk e) =
      CategoryTheory.nerve.homEquiv (e.map φ) :=
  SSet.descOfTruncation_map_homMk φ e

example {V W : SSet.Truncated.{1} 2} (ψ : V ⟶ W)
    (φ : W ⟶ (SSet.truncation 2).obj (CategoryTheory.nerve (ULiftHom.{1} (Fin 2)))) :
    SSet.descOfTruncation (ψ ≫ φ) =
      SSet.Truncated.mapHomotopyCategory ψ ⋙ SSet.descOfTruncation φ :=
  SSet.descOfTruncation_comp ψ φ

end DescentFormulas

section MixedUniverseClients

/-- The category of small types: object universe `1`, morphism
universe `0`; its nerve lives in `SSet.{1}`. -/
example {Z : SSet.{1}} (g : Z ⟶ CategoryTheory.nerve (Type 0))
    (z : Z _⦋0⦌) :
    (SSet.descNerve g).obj (SSet.HomotopyCategory.mk z) =
      CategoryTheory.nerveEquiv (g.app (op ⦋0⦌) z) :=
  SSet.descNerve_obj_mk g z

example {Z : SSet.{1}} :
    Function.Injective
      (fun g : Z ⟶ CategoryTheory.nerve (Type 0) => SSet.descNerve g) :=
  SSet.descNerve_injective

example {Z : SSet.{1}} (g : Z ⟶ CategoryTheory.nerve (Type 0)) :
    SSet.nerveTruncEquiv Z (Type 0) g = (SSet.truncation 2).map g :=
  SSet.nerveTruncEquiv_apply g

/-- `ULiftHom.{1} (Fin 2)`: object universe `0`, morphism universe
`1`; its nerve also lives in `SSet.{1}`. -/
example {Z : SSet.{1}} (g : Z ⟶ CategoryTheory.nerve (ULiftHom.{1} (Fin 2)))
    {x y : Z _⦋0⦌} (e : SSet.Edge x y) :
    (SSet.descNerve g).map (SSet.HomotopyCategory.homMk e) =
      CategoryTheory.nerve.homEquiv (e.map g) :=
  SSet.descNerve_map_homMk g e

example {Z : SSet.{1}} :
    Function.Injective
      (fun g : Z ⟶ CategoryTheory.nerve (ULiftHom.{1} (Fin 2)) =>
        SSet.descNerve g) :=
  SSet.descNerve_injective

example {Z : SSet.{1}} {m₁ m₂ : Z ⟶ CategoryTheory.nerve (ULiftHom.{1} (Fin 2))}
    (e : SSet.Edge (SSet.ihomVertexEquiv Z _ m₁)
      (SSet.ihomVertexEquiv Z _ m₂)) (z : Z _⦋0⦌) :
    (CategoryTheory.nerve (ULiftHom.{1} (Fin 2))).Edge (m₁.app (op ⦋0⦌) z)
      (m₂.app (op ⦋0⦌) z) :=
  SSet.edgeAtVertex e z

end MixedUniverseClients

section Evaluation

variable {Z : SSet.{max u v}} {D : Type u} [Category.{v} D]

example (m : Z ⟶ CategoryTheory.nerve D) (z : Z _⦋0⦌) :
    ((SSet.evalDeltaZeroIso (CategoryTheory.nerve D)).hom).app (op ⦋0⦌)
        (((MonoidalClosed.pre (SSet.const z)).app
          (CategoryTheory.nerve D)).app (op ⦋0⦌)
          (SSet.ihomVertexEquiv Z _ m)) = m.app (op ⦋0⦌) z :=
  SSet.eval_app_pre_app_ihomVertexEquiv m z

/-- Mapping an edge along a composite is mapping it along the factors. -/
example {A B C : SSet.{s}} {a b : A _⦋0⦌} (e : SSet.Edge a b)
    (f : A ⟶ B) (g : B ⟶ C) : (e.map f).map g = e.map (f ≫ g) :=
  SSet.Edge.map_map e f g

example {m₁ m₂ : Z ⟶ CategoryTheory.nerve D}
    (e : SSet.Edge (SSet.ihomVertexEquiv Z _ m₁)
      (SSet.ihomVertexEquiv Z _ m₂)) (z : Z _⦋0⦌) :
    (CategoryTheory.nerve D).Edge (m₁.app (op ⦋0⦌) z)
      (m₂.app (op ⦋0⦌) z) :=
  SSet.edgeAtVertex e z

example {m₁ m₂ : Z ⟶ CategoryTheory.nerve D}
    (e : SSet.Edge (SSet.ihomVertexEquiv Z _ m₁)
      (SSet.ihomVertexEquiv Z _ m₂)) (z : Z _⦋0⦌) :
    (SSet.edgeAtVertex e z).edge =
      ((SSet.evalDeltaZeroIso (CategoryTheory.nerve D)).hom).app (op ⦋1⦌)
        (((MonoidalClosed.pre (SSet.const z)).app
          (CategoryTheory.nerve D)).app (op ⦋1⦌) e.edge) :=
  SSet.edgeAtVertex_edge_eq_app e z

end Evaluation

section NerveAdjunction

variable (Z X Y : SSet.{s}) (f : X ⟶ Y) {D : Type s} [Category.{s} D]

example (g : Z ⟶ CategoryTheory.nerve D) :
    (CategoryTheory.nerveAdjunction.homEquiv Z (Cat.of D)).symm g =
      (SSet.descNerve g).toCatHom :=
  SSet.nerveAdjunction_homEquiv_symm_apply g

example : Z ⟶ CategoryTheory.nerve Z.HomotopyCategory :=
  CategoryTheory.nerveAdjunction.unit.app Z

example : (SSet.truncation 2).map
        (CategoryTheory.nerveAdjunction.unit.app Z) =
    SSet.Truncated.HomotopyCategory.homToNerveMk
      (𝟭 ((SSet.truncation 2).obj Z).HomotopyCategory) :=
  SSet.truncation_map_nerveAdjunction_unit_app Z

example : SSet.descNerve (CategoryTheory.nerveAdjunction.unit.app Z) =
    𝟭 Z.HomotopyCategory :=
  SSet.descNerve_nerveAdjunction_unit_app Z

example : SSet.descNerve
        (CategoryTheory.nerveAdjunction.unit.app (Δ[0] : SSet.{0})) =
    𝟭 (Δ[0] : SSet.{0}).HomotopyCategory :=
  SSet.descNerve_nerveAdjunction_unit_app _

-- Naturality of the unit is the upstream adjunction-unit naturality,
-- specialized through the definitions of `nerveMap` and
-- `mapHomotopyCategory` (no wrapper lemma is kept for it).
example : f ≫ CategoryTheory.nerveAdjunction.unit.app Y =
    CategoryTheory.nerveAdjunction.unit.app X ≫
      CategoryTheory.nerveMap (SSet.mapHomotopyCategory f) :=
  CategoryTheory.nerveAdjunction.unit.naturality f

-- Descent after the canonical adjunction unit and a nerve map recovers
-- the functor.
example (K : Z.HomotopyCategory ⥤ D) :
    SSet.descNerve
        ((CategoryTheory.nerveAdjunction.unit.app Z :
            Z ⟶ CategoryTheory.nerve Z.HomotopyCategory) ≫
          CategoryTheory.nerveMap K) = K :=
  (SSet.descNerve_postcomp_nerveMap _ K).trans
    ((congrArg (· ⋙ K)
      (SSet.descNerve_nerveAdjunction_unit_app Z)).trans
        (Functor.id_comp K))

example :
    (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)).toFunctor =
      SSet.descNerve (𝟙 (CategoryTheory.nerve D)) :=
  SSet.nerveAdjunction_counit_app_toFunctor

example (x : (CategoryTheory.nerve D) _⦋0⦌) :
    (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)).toFunctor.obj
        (SSet.HomotopyCategory.mk x) = CategoryTheory.nerveEquiv x := by
  rw [SSet.nerveAdjunction_counit_app_toFunctor]
  exact SSet.descNerve_obj_mk _ _

end NerveAdjunction

end NerveDescentTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
