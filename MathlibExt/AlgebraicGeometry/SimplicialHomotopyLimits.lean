/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Actual space-valued homotopy pullbacks and limits

The path input is a native pre-path object whose diagonal is a weak
homotopy equivalence and whose endpoint pair is a Kan fibration.
Homotopy pullbacks are then the literal native pullbacks of its endpoint
pair. The comparison from a commuting square uses the actual diagonal.

For a diagram, a chosen injectively fibrant replacement is constrained
by the lifting property against objectwise trivial monomorphisms. The
homotopy-limit model and its cone comparison are computed as the native
limit and native limit lift of that replacement.

These constructions concern spaces. Their weak homotopy equivalences
must not be used as equivalences of enhanced categories or DG nerves.
References: Bousfield--Kan, Homotopy limits, completions and
localizations, Chapters X--XI; PTVV, arXiv:1111.3209v4, conventions.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits

open CategoryTheory Limits HomotopicalAlgebra
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels

universe u

/-- A genuine Quillen path model, with actual endpoint and diagonal maps. -/
structure KanPathModel (Y : SSet.{u}) extends PrepathObject Y where
  kan : SSet.KanComplex Y
  diagonal_weak : WeakEquivalence ι
  endpoints_fibration : SSet.modelCategoryQuillen.J.rlp (prod.lift p₀ p₁)

/-- The actual pullback of an endpoint fibration. No homotopy invariant
or comparison map is a freely supplied field. -/
def homotopyPullback {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (P : KanPathModel Z) : SSet.{u} :=
  pullback (prod.map f g) (prod.lift P.p₀ P.p₁)

/-- The first actual projection from the homotopy pullback. -/
def first {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (P : KanPathModel Z) :
    homotopyPullback f g P ⟶ X :=
  pullback.fst _ _ ≫ prod.fst

/-- The second actual projection from the homotopy pullback. -/
def second {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (P : KanPathModel Z) :
    homotopyPullback f g P ⟶ Y :=
  pullback.fst _ _ ≫ prod.snd

/-- A strictly commuting square gives the fixed diagonal-path comparison. -/
def comparison {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (P : KanPathModel Z) (a : A ⟶ X) (b : A ⟶ Y) (h : a ≫ f = b ≫ g) :
    A ⟶ homotopyPullback f g P :=
  pullback.lift (prod.lift a b) (a ≫ f ≫ P.ι) (by
    apply prod.hom_ext <;> simp [Category.assoc, h])

@[reassoc (attr := simp)]
theorem comparison_first {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (P : KanPathModel Z) (a : A ⟶ X) (b : A ⟶ Y) (h : a ≫ f = b ≫ g) :
    comparison f g P a b h ≫ first f g P = a := by
  have hp : prod.lift a b ≫ prod.map f g =
      (a ≫ f ≫ P.ι) ≫ prod.lift P.p₀ P.p₁ := by
    apply prod.hom_ext <;> simp [Category.assoc, h]
  simpa only [comparison, first] using!
    (pullback.lift_fst_assoc (prod.lift a b) (a ≫ f ≫ P.ι) hp prod.fst).trans
      (prod.lift_fst a b)

@[reassoc (attr := simp)]
theorem comparison_second {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (P : KanPathModel Z) (a : A ⟶ X) (b : A ⟶ Y) (h : a ≫ f = b ≫ g) :
    comparison f g P a b h ≫ second f g P = b := by
  have hp : prod.lift a b ≫ prod.map f g =
      (a ≫ f ≫ P.ι) ≫ prod.lift P.p₀ P.p₁ := by
    apply prod.hom_ext <;> simp [Category.assoc, h]
  simpa only [comparison, second] using!
    (pullback.lift_fst_assoc (prod.lift a b) (a ≫ f ≫ P.ι) hp prod.snd).trans
      (prod.lift_snd a b)

/-- The actual based homotopy fibre for a specified point map. -/
def homotopyFibre {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⟶ Y) (P : KanPathModel Y) :
    SSet.{u} := homotopyPullback f x P

/-- Injective fibrancy in the actual diagram category, stated with its
objectwise trivial-cofibration lifting property. -/
def IsInjectivelyFibrant {J : Type u} [Category.{u} J] (D : J ⥤ SSet.{u}) : Prop :=
  ∀ (A B : J ⥤ SSet.{u}) (i : A ⟶ B),
    (∀ j, Mono (i.app j) ∧ WeakEquivalence (i.app j)) →
    ∀ f : A ⟶ D, ∃ g : B ⟶ D, i ≫ g = f

/-- Actual diagram replacement, retaining all naturality maps. -/
structure FibrantDiagramReplacement {J : Type u} [Category.{u} J]
    (D : J ⥤ SSet.{u}) where
  diagram : J ⥤ SSet.{u}
  map : D ⟶ diagram
  map_weak : ∀ j, WeakEquivalence (map.app j)
  fibrant : IsInjectivelyFibrant diagram

/-- The native limit of the specified injectively fibrant diagram. -/
def homotopyLimit {J : Type u} [Category.{u} J] {D : J ⥤ SSet.{u}}
    (R : FibrantDiagramReplacement D) : SSet.{u} := limit R.diagram

/-- The canonical comparison from the actual cone, not a supplied descent map. -/
def coneComparison {J : Type u} [Category.{u} J] {D : J ⥤ SSet.{u}}
    (R : FibrantDiagramReplacement D) (c : Cone D) : c.pt ⟶ homotopyLimit R :=
  limit.lift R.diagram ⟨c.pt, c.π ≫ R.map⟩

@[reassoc (attr := simp)]
theorem coneComparison_π {J : Type u} [Category.{u} J] {D : J ⥤ SSet.{u}}
    (R : FibrantDiagramReplacement D) (c : Cone D) (j : J) :
    coneComparison R c ≫ limit.π R.diagram j = c.π.app j ≫ R.map.app j := by
  exact limit.lift_π ⟨c.pt, c.π ≫ R.map⟩ j

end MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
