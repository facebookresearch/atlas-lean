/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Tactic.FinCases

/-!
# Actual categorical homotopy models for enhanced descent

An equivalence edge is fixed by its inverse and the two inverse
2-simplices. The core is the literal subcomplex of simplices whose
edges are equivalences. Categorical weak equivalence is the Joyal
mapping test: precomposition induces weak homotopy equivalences on
the cores of all functor quasicategories.

A categorical diagram replacement takes values in a universe containing
the actual index objects and morphisms. It uses the categorical test and the
injective lifting property against objectwise trivial monomorphisms.
Its limit and cone comparison are native limits and native limit lifts.
No Kan-space replacement or space weak equivalence is substituted for
a categorical replacement. In particular no Perf or arc-descent theorem
is contained in these model choices.

References: Lurie, Higher Topos Theory, §§1.2.5 and 2.2.5;
Joyal, The theory of quasi-categories and its applications.
The underlying nerves, simplicial Hom and limits are native Mathlib.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.QuasicategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

universe u v w

/-- An actual edge with a two-sided inverse, including both inverse 2-simplices. -/
def IsEquivalenceEdge (X : SSet) (e : X _⦋1⦌) : Prop :=
  ∃ (g : X _⦋1⦌) (a b : X _⦋2⦌),
    X.δ 2 a = e ∧ X.δ 0 a = g ∧ X.δ 1 a = X.σ 0 (X.δ 1 e) ∧
    X.δ 2 b = g ∧ X.δ 0 b = e ∧ X.δ 1 b = X.σ 0 (X.δ 0 e)

/-- Every simplicial map preserves the displayed inverse-edge data. -/
theorem IsEquivalenceEdge.map {X Y : SSet} (f : X ⟶ Y) {e : X _⦋1⦌}
    (h : IsEquivalenceEdge X e) : IsEquivalenceEdge Y (f.app (op ⦋1⦌) e) := by
  obtain ⟨g, a, b, hae, hag, haa, hbg, hbe, hbb⟩ := h
  refine ⟨f.app (op ⦋1⦌) g, f.app (op ⦋2⦌) a, f.app (op ⦋2⦌) b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← SSet.δ_naturality_apply, hae]
  · rw [← SSet.δ_naturality_apply, hag]
  · rw [← SSet.δ_naturality_apply, haa, SSet.σ_naturality_apply, SSet.δ_naturality_apply]
  · rw [← SSet.δ_naturality_apply, hbg]
  · rw [← SSet.δ_naturality_apply, hbe]
  · rw [← SSet.δ_naturality_apply, hbb, SSet.σ_naturality_apply, SSet.δ_naturality_apply]

/-- The actual edge from vertex i to vertex j of a simplex. -/
def edgeInclusion {n : SimplexCategory} (i j : Fin (n.len + 1)) (h : i ≤ j) :
    ⦋1⦌ ⟶ n :=
  SimplexCategory.Hom.mk
    { toFun := fun t => if t = 0 then i else j
      monotone' := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all }

/-- Edge inclusions compose with the literal order map of a simplex. -/
theorem edgeInclusion_comp {n m : SimplexCategory} (f : n ⟶ m)
    (i j : Fin (n.len + 1)) (h : i ≤ j) :
    edgeInclusion i j h ≫ f =
      edgeInclusion (f.toOrderHom i) (f.toOrderHom j) (f.toOrderHom.monotone h) := by
  ext t
  fin_cases t <;> rfl

/-- The actual simplices of the maximal groupoid core. -/
def IsCoreSimplex (X : SSet) (n : SimplexCategoryᵒᵖ) (x : X.obj n) : Prop :=
  ∀ (i j : Fin (n.unop.len + 1)) (h : i ≤ j),
    IsEquivalenceEdge X (X.map (edgeInclusion i j h).op x)

/-- The literal core subcomplex retains exactly the equivalence-edge simplices. -/
def coreSubcomplex (X : SSet) : X.Subcomplex where
  obj n := {x | IsCoreSimplex X n x}
  map {n m} f x hx := by
    intro i j hij
    have h := hx (f.unop.toOrderHom i) (f.unop.toOrderHom j)
      (f.unop.toOrderHom.monotone hij)
    have he := edgeInclusion_comp f.unop i j hij
    rw [← he] at h
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      Quiver.Hom.op_unop] using h

/-- The actual simplicial core, rather than a supplied homotopy invariant. -/
abbrev core (X : SSet) : SSet := (coreSubcomplex X).toSSet

/-- Simplicial maps induce their literal maps on core simplices. -/
def coreMap {X Y : SSet} (f : X ⟶ Y) : core X ⟶ core Y where
  app n := ↾fun x => ⟨f.app n x.val, by
    intro i j hij
    have h := IsEquivalenceEdge.map f (x.property i j hij)
    have hn := congrArg (fun g => g x.val) (f.naturality (edgeInclusion i j hij).op)
    change f.app (op ⦋1⦌) (X.map (edgeInclusion i j hij).op x.val) =
      Y.map (edgeInclusion i j hij).op (f.app n x.val) at hn
    rwa [← hn]⟩
  naturality n m g := by
    ext x
    apply Subtype.ext
    exact congrArg (fun f => f x.val) (f.naturality g)

@[simp]
theorem coreMap_id (X : SSet) : coreMap (𝟙 X) = 𝟙 (core X) := by
  ext n x
  rfl

@[simp]
theorem coreMap_comp {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coreMap (f ≫ g) = coreMap f ≫ coreMap g := by
  ext n x
  rfl

/-- Actual precomposition on the native simplicial functor object. -/
def precomposition {X Y : SSet} (f : X ⟶ Y) (Z : SSet) :
    mapping Y Z ⟶ mapping X Z :=
  ((SimplicialCategory.sHomFunctor SSet).map f.op).app Z

/-- Joyal categorical weak equivalence, tested on all native functor cores. -/
def CategoricalWeakEquivalence {X Y : SSet} (f : X ⟶ Y) : Prop :=
  ∀ (Z : SSet), SSet.Quasicategory Z →
    WeakEquivalence (coreMap (precomposition f Z))

/-- The injective categorical lifting property on an actual diagram. -/
def IsCategoricallyFibrant {J : Type v} [Category.{w} J] (D : J ⥤ SSet.{max u v w}) : Prop :=
  ∀ (A B : J ⥤ SSet.{max u v w}) (i : A ⟶ B),
    (∀ j, Mono (i.app j) ∧ CategoricalWeakEquivalence (i.app j)) →
    ∀ f : A ⟶ D, ∃ g : B ⟶ D, i ≫ g = f

/-- An actual categorical diagram replacement; arc-descent is no field. -/
structure CategoricalDiagramReplacement {J : Type v} [Category.{w} J] (D : J ⥤ SSet.{max u v w}) where
  diagram : J ⥤ SSet.{max u v w}
  augmentation : D ⟶ diagram
  weak : ∀ j, CategoricalWeakEquivalence (augmentation.app j)
  fibrant : IsCategoricallyFibrant.{u, v, w} diagram
  quasicategory : ∀ j, SSet.Quasicategory (diagram.obj j)

/-- The actual categorical homotopy-limit model of the replacement. -/
def homotopyLimit {J : Type v} [Category.{w} J] {D : J ⥤ SSet.{max u v w}}
    (R : CategoricalDiagramReplacement.{u, v, w} D) : SSet.{max u v w} := limit R.diagram

/-- The canonical categorical comparison of the specified cone. -/
def coneComparison {J : Type v} [Category.{w} J] {D : J ⥤ SSet.{max u v w}}
    (R : CategoricalDiagramReplacement.{u, v, w} D) (c : Cone D) :
    c.pt ⟶ homotopyLimit.{u, v, w} R :=
  limit.lift R.diagram ⟨c.pt, c.π ≫ R.augmentation⟩

@[reassoc (attr := simp)]
theorem coneComparison_π {J : Type v} [Category.{w} J] {D : J ⥤ SSet.{max u v w}}
    (R : CategoricalDiagramReplacement.{u, v, w} D) (c : Cone D) (j : J) :
    coneComparison.{u, v, w} R c ≫ limit.π R.diagram j =
      c.π.app j ≫ R.augmentation.app j :=
  limit.lift_π ⟨c.pt, c.π ≫ R.augmentation⟩ j

end MathlibExt.AlgebraicTopology.QuasicategoricalModels
