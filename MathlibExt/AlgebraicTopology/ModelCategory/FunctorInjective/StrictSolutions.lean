/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.BoundedGenerators
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorWeakLifting
import Mathlib.CategoryTheory.Presentable.SolutionSetCondition

/-!
# Original weak-arrow solutions for selected compact diagram cofibrations

The actual accessible inclusion supplies a working-small strict solution
family. The source, target and every original component square remain the
original ones. No diagram model, acyclicity, or Smith result is an input.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits
open HomotopicalAlgebra.CofibrantGenerationData

namespace HomotopicalAlgebra.FunctorInjective

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C]

/-- The actual solution data consists of original weak Arrows and original maps. -/
structure WeakArrowSolutionData (p : Arrow (D ⥤ C)) where
  /-- The solution labels are genuinely in the working universe. -/
  index : Type w
  /-- Every selected Arrow is an original objectwise weak Arrow. -/
  arrow : index → FunctorModelWeakArrow D C
  /-- The selected generator square is an actual original Arrow map. -/
  square : ∀ k, p ⟶ (arrow k).obj
  /-- Every incoming original weak square factors with equality of the whole square. -/
  factors : ∀ (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj),
    ∃ (k : index) (g : arrow k ⟶ q), square k ≫ g.hom = f

namespace WeakArrowSolutionData

variable {p : Arrow (D ⥤ C)} (a : WeakArrowSolutionData.{w} p)

/-- Every selected original solution is weak at every original diagram object. -/
theorem arrow_weak (k : a.index) (d : D) :
    weakEquivalences C ((a.arrow k).obj.hom.app d) :=
  (a.arrow k).property d

/-- The selected original square retains its full source and target transformations. -/
theorem square_equation (k : a.index) :
    (a.square k).left ≫ (a.arrow k).obj.hom = p.hom ≫ (a.square k).right :=
  (a.square k).w

/-- Each actual original component square is the corresponding component of that square. -/
theorem square_component_equation (k : a.index) (d : D) :
    (a.square k).left.app d ≫ (a.arrow k).obj.hom.app d =
      p.hom.app d ≫ (a.square k).right.app d :=
  congr_app (a.square_equation k) d

/-- The source transformation of a selected solution has all original action equations. -/
theorem square_source_naturality (k : a.index) {d e : D} (f : d ⟶ e) :
    p.left.map f ≫ (a.square k).left.app e =
      (a.square k).left.app d ≫ (a.arrow k).obj.left.map f :=
  (a.square k).left.naturality f

/-- The target transformation of a selected solution has all original action equations. -/
theorem square_target_naturality (k : a.index) {d e : D} (f : d ⟶ e) :
    p.right.map f ≫ (a.square k).right.app e =
      (a.square k).right.app d ≫ (a.arrow k).obj.right.map f :=
  (a.square k).right.naturality f

/-- A chosen factorization keeps its original working-small label. -/
def factorIndex (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj) : a.index :=
  (a.factors q f).choose

/-- The actual factor map is a map between the same original weak Arrows. -/
def factorMap (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj) :
    a.arrow (a.factorIndex q f) ⟶ q :=
  (a.factors q f).choose_spec.choose

/-- The chosen factorization is exactly the entire original incoming square. -/
theorem factorMap_equation (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj) :
    a.square (a.factorIndex q f) ≫ (a.factorMap q f).hom = f :=
  (a.factors q f).choose_spec.choose_spec

/-- Both endpoint transformations of the actual factorization are preserved. -/
theorem factorMap_endpoints (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj) :
    (a.square (a.factorIndex q f)).left ≫ (a.factorMap q f).hom.left = f.left ∧
      (a.square (a.factorIndex q f)).right ≫ (a.factorMap q f).hom.right = f.right :=
  ⟨congrArg Arrow.Hom.left (a.factorMap_equation q f),
    congrArg Arrow.Hom.right (a.factorMap_equation q f)⟩

/-- Both endpoint equations retain every original index component. -/
theorem factorMap_components (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj) (d : D) :
    (a.square (a.factorIndex q f)).left.app d ≫
        (a.factorMap q f).hom.left.app d = f.left.app d ∧
      (a.square (a.factorIndex q f)).right.app d ≫
        (a.factorMap q f).hom.right.app d = f.right.app d :=
  ⟨congr_app (a.factorMap_endpoints q f).1 d,
    congr_app (a.factorMap_endpoints q f).2 d⟩

/-- The factor map keeps the complete original weak-arrow commuting square. -/
theorem factorMap_square (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj) :
    (a.factorMap q f).hom.left ≫ q.obj.hom =
      (a.arrow (a.factorIndex q f)).obj.hom ≫ (a.factorMap q f).hom.right :=
  (a.factorMap q f).hom.w

/-- The chosen factor's source transformation retains every original action equation. -/
theorem factorMap_source_naturality (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj)
    {d e : D} (h : d ⟶ e) :
    (a.arrow (a.factorIndex q f)).obj.left.map h ≫
        (a.factorMap q f).hom.left.app e =
      (a.factorMap q f).hom.left.app d ≫ q.obj.left.map h :=
  (a.factorMap q f).hom.left.naturality h

/-- The chosen factor's target transformation retains every original action equation. -/
theorem factorMap_target_naturality (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj)
    {d e : D} (h : d ⟶ e) :
    (a.arrow (a.factorIndex q f)).obj.right.map h ≫
        (a.factorMap q f).hom.right.app e =
      (a.factorMap q f).hom.right.app d ≫ q.obj.right.map h :=
  (a.factorMap q f).hom.right.naturality h

/-- Precomposition by an actual source Arrow iso transports the same whole solution family. -/
def precomposeIso {p' : Arrow (D ⥤ C)} (e : p' ≅ p) : WeakArrowSolutionData.{w} p' where
  index := a.index
  arrow := a.arrow
  square k := e.hom ≫ a.square k
  factors q f := by
    obtain ⟨k, g, h⟩ := a.factors q (e.inv ≫ f)
    refine ⟨k, g, ?_⟩
    rw [Category.assoc, h]
    simp

/-- Source reindexing retains the actual entire original weak Arrow function. -/
theorem precomposeIso_arrow {p' : Arrow (D ⥤ C)} (e : p' ≅ p) :
    (a.precomposeIso e).arrow = a.arrow := rfl

/-- Reindexing changes each square by the actual complete iso map. -/
theorem precomposeIso_square {p' : Arrow (D ⥤ C)} (e : p' ≅ p) (k : a.index) :
    (a.precomposeIso e).square k = e.hom ≫ a.square k := rfl

/-- The complete square function under reindexing uses the original iso. -/
theorem precomposeIso_square_function {p' : Arrow (D ⥤ C)} (e : p' ≅ p) :
    (a.precomposeIso e).square = (fun k ↦ e.hom ≫ a.square k) := rfl

/-- Reindexing retains every original source component of every selected solution. -/
theorem precomposeIso_left_component {p' : Arrow (D ⥤ C)} (e : p' ≅ p)
    (k : a.index) (d : D) :
    ((a.precomposeIso e).square k).left.app d = e.hom.left.app d ≫ (a.square k).left.app d := rfl

/-- Reindexing retains every original target component of every selected solution. -/
theorem precomposeIso_right_component {p' : Arrow (D ⥤ C)} (e : p' ≅ p)
    (k : a.index) (d : D) :
    ((a.precomposeIso e).square k).right.app d =
      e.hom.right.app d ≫ (a.square k).right.app d := rfl

end WeakArrowSolutionData

section ActualAccessibleWeakInclusion

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} D C)

include d κLP s in
/-- The original objectwise weak inclusion has its native solution-set condition internally. -/
theorem weakArrow_solutionSetCondition :
    SolutionSetCondition.{w} (functorModelWeakArrows D C).ι := by
  obtain ⟨hCategory, hInclusion⟩ := d.functorModelWeakArrows_isAccessible s κLP
  let _ : IsAccessibleCategory.{w} (FunctorModelWeakArrow D C) := hCategory
  let _ : Functor.IsAccessible.{w} (functorModelWeakArrows D C).ι := hInclusion
  let _ : IsCardinalLocallyPresentable (D ⥤ C) κLP := s.isCardinalLocallyPresentable κLP
  let _ : IsAccessibleCategory.{w} (D ⥤ C) := ⟨κLP, inferInstance, inferInstance⟩
  let _ : IsAccessibleCategory.{w} (Arrow (D ⥤ C)) := inferInstance
  exact SolutionSetCondition.of_isCardinalAccessible (functorModelWeakArrows D C).ι

/-- Original weak solutions are selected from the proved actual accessible inclusion. -/
def weakArrowSolutionData (p : Arrow (D ⥤ C)) : WeakArrowSolutionData.{w} p := by
  let h := weakArrow_solutionSetCondition d κLP s p
  let ι := h.choose
  let a := h.choose_spec.choose
  let f := h.choose_spec.choose_spec.choose
  have hf := h.choose_spec.choose_spec.choose_spec
  exact { index := ι, arrow := a, square := f, factors := hf }

include d κLP s in
/-- Every original incoming weak Arrow map factors strictly through an actual chosen value. -/
theorem originalWeakArrow_strictSolutions (p : Arrow (D ⥤ C)) :
    ∃ (ι : Type w) (a : ι → FunctorModelWeakArrow D C)
      (f : ∀ k, p ⟶ (a k).obj),
      ∀ (q : FunctorModelWeakArrow D C) (g : p ⟶ q.obj),
        ∃ (k : ι) (h : a k ⟶ q), f k ≫ h.hom = g := by
  let a := weakArrowSolutionData d κLP s p
  exact ⟨a.index, a.arrow, a.square, a.factors⟩

variable {χ : Cardinal.{w}} [Fact χ.IsRegular] (b : BoundedGeneratorData D C χ)

/-- The actual bounded generator has internally selected solutions on the same original carrier. -/
def generatorSolutions (k : b.index) : WeakArrowSolutionData.{w} (b.arrow k) :=
  weakArrowSolutionData d κLP s (b.arrow k)

/-- The full selected bounded family receives strict solutions without a solution-set input. -/
theorem boundedGenerator_strictSolutions (k : b.index)
    (q : FunctorModelWeakArrow D C) (f : b.arrow k ⟶ q.obj) :
    ∃ (t : (generatorSolutions d κLP s b k).index)
      (g : (generatorSolutions d κLP s b k).arrow t ⟶ q),
      (generatorSolutions d κLP s b k).square t ≫ g.hom = f :=
  (generatorSolutions d κLP s b k).factors q f

/-- All selected generatorwise solution labels form the actual working-small dependent sum. -/
def solutionIndex := Σ k : b.index, (generatorSolutions d κLP s b k).index

/-- The collection retains every actual original generator label. -/
def solutionGenerator (t : solutionIndex d κLP s b) : b.index := t.1

/-- The collection retains the actual original weak Arrow selected under that label. -/
def solutionArrow (t : solutionIndex d κLP s b) : FunctorModelWeakArrow D C :=
  (generatorSolutions d κLP s b t.1).arrow t.2

/-- The collected square retains its original selected source generator and weak Arrow. -/
def solutionSquare (t : solutionIndex d κLP s b) :
    b.arrow (solutionGenerator d κLP s b t) ⟶ (solutionArrow d κLP s b t).obj :=
  (generatorSolutions d κLP s b t.1).square t.2

/-- The complete dependent-sum weak Arrow function is the original selected family function. -/
theorem solutionArrow_function :
    (fun t : solutionIndex d κLP s b ↦ (solutionArrow d κLP s b t).obj) =
      (fun t : solutionIndex d κLP s b ↦
        ((generatorSolutions d κLP s b t.1).arrow t.2).obj) := rfl

/-- Every collected Arrow retains weakness at all original index objects. -/
theorem solutionArrow_weak (t : solutionIndex d κLP s b) (a : D) :
    weakEquivalences C ((solutionArrow d κLP s b t).obj.hom.app a) :=
  (solutionArrow d κLP s b t).property a

/-- Any compact original source uses its actual whole representative iso. -/
def compactArrowSolutions (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) : WeakArrowSolutionData.{w} p :=
  (generatorSolutions d κLP s b (b.representative p hp)).precomposeIso
    (b.representativeIso p hp)

/-- The complete transported weak Arrow function is the same selected representative family. -/
theorem compactArrowSolutions_arrow (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    (compactArrowSolutions d κLP s b p hp).arrow =
      (generatorSolutions d κLP s b (b.representative p hp)).arrow := rfl

/-- A compact-source solution square is the original representative iso followed by its square. -/
theorem compactArrowSolutions_square (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p)
    (t : (generatorSolutions d κLP s b (b.representative p hp)).index) :
    (compactArrowSolutions d κLP s b p hp).square t =
      (b.representativeIso p hp).hom ≫
        (generatorSolutions d κLP s b (b.representative p hp)).square t := rfl

/-- Every incoming original weak square from any compact original arrow factors strictly. -/
theorem compactOriginalArrow_strictSolutions (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p)
    (q : FunctorModelWeakArrow D C) (f : p ⟶ q.obj) :
    ∃ (t : (compactArrowSolutions d κLP s b p hp).index)
      (g : (compactArrowSolutions d κLP s b p hp).arrow t ⟶ q),
      (compactArrowSolutions d κLP s b p hp).square t ≫ g.hom = f :=
  (compactArrowSolutions d κLP s b p hp).factors q f

/-- The base/index construction internally gives the whole selected generator solution family. -/
def constructedGeneratorSolutions
    (k : (boundedConstruction d κLP s).family.index) :
    WeakArrowSolutionData.{w} ((boundedConstruction d κLP s).family.arrow k) :=
  generatorSolutions d κLP s (boundedConstruction d κLP s).family k

end ActualAccessibleWeakInclusion

end HomotopicalAlgebra.FunctorInjective
