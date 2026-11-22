/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBoundarySupportDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceLocalization
import MathlibExt.CategoryTheory.Presentable.OriginalFiniteLiftDescent

/-!
# Every actual original free boundary test descends to a countable original support

The SAME native boundary middle object over a weak original terminal
map has a genuinely weak terminal map. Its SAME full native horn right
factor therefore lifts every original free boundary. Finite original
source and target compactness descends that actual lift through the
original countable-support diagram, retaining its full boundary and
original terminal equations. All dimensions and ordered pairs remain.
-/

noncomputable section
universe u v
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryFiniteTestDescent
open OriginalBoundaryGoodTree OriginalBoundarySupportDiagram
variable {O : Type u} {C D : FixedObjects O} (f : C ⟶ D)

/-- The actual original full boundary projection transfers genuine terminal weakness to the SAME native middle object.
-/
theorem middle_terminal_weak (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D)) :
    FixedObjectModel.weakEquivalences O
      (CodiscreteTerminal.toTerminal (FreeFactorization.boundary f).Z) := by
  have hp : FixedObjectModel.weakEquivalences O (FreeFactorization.boundary f).p :=
    (FixedObjectModel.weakEquivalences_original_iff _).mpr
      (fun x y => (FreeFactorization.boundary_p_original f x y).2)
  have hc := (FixedObjectModel.weakEquivalences O).comp_mem _ _ hp hD
  have he := CodiscreteTerminal.toTerminal_naturality (FreeFactorization.boundary f).p
  exact (congrArg (fun k : (FreeFactorization.boundary f).Z ⟶ CodiscreteTerminal.object O =>
    FixedObjectModel.weakEquivalences O k) he).mp hc

/-- Every original free boundary end is genuinely finitely presentable, including degree zero and all loop labels. -/
theorem boundary_ends_presentable (i : (boundaryFamily O).toSet) :
    IsFinitelyPresentable.{u} i.val.left ∧ IsFinitelyPresentable.{u} i.val.right := by
  rcases i with ⟨⟨A, B, g⟩, hg⟩
  obtain ⟨⟨x, y, n⟩⟩ := hg
  exact ⟨inferInstance, inferInstance⟩

/-- Every full original boundary test over the SAME original replaced piece has its actual lift on a later countable
support. -/
theorem exists_lift
    (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))
    (B : Supports f) (i : (boundaryFamily O).toSet)
    (top : i.val.left ⟶ (replacedDiagram f).obj B) :
    ∃ (E : Supports f) (g : B ⟶ E) (l : i.val.right ⟶ (replacedDiagram f).obj E),
      i.val.hom ≫ l = top ≫ (replacedDiagram f).map g ∧
      l ≫ OriginalFibrantReplacement.right O ((diagram f).obj E) =
        CodiscreteTerminal.toTerminal i.val.right := by
  have hrlp : (boundaryFamily O).rlp
      (OriginalFibrantReplacement.right O (FreeFactorization.boundary f).Z) :=
    (OriginalFibrantReplacement.right_boundary_rlp_iff O _).mpr (middle_terminal_weak f hD)
  have hlp : HasLiftingProperty i.val.hom
      (OriginalFibrantReplacement.right O (FreeFactorization.boundary f).Z) := hrlp _ i.property
  let sq : CommSq (top ≫ (replacedCocone f).ι.app B) i.val.hom
      (OriginalFibrantReplacement.right O (FreeFactorization.boundary f).Z)
      (CodiscreteTerminal.toTerminal i.val.right) :=
    ⟨CodiscreteTerminal.isTerminal.hom_ext _ _⟩
  let _ : sq.HasLift := hlp.sq_hasLift sq
  let _ : IsFinitelyPresentable.{u} i.val.left := (boundary_ends_presentable i).1
  let _ : IsFinitelyPresentable.{u} i.val.right := (boundary_ends_presentable i).2
  obtain ⟨E, g, l, hl, _⟩ := Limits.OriginalFiniteLiftDescent.exists_lift
    (replacedIsColimit f) i.val.hom B top sq.lift sq.fac_left
  exact ⟨E, g, l, hl, CodiscreteTerminal.isTerminal.hom_ext _ _⟩

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryFiniteTestDescent

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceLocalization
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)
variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e))

/-- The SAME actually constructed original localization has a genuinely weak full terminal map. -/
theorem terminal_weak : FixedObjectModel.weakEquivalences walking.{u}
    (CodiscreteTerminal.toTerminal (fixedObject a e he)) := by
  apply (FixedObjectModel.weakEquivalences_iff _).mpr
  intro x y
  have hw := hom_toUnit_weak a e he x y
  have hm := CodiscreteTerminal.toTerminal_homMap (fixedObject a e he) x y
  exact (congrArg (fun k : FixedObjects.hom (fixedObject a e he) x y ⟶ 𝟙_ SSet.{u} =>
    SSet.realizationWeakEquivalences k) hm).mpr hw

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceLocalization
