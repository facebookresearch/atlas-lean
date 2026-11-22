/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.MappingFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyModel
import MathlibExt.AlgebraicTopology.SimplicialObject.MatchingOne
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Reedy-fibrant endpoint maps and their original mapping fibres

The actual terminal-relative matching arrow is compared with the absolute
matching arrow. The native degree-one matching comparison, including its
source–target product swap, then gives the original `(d₁,d₀)` Kan fibration.
The original chosen pullback mapping fibres inherit Kan-ness.

Source: Rezk (2001), Section 5.1. All comparisons retain the original maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.SimplicialObject
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.ReedyModel

private theorem matchingDiagram_preservesTerminal (n : ℕ) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (matchingDiagramFunctor (C := SSet.{u}) n) :=
  ⟨fun {K} => ⟨fun c {hc} => ⟨by
    apply evaluationJointlyReflectsLimits _ (fun a => ?_)
    change IsLimit (((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj a.obj.right).mapCone c)
    exact isLimitOfPreserves _ hc⟩⟩⟩

private theorem matchingObject_preservesTerminal (n : ℕ) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (matchingObjectFunctor (C := SSet.{u}) n) := by
  let := matchingDiagram_preservesTerminal.{u} n
  change PreservesLimitsOfShape (Discrete PEmpty.{1}) (matchingDiagramFunctor n ⋙ lim)
  infer_instance

/-- The matching map of the actual terminal diagram is its native terminal-object isomorphism. -/
def terminalMatchingMapIso (n : ℕ) :
    (⊤_ SimplicialSpace.{u}).diagram.obj (op ⦋n⦌) ≅
      matchingObject (⊤_ SimplicialSpace.{u}).diagram n := by
  let := matchingObject_preservesTerminal.{u} n
  let hdiagram : IsTerminal (⊤_ SimplicialSpace.{u}).diagram :=
    IsTerminal.isTerminalObj SimplicialSpace.forget (⊤_ SimplicialSpace.{u}) terminalIsTerminal
  let hlevel := IsTerminal.isTerminalObj
    ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op ⦋n⦌))
    (⊤_ SimplicialSpace.{u}).diagram hdiagram
  let hmatching := IsTerminal.isTerminalObj (matchingObjectFunctor n)
    (⊤_ SimplicialSpace.{u}).diagram hdiagram
  let : IsIso (matchingMap (⊤_ SimplicialSpace.{u}).diagram n) :=
    isIso_of_isTerminal hlevel hmatching _
  exact asIso (matchingMap (⊤_ SimplicialSpace.{u}).diagram n)

private def terminalDiagram_isTerminal : IsTerminal (⊤_ SimplicialSpace.{u}).diagram :=
  IsTerminal.isTerminalObj SimplicialSpace.forget (⊤_ SimplicialSpace.{u}) terminalIsTerminal

private def terminalLevel_isTerminal (n : ℕ) :
    IsTerminal ((⊤_ SimplicialSpace.{u}).diagram.obj (op ⦋n⦌)) :=
  IsTerminal.isTerminalObj ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op ⦋n⦌))
    (⊤_ SimplicialSpace.{u}).diagram terminalDiagram_isTerminal

private def terminalMatching_isTerminal (n : ℕ) :
    IsTerminal (matchingObject (⊤_ SimplicialSpace.{u}).diagram n) := by
  let := matchingObject_preservesTerminal.{u} n
  exact IsTerminal.isTerminalObj (matchingObjectFunctor n)
    (⊤_ SimplicialSpace.{u}).diagram terminalDiagram_isTerminal

private theorem terminalMatchingMap_isIso (n : ℕ) :
    IsIso (matchingMap (⊤_ SimplicialSpace.{u}).diagram n) :=
  isIso_of_isTerminal (terminalLevel_isTerminal n) (terminalMatching_isTerminal n) _

/-- The forward terminal matching comparison is the original matching map. -/
@[simp]
theorem terminalMatchingMapIso_hom (n : ℕ) :
    (terminalMatchingMapIso.{u} n).hom = matchingMap (⊤_ SimplicialSpace.{u}).diagram n := rfl

/-- The second projection identifies the original terminal-relative matching object with MₙW. -/
def terminalRelativeMatchingObjectIso (W : SimplicialSpace.{u}) (n : ℕ) :
    relativeMatchingObject (terminal.from W).hom n ≅ matchingObject W.diagram n := by
  let := terminalMatchingMap_isIso.{u} n
  exact asIso (pullback.snd (matchingMap (⊤_ SimplicialSpace.{u}).diagram n)
    ((matchingObjectFunctor n).map (terminal.from W).hom))

/-- The forward target comparison is the literal original second pullback projection. -/
@[simp]
theorem terminalRelativeMatchingObjectIso_hom (W : SimplicialSpace.{u}) (n : ℕ) :
    (terminalRelativeMatchingObjectIso W n).hom =
      pullback.snd (matchingMap (⊤_ SimplicialSpace.{u}).diagram n)
        ((matchingObjectFunctor n).map (terminal.from W).hom) := rfl

/-- The inverse comparison retains the second original projection. -/
@[reassoc (attr := simp)]
theorem terminalRelativeMatchingObjectIso_inv_snd (W : SimplicialSpace.{u}) (n : ℕ) :
    (terminalRelativeMatchingObjectIso W n).inv ≫
        pullback.snd (matchingMap (⊤_ SimplicialSpace.{u}).diagram n)
          ((matchingObjectFunctor n).map (terminal.from W).hom) =
      𝟙 (matchingObject W.diagram n) :=
  (terminalRelativeMatchingObjectIso W n).inv_hom_id

/-- The inverse comparison retains the first projection through the original terminal map. -/
@[reassoc]
theorem terminalRelativeMatchingObjectIso_inv_fst (W : SimplicialSpace.{u}) (n : ℕ) :
    (terminalRelativeMatchingObjectIso W n).inv ≫
        pullback.fst (matchingMap (⊤_ SimplicialSpace.{u}).diagram n)
          ((matchingObjectFunctor n).map (terminal.from W).hom) =
      (matchingObjectFunctor n).map (terminal.from W).hom ≫ (terminalMatchingMapIso n).inv := by
  apply (cancel_mono (terminalMatchingMapIso.{u} n).hom).mp
  rw [Category.assoc, terminalMatchingMapIso_hom, pullback.condition,
    ← Category.assoc, terminalRelativeMatchingObjectIso_inv_snd, Category.id_comp]
  have hcancel : (terminalMatchingMapIso.{u} n).inv ≫
      matchingMap (⊤_ SimplicialSpace.{u}).diagram n = 𝟙 _ := by
    rw [← terminalMatchingMapIso_hom]
    exact Iso.inv_hom_id _
  rw [Category.assoc, hcancel, Category.comp_id]

/-- The original terminal-relative matching arrow is the absolute matching arrow, in every
degree. -/
def terminalRelativeMatchingArrowIso (W : SimplicialSpace.{u}) (n : ℕ) :
    Arrow.mk (relativeMatchingMap (terminal.from W).hom n) ≅
      Arrow.mk (matchingMap W.diagram n) :=
  Arrow.isoMk (Iso.refl _) (terminalRelativeMatchingObjectIso W n) (by
    change 𝟙 (W.diagram.obj (op ⦋n⦌)) ≫ matchingMap W.diagram n =
      relativeMatchingMap (terminal.from W).hom n ≫ (terminalRelativeMatchingObjectIso W n).hom
    rw [Category.id_comp, terminalRelativeMatchingObjectIso_hom, relativeMatchingMap_snd])

/-- The source of the forward whole Arrow comparison is literally identity. -/
@[simp]
theorem terminalRelativeMatchingArrowIso_hom_left (W : SimplicialSpace.{u}) (n : ℕ) :
    ((terminalRelativeMatchingArrowIso W n).hom).left = 𝟙 (W.diagram.obj (op ⦋n⦌)) := rfl

/-- The source of the inverse whole Arrow comparison is literally identity. -/
@[simp]
theorem terminalRelativeMatchingArrowIso_inv_left (W : SimplicialSpace.{u}) (n : ℕ) :
    ((terminalRelativeMatchingArrowIso W n).inv).left = 𝟙 (W.diagram.obj (op ⦋n⦌)) := rfl

/-- The forward whole Arrow target is exactly the second original pullback projection. -/
@[simp]
theorem terminalRelativeMatchingArrowIso_hom_right (W : SimplicialSpace.{u}) (n : ℕ) :
    ((terminalRelativeMatchingArrowIso W n).hom).right =
      (terminalRelativeMatchingObjectIso W n).hom := rfl

/-- The inverse whole Arrow target is the inverse original projection comparison. -/
@[simp]
theorem terminalRelativeMatchingArrowIso_inv_right (W : SimplicialSpace.{u}) (n : ℕ) :
    ((terminalRelativeMatchingArrowIso W n).inv).right =
      (terminalRelativeMatchingObjectIso W n).inv := rfl

/-- The native whole degree-one matching arrow is the original `(d₁,d₀)` endpoint arrow. -/
def matchingEndpointArrowIso (W : SimplicialSpace.{u}) :
    Arrow.mk (matchingMap W.diagram 1) ≅ Arrow.mk (mappingEndpoint W) :=
  matchingOneSourceTargetArrowIso.app W.diagram

/-- The forward endpoint comparison keeps the original degree-one source. -/
@[simp]
theorem matchingEndpointArrowIso_hom_left (W : SimplicialSpace.{u}) :
    (matchingEndpointArrowIso W).hom.left = 𝟙 (W.diagram.obj (op ⦋1⦌)) := rfl

/-- The inverse endpoint comparison keeps the original degree-one source. -/
@[simp]
theorem matchingEndpointArrowIso_inv_left (W : SimplicialSpace.{u}) :
    (matchingEndpointArrowIso W).inv.left = 𝟙 (W.diagram.obj (op ⦋1⦌)) := rfl

/-- The forward target includes the native swap from `(d₀,d₁)` to `(d₁,d₀)`. -/
theorem matchingEndpointArrowIso_hom_right (W : SimplicialSpace.{u}) :
    (matchingEndpointArrowIso W).hom.right = matchingOneIso.hom.app W.diagram ≫
      (prod.braiding (W.diagram.obj (op ⦋0⦌)) (W.diagram.obj (op ⦋0⦌))).hom :=
  matchingOneSourceTargetIso_hom_eq W.diagram

/-- The inverse target uses the same native inverse swap and matching comparison. -/
theorem matchingEndpointArrowIso_inv_right (W : SimplicialSpace.{u}) :
    (matchingEndpointArrowIso W).inv.right =
      (prod.braiding (W.diagram.obj (op ⦋0⦌)) (W.diagram.obj (op ⦋0⦌))).inv ≫
        matchingOneIso.inv.app W.diagram :=
  matchingOneSourceTargetIso_inv_eq W.diagram

/-- Forward target naturality keeps the original outer-zero morphism in both product factors. -/
@[reassoc]
theorem matchingEndpointArrowIso_hom_right_naturality {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) :
    (matchingObjectFunctor 1).map f.hom ≫ (matchingEndpointArrowIso V).hom.right =
      (matchingEndpointArrowIso W).hom.right ≫
        prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)) :=
  matchingOneSourceTargetIso_hom_naturality f.hom

/-- Inverse target naturality retains the same original matching and product morphisms. -/
@[reassoc]
theorem matchingEndpointArrowIso_inv_right_naturality {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) :
    prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)) ≫
        (matchingEndpointArrowIso V).inv.right =
      (matchingEndpointArrowIso W).inv.right ≫ (matchingObjectFunctor 1).map f.hom :=
  matchingOneSourceTargetIso_inv_naturality f.hom

/-- The whole original terminal-relative degree-one arrow is the original endpoint arrow. -/
def terminalRelativeEndpointArrowIso (W : SimplicialSpace.{u}) :
    Arrow.mk (relativeMatchingMap (terminal.from W).hom 1) ≅
      Arrow.mk (mappingEndpoint W) :=
  terminalRelativeMatchingArrowIso W 1 ≪≫ matchingEndpointArrowIso W

/-- Its forward source is still literally identity. -/
@[simp]
theorem terminalRelativeEndpointArrowIso_hom_left (W : SimplicialSpace.{u}) :
    (terminalRelativeEndpointArrowIso W).hom.left =
      𝟙 (W.diagram.obj (op ⦋1⦌)) := by
  simp [terminalRelativeEndpointArrowIso]

/-- Its inverse source is still literally identity. -/
@[simp]
theorem terminalRelativeEndpointArrowIso_inv_left (W : SimplicialSpace.{u}) :
    (terminalRelativeEndpointArrowIso W).inv.left =
      𝟙 (W.diagram.obj (op ⦋1⦌)) := by
  simp [terminalRelativeEndpointArrowIso]

/-- The forward target is the second relative projection followed by the labelled product swap. -/
theorem terminalRelativeEndpointArrowIso_hom_right (W : SimplicialSpace.{u}) :
    (terminalRelativeEndpointArrowIso W).hom.right =
      (terminalRelativeMatchingObjectIso W 1).hom ≫ matchingOneIso.hom.app W.diagram ≫
        (prod.braiding (W.diagram.obj (op ⦋0⦌)) (W.diagram.obj (op ⦋0⦌))).hom := by
  change (terminalRelativeMatchingObjectIso W 1).hom ≫
      (matchingEndpointArrowIso W).hom.right = _
  rw [matchingEndpointArrowIso_hom_right]

/-- The inverse target retains the inverse swap and original inverse relative comparison. -/
theorem terminalRelativeEndpointArrowIso_inv_right (W : SimplicialSpace.{u}) :
    (terminalRelativeEndpointArrowIso W).inv.right =
      (prod.braiding (W.diagram.obj (op ⦋0⦌)) (W.diagram.obj (op ⦋0⦌))).inv ≫
        matchingOneIso.inv.app W.diagram ≫ (terminalRelativeMatchingObjectIso W 1).inv := by
  change (matchingEndpointArrowIso W).inv.right ≫
      (terminalRelativeMatchingObjectIso W 1).inv = _
  rw [matchingEndpointArrowIso_inv_right, Category.assoc]

attribute [local instance] modelCategory

/-- Actual Reedy fibrancy gives a genuine Kan fibration of every original absolute matching map. -/
theorem matchingMap_fibration (W : SimplicialSpace.{u}) (n : ℕ) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsFibrant W → Fibration (matchingMap W.diagram n) := by
  intro hW
  rw [SSet.modelCategoryQuillen.fibration_iff]
  have hrel := (fibration_iff (terminal.from W)).mp hW n
  exact (SSet.modelCategoryQuillen.J.rlp.arrow_mk_iso_iff
    (terminalRelativeMatchingArrowIso W n)).mp hrel

/-- Actual Reedy fibrancy gives the original source–target endpoint Kan fibration. -/
theorem mappingEndpoint_fibration (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsFibrant W → Fibration (mappingEndpoint W) := by
  intro hW
  rw [SSet.modelCategoryQuillen.fibration_iff]
  exact (SSet.modelCategoryQuillen.J.rlp.arrow_mk_iso_iff
    (matchingEndpointArrowIso W)).mp
      ((SSet.modelCategoryQuillen.fibration_iff _).mp (matchingMap_fibration W 1 hW))

/-- The original chosen mapping-fibre square is the literal pullback of the endpoint and pair
map. -/
theorem mappingFibre_isPullback (W : SimplicialSpace.{u})
    (x y : W.diagram.obj (op ⦋0⦌) _⦋0⦌) :
    IsPullback (mappingFibre.fst W x y) (mappingFibre.snd W x y)
      (mappingEndpoint W) (mappingPointPair W x y) :=
  IsPullback.of_hasPullback _ _

/-- The original second fibre projection is a Kan fibration, with the prescribed vertex pair. -/
theorem mappingFibre_snd_fibration (W : SimplicialSpace.{u})
    (x y : W.diagram.obj (op ⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsFibrant W → Fibration (mappingFibre.snd W x y) := by
  intro hW
  rw [HomotopicalAlgebra.fibration_iff]
  exact (fibrations SSet.{u}).of_isPullback (mappingFibre_isPullback W x y)
    ((HomotopicalAlgebra.fibration_iff _).mp (mappingEndpoint_fibration W hW))

/-- Every original vertex-pair mapping fibre is fibrant in the actual Kan–Quillen model. -/
theorem mappingFibre_isFibrant (W : SimplicialSpace.{u})
    (x y : W.diagram.obj (op ⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsFibrant W → IsFibrant (mappingFibre W x y) := by
  intro hW
  let := mappingFibre_snd_fibration W x y hW
  let : IsFibrant (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 (Δ[0] : SSet.{u}))
      SSet.stdSimplex.isTerminalObj₀).mpr (by infer_instance)
  exact isFibrant_of_fibration (mappingFibre.snd W x y)

/-- Every original vertex-pair mapping fibre is a Kan complex under actual Reedy fibrancy. -/
theorem mappingFibre_kanComplex (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsFibrant W → SSet.KanComplex (mappingFibre W x y) :=
  mappingFibre_isFibrant W x y

end SimplicialSpace.ReedyModel
