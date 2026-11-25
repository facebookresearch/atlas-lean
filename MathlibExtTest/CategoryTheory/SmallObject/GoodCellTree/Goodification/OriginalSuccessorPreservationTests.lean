/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalSuccessorPreservation
import Lean.Util.CollectAxioms

/-!
# Public original-prefix successor clients

Exercise the actual one-cell successor producer, complete old-field preservation,
the old-only BEFORE and newborn AFTER lower-colimit boundaries, and the newborn
predecessor, attaching and cell-target squares. The root and total carrier are
arbitrary; compactness is required only for the newborn cell ends. These clients
promote the verified public lower-colimit and preservation examples.
-/

set_option autoImplicit false

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace OriginalSuccessorPreservationPublicClient

noncomputable section

open CategoryTheory.SmallObject.OriginalGoodification OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [Category.{v} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

-- The original BEFORE data and newborn compact cell ends produce the full AFTER prefix.
example : Prefix O M chi (after gamma) := successorPrefix O M chi gamma r N

-- The public witness contains all nine original preservation fields.
example : Preserves O M chi (before_le_after gamma) r
    (successorPrefix O M chi gamma r N) := successorPrefix_preserves O M chi gamma r N

-- BEFORE excludes the newborn, whereas AFTER includes that same original label.
example : labels.symm gamma ∉ before gamma := by
  change ¬labels (labels.symm gamma) < gamma
  simp

example : labels.symm gamma ∈ after gamma := by
  change labels (labels.symm gamma) ≤ gamma
  simp

-- Old-only boundary: the actual original BEFORE cocone is colimiting in the successor.
example :
    letI := successorOrder O M chi gamma r N
    letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
    IsColimit (OriginalLowerComparisonCocone.cocone
      (successorLabelHom O M chi gamma r N) (successorTree O M chi gamma r N).diagram
      O.diagram (successorComparison O M chi gamma r N) M (before gamma)) :=
  successorLowerIsColimit O M chi gamma r N (before gamma) (before_le_after gamma)

-- Newborn boundary: the actual original AFTER cocone includes the new cell and is colimiting.
example :
    letI := successorOrder O M chi gamma r N
    letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
    IsColimit (OriginalLowerComparisonCocone.cocone
      (successorLabelHom O M chi gamma r N) (successorTree O M chi gamma r N).diagram
      O.diagram (successorComparison O M chi gamma r N) M (after gamma)) :=
  successorLowerIsColimit O M chi gamma r N (after gamma) le_rfl

-- Every original lower subset also exposes its UP through the bundled public prefix.
example (D : LowerSet P) (hD : D ≤ after gamma) :
    let d := successorPrefix O M chi gamma r N
    letI := d.ord
    letI : Preorder (after gamma) := d.ord.toPreorder
    IsColimit (OriginalLowerComparisonCocone.cocone
      (prefixLabels (after gamma) d.ord d.below) d.tree.diagram O.diagram d.comparison M D) :=
  (successorPrefix O M chi gamma r N).lowerUP D hD

-- The literal successor tree has its derived good bound and original cell labels.
example :
    let d := successorPrefix O M chi gamma r N
    letI := d.ord
    d.tree.IsGood chi := (successorPrefix O M chi gamma r N).good

example (a : after gamma) :
    (letI := (successorPrefix O M chi gamma r N).ord
     (successorPrefix O M chi gamma r N).tree.label a) = O.label a.1 :=
  (successorPrefix O M chi gamma r N).labels a

-- The newborn predecessor square retains the actual original vertex comparison.
example :
    let d := successorPrefix O M chi gamma r N
    letI := d.ord
    letI : Preorder (after gamma) := d.ord.toPreorder
    let a : after gamma := ⟨labels.symm gamma,
      by change labels (labels.symm gamma) ≤ gamma; simp⟩
    prefixPredecessorComparison O M chi d a ≫ O.predecessorMap a.1 =
      d.tree.predecessorMap a ≫ d.comparison.app a := by
  let d := successorPrefix O M chi gamma r N
  let _ := d.ord
  let _ : Preorder (after gamma) := d.ord.toPreorder
  let a : after gamma := ⟨labels.symm gamma,
    by change labels (labels.symm gamma) ≤ gamma; simp⟩
  exact prefixPredecessorComparison_square O M chi d a

-- The original attaching map is retained at the actual newborn predecessor point.
example :
    let d := successorPrefix O M chi gamma r N
    let a : after gamma := ⟨labels.symm gamma,
      by change labels (labels.symm gamma) ≤ gamma; simp⟩
    (letI := d.ord
     d.tree.attaching a ≫ (prefixPredecessorComparison O M chi d a).right) ≍
      O.attaching (labels.symm gamma) := successorPrefix_new_attaching O M chi gamma r N

-- The actual newborn cell-target map survives the whole original vertex comparison.
example :
    let d := successorPrefix O M chi gamma r N
    letI := d.ord
    letI : Preorder (after gamma) := d.ord.toPreorder
    let a : after gamma := ⟨labels.symm gamma,
      by change labels (labels.symm gamma) ≤ gamma; simp⟩
    d.tree.cell a ≫ (d.comparison.app a).right ≍ O.cell (labels.symm gamma) :=
  successorPrefix_new_cell_full O M chi gamma r N

end

end OriginalSuccessorPreservationPublicClient

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let declarations := #[
    ``CategoryTheory.SmallObject.OriginalGoodification.successorPrefix,
    ``CategoryTheory.SmallObject.OriginalGoodification.successorPrefix_preserves]
  let modules ← declarations.mapM fun name => do
    let some idx := env.getModuleIdxFor? name
      | throwError "The original successor API is not imported: {name}"
    pure idx
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains idx then names.push name else names
    | none => names
  for name in names do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun ax =>
      ax != ``propext && ax != ``Quot.sound && ax != ``Classical.choice
    unless forbidden.isEmpty do
      throwError "Nonstandard axioms in {name}: {forbidden}"
  logInfo m!"Original successor clients: {names.size} actual declarations, standard axioms"
