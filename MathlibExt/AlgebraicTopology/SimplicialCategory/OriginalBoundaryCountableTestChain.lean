/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBoundaryCountableTestEnlargement
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.UnderColimits
import Mathlib.Order.Monotone.Basic

/-!
# The SAME original countable test chain and full original union cocone

Start from the actual empty original cell support and repeatedly take
the proved original countable common lift support. Its actual countable
union retains all original cells and source maps. The literal lower
colimit cocone and its SAME original horn replacement have their full
universal properties. No weak-union conclusion is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryCountableTestChain
open OriginalBoundaryGoodTree OriginalBoundarySupportDiagram OriginalBoundaryCountableTestEnlargement
variable {O : Type u} [Countable O] {C D : FixedObjects O} [CountableHoms C] (f : C ⟶ D)
variable (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))

/-- The SAME actual original support sequence begins at the empty original support. -/
def stages : ℕ → Supports f
  | 0 => by
    let _ : PartialOrder (Cells f) := (data f).order
    exact BoundedLowerSupport.empty rank
  | n + 1 => step f hD (stages n)

/-- Every actual next stage is literally the proved original common lift support. -/
theorem stages_succ (n : ℕ) : stages f hD (n + 1) = step f hD (stages f hD n) := rfl

/-- The actual original stage function preserves every original support inclusion. -/
theorem stages_monotone : Monotone (stages f hD) :=
  monotone_nat_of_le_succ (fun n => le_step f hD (stages f hD n))

/-- The SAME actual countable union of original stage supports. -/
def finalSupport : Supports f := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact BoundedLowerSupport.countableUnion rank Cardinal.aleph0_lt_aleph_one (stages f hD)

/-- Each original stage retains all its original cells in the SAME actual final support. -/
theorem stage_le_final (n : ℕ) : stages f hD n ≤ finalSupport f hD := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact BoundedLowerSupport.le_indexedUnion rank (stages f hD)
    (GoodOrderBounds.natLt rank Cardinal.aleph0_lt_aleph_one) n

/-- The SAME original stage support diagram uses the literal original lower-set maps. -/
def supportDiagram :
    let _ : PartialOrder (Cells f) := (data f).order
    ℕ ⥤ LowerSet (Cells f) := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact (stages_monotone f hD).functor ⋙ BoundedLowerSupport.toLower rank

/-- Every actual original stage remains its literal recorded lower-colimit object under the original source. -/
def underDiagram : ℕ ⥤ Under C := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact supportDiagram f hD ⋙ (data f).lowerData.functor

/-- The actual full original union cocone under its unchanged original source. -/
def underCocone : Cocone (underDiagram f hD) := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact (data f).lowerData.filteredCocone (supportDiagram f hD)

/-- The original union cocone has its genuine full universal property. -/
def underIsColimit : IsColimit (underCocone f hD) := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact (data f).lowerData.isColimitFilteredCocone (B := supportDiagram f hD)

/-- The SAME whole original stage diagram in the full original fixed-label category. -/
abbrev diagram : ℕ ⥤ FixedObjects O := underDiagram f hD ⋙ Under.forget C

/-- Every full original stage object is literally the SAME original countable piece. -/
theorem diagram_obj (n : ℕ) : (diagram f hD).obj n = piece f (stages f hD n) := rfl

/-- The complete actual original cocone to the SAME original countable union piece. -/
def cocone : Cocone (diagram f hD) := (Under.forget C).mapCocone (underCocone f hD)

/-- The entire original union point is precisely the SAME actual selected original final piece. -/
theorem cocone_point : (cocone f hD).pt = piece f (finalSupport f hD) := rfl

/-- The SAME literal full countable union piece is the original stage colimit. -/
def isColimit : IsColimit (cocone f hD) :=
  isColimitOfPreserves (Under.forget C) (underIsColimit f hD)

/-- The actual original replaced stage diagram uses the SAME full horn functor. -/
abbrev replacedDiagram : ℕ ⥤ FixedObjects O := diagram f hD ⋙ OriginalFibrantReplacement.functor O

/-- The original replaced union cocone retains all SAME native horn functor maps. -/
def replacedCocone : Cocone (replacedDiagram f hD) :=
  (OriginalFibrantReplacement.functor O).mapCocone (cocone f hD)

/-- The SAME original native horn replacement preserves this actual countable union colimit. -/
def replacedIsColimit : IsColimit (replacedCocone f hD) := by
  let _ : Fact Cardinal.aleph0.{u}.IsRegular := Cardinal.fact_isRegular_aleph0
  let _ : IsCardinalFiltered ℕ Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff ℕ).mpr inferInstance
  let _ : PreservesColimitsOfShape ℕ (OriginalFibrantReplacement.functor O) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
      (OriginalFibrantReplacement.functor O) Cardinal.aleph0.{u} ℕ
  exact isColimitOfPreserves (OriginalFibrantReplacement.functor O) (isColimit f hD)

/-- Each SAME original next-stage map is the literal support map carrying all derived original boundary lifts. -/
theorem replacedDiagram_succ (n : ℕ) :
    (replacedDiagram f hD).map (homOfLE (Nat.le_succ n)) =
      (OriginalBoundarySupportDiagram.replacedDiagram f).map
        (homOfLE (le_step f hD (stages f hD n))) := rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryCountableTestChain
