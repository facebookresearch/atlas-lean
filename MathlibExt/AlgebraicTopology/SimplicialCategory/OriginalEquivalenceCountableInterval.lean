/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBoundaryCountableTestUnionWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceLocalizationPointWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeSingleHomCofibrant

/-!
# The SAME original equivalence factors through a genuine countable cofibrant weak interval

The actual original equivalence localization supplies its unchanged full
map from the original free arrow. The genuine countable native cell test
union retains that map and both projections. Its fixed-label initial
cofibrancy, all full Hom countability and all full weak unit Homs are
proved. The SAME original point maps are Dwyer--Kan weak. The original
target-object universe is independent and its two images may coincide.
-/

noncomputable section
universe u v
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceCountableInterval
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
local instance walking_countable : Countable walking.{u} := by
  change Countable (ULift.{u} (SSet.WalkingHom (𝟙_ SSet.{u})))
  exact ⟨⟨fun x => match x.down with
    | .source => 0
    | .target => 1, by
      intro x y h
      rcases x with ⟨x⟩
      rcases y with ⟨y⟩
      cases x <;> cases y <;> simp_all⟩⟩
variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)
variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf C e))

/-- The actual bounded native original support chosen by the proved countable test chain. -/
abbrev support : OriginalBoundaryGoodTree.Supports (OriginalEquivalenceLocalization.fromFree a e he) :=
  OriginalBoundaryCountableTestChain.finalSupport (OriginalEquivalenceLocalization.fromFree a e he)
    (OriginalEquivalenceLocalization.terminal_weak a e he)

/-- The SAME full original countable interval keeps the native lower-colimit on its unchanged original two labels. -/
abbrev fixedObject : FixedObjects walking.{u} :=
  OriginalBoundaryGoodTree.piece (OriginalEquivalenceLocalization.fromFree a e he) (support a e he)

/-- The full varying-object original interval retains every actual original Hom and the same two labels. -/
abbrev object : Carrier.{u} := (fixedObject a e he).val

/-- The unchanged original free arrow maps into the SAME actual native countable piece. -/
abbrev fromFree : free.{u} ⟶ fixedObject a e he :=
  OriginalBoundaryGoodTree.root (OriginalEquivalenceLocalization.fromFree a e he) (support a e he)

/-- The actual native comparison into the SAME original localization pullback. -/
abbrev toLocalization : fixedObject a e he ⟶ OriginalEquivalenceLocalization.fixedObject a e he :=
  OriginalBoundaryGoodTree.toOriginal (OriginalEquivalenceLocalization.fromFree a e he) (support a e he)

/-- Both full actual original factors recover the SAME unchanged original free-arrow localization map. -/
theorem free_toLocalization : fromFree a e he ≫ toLocalization a e he =
    OriginalEquivalenceLocalization.fromFree a e he :=
  OriginalBoundaryGoodTree.root_toOriginal _ _

/-- The SAME actual free-arrow inclusion is genuinely fixed-model cofibrant. -/
theorem fromFree_cofibration : FixedObjectModel.cofibrations walking.{u} (fromFree a e he) :=
  OriginalBoundaryGoodTree.root_cofibration _ _

/-- The SAME actual original interval is genuinely cofibrant from the literal fixed-label initial object. -/
theorem isCofibrant :
    let _ : ModelCategory (FixedObjects walking.{u}) := FixedObjectModel.modelCategory walking
    IsCofibrant (fixedObject a e he) := by
  let _ : ModelCategory (FixedObjects walking.{u}) := FixedObjectModel.modelCategory walking
  let _ : IsCofibrant free.{u} := FreeSingleHom.isCofibrant _ _ _
  let _ : Cofibration (fromFree a e he) := (cofibration_iff _).mpr (fromFree_cofibration a e he)
  exact isCofibrant_of_cofibration (fromFree a e he)

/-- ALL full original Hom simplices in the actual original interval are countable, with no countability premise on C. -/
instance countableHoms : CountableHoms (fixedObject a e he) :=
  OriginalBoundaryGoodTree.piece_countableHoms _ _

/-- The full original terminal map of this SAME actual countable interval is genuinely fixed-model weak. -/
theorem terminal_weak : FixedObjectModel.weakEquivalences walking.{u}
    (CodiscreteTerminal.toTerminal (fixedObject a e he)) :=
  OriginalBoundaryCountableTestUnionWeak.terminal_weak (OriginalEquivalenceLocalization.fromFree a e he)
    (OriginalEquivalenceLocalization.terminal_weak a e he)

/-- Every ordered pair, including both loops and the reverse pair, has its full SAME original Hom weak to the unit. -/
theorem hom_toUnit_weak (x y : walking.{u}) :
    SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit (hom (fixedObject a e he) x y)) := by
  have h := (FixedObjectModel.weakEquivalences_iff _).mp (terminal_weak a e he) x y
  exact (congrArg (fun k : hom (fixedObject a e he) x y ⟶ 𝟙_ SSet.{u} =>
    SSet.realizationWeakEquivalences k) (CodiscreteTerminal.toTerminal_homMap (fixedObject a e he) x y)).mp h

/-- Every SAME full original Hom at individual native vertices is weak to the literal original unit. -/
theorem originalHom_toUnit_weak (x y : object a e he) :
    SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit (x ⟶[SSet.{u}] y)) :=
  (CodiscreteEnrichment.toUnit_weak_iff (originalHomIso (fixedObject a e he) x y).hom
    (SSet.realizationWeakEquivalences.of_isIso _)).mpr
      (hom_toUnit_weak a e he (label (fixedObject a e he) x) (label (fixedObject a e he) y))

/-- Each SAME actual original point selection into the full countable interval is genuinely Dwyer--Kan weak. -/
theorem point_weak (x : walking.{u}) :
    EnrichedDwyerKan.weakEquivalences (BergnerObjects.select (vertex (fixedObject a e he) x)) :=
  OriginalWeakUnitHomsPointRecognition.point_weak (object a e he) (originalHom_toUnit_weak a e he)
    (vertex (fixedObject a e he) x)

/-- ALL actual original degree-zero Hom types are nonempty, including the reverse and both loop types. -/
theorem hom_zero_nonempty (x y : walking.{u}) : Nonempty ((hom (fixedObject a e he) x y) _⦋0⦌) := by
  obtain ⟨z, _hz⟩ := (SSet.realizationWeakEquivalences.bijective_mapπ₀ (hom_toUnit_weak a e he x y)).2
    (SSet.π₀.mk (X := 𝟙_ SSet.{u}) PUnit.unit)
  obtain ⟨v, _hv⟩ := SSet.π₀.mk_surjective z
  exact ⟨v⟩

/-- The whole original interval projection retains the actual unchanged enriched functor and independent target
universe. -/
def toOriginal : EnrichedFunctor SSet.{u} (object a e he) C :=
  EnrichedFunctor.comp SSet.{u} (toLocalization a e he).val (OriginalEquivalenceLocalization.toOriginal a e he)

/-- Both SAME original labels retain exactly their supplied original image under the actual full projection. -/
theorem toOriginal_obj (x : walking.{u}) :
    (toOriginal a e he).obj (vertex (fixedObject a e he) x) = a x := by
  exact (congrArg (OriginalEquivalenceLocalization.toOriginal a e he).obj
    (map_vertex (toLocalization a e he) x)).trans
      (OriginalEquivalenceLocalization.toOriginal_obj a e he x)

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceCountableInterval
