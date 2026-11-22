/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceCountableIntervalDirectReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitCoefficientReadback

/-!
# Actual same-label weak intervals factor original fixed-category equivalences

The full original arbitrary-equivalence constructor applied at the SAME
actual fixed-category vertices retains both labels. Original carrier
readback gives its complete fixed-label map into the unchanged target.
Its genuine countable fixed-cofibrant weak interval is constructed from
the supplied original component equivalence, with no weak target input.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalFixedLabelIntervalFactor
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable (P : FixedObjects walking.{u})
variable (e : (hom P (BergnerTwoObject.source (𝟙_ SSet.{u}))
  (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf P.val e))

/-- The actual full original weak interval at the SAME original fixed-label vertices. -/
abbrev object : FixedObjects walking.{u} := OriginalEquivalenceCountableInterval.fixedObject (vertex P) e he

/-- The genuine original projection is retained through the exact native original label readback. -/
def map : object P e he ⟶ P := by
  let F := OriginalEquivalenceCountableInterval.toOriginal (vertex P) e he
  have h : ∀ x, F.obj (vertex (object P e he) x) = vertex P x :=
    OriginalEquivalenceCountableInterval.toOriginal_obj (vertex P) e he
  have hF := CarrierLabelReadback.map (object P e he) (vertex P) F h
  let Q := CarrierReindexing.object P.val (vertex P)
  let toP : Q ⟶ P :=
    ⟨CarrierReindexing.toTarget P.val (vertex P), by
      apply IsHomLift.of_fac' forgetObjects (𝟙 (walking.{u} : Type u))
        (CarrierReindexing.toTarget P.val (vertex P)) Q.property P.property
      ext x
      rfl⟩
  exact hF ≫ toP

/-- The constructed SAME original weak interval map is genuinely weak whenever the actual original target is weak to its
literal unit. -/
theorem map_weak (hP : FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal P)) :
    FixedObjectModel.weakEquivalences walking (map P e he) := by
  have hK := OriginalEquivalenceCountableInterval.terminal_weak (vertex P) e he
  have hfac : map P e he ≫ CodiscreteTerminal.toTerminal P =
      CodiscreteTerminal.toTerminal (object P e he) := CodiscreteTerminal.toTerminal_naturality _
  exact (FixedObjectModel.weakEquivalences walking).of_postcomp _ _ hP
    ((congrArg (fun f => FixedObjectModel.weakEquivalences walking f) hfac).mpr hK)

/-- The SAME actual constructed fixed interval is genuinely cofibrant, independently of its original target. -/
theorem isCofibrant :
    let _ : ModelCategory (FixedObjects walking.{u}) := FixedObjectModel.modelCategory walking
    IsCofibrant (object P e he) := OriginalEquivalenceCountableInterval.isCofibrant (vertex P) e he

end CategoryTheory.SimplicialEnrichment.OriginalFixedLabelIntervalFactor
