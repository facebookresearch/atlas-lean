/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCarrierDisjointCoproduct
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedInitialObjects
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexingEquivalence
import Mathlib.Logic.Equiv.Set

/-!
# The original injected enriched family and its genuine isolated complement

The SAME whole original enrichment is summed with the actual initial
enrichment on the unused labels. The canonical range/complement
equivalence reindexes that genuine carrier coproduct onto exactly the
supplied target labels, including empty source and complement families.
Every full original Hom and both entire comparison maps are retained.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.InjectiveLabelFamilies
open FixedObjects

variable {A O : Type u} (a : A → O) (ha : Function.Injective a)

/-- The SAME unused original labels, with no chosen source basepoint. -/
abbrev complement : Type u := {o : O // o ∉ Set.range a}

/-- The actual original fixed-label initial enrichment on those unused labels. -/
abbrev isolated : FixedObjects (complement a) := BergnerFixedInitialObjects.fixedObject (complement a)

variable (C : FixedObjects A)

/-- The genuine carrier coproduct of the SAME full source and the actual isolated complement. -/
abbrev family : Carrier.{u} := DisjointCoproduct.object C.val (isolated a).val

/-- The actual complete original object family is equivalent to exactly the supplied target labels. -/
def familyEquiv : family a C ≃ O := by
  classical
  exact (Equiv.sumCongr (verticesEquiv C).symm (verticesEquiv (isolated a)).symm).trans
    ((Equiv.sumCongr (Equiv.ofInjective a ha) (Equiv.refl (complement a))).trans
      (Equiv.Set.sumCompl (Set.range a)))

/-- Every original source vertex has its SAME injected label. -/
theorem familyEquiv_inl (s : A) :
    familyEquiv a ha C (Sum.inl (vertex C s)) = a s := by
  change a (label C (vertex C s)) = a s
  exact congrArg a (label_vertex C s)

/-- Every actual isolated vertex has its SAME unused original label. -/
theorem familyEquiv_inr (o : complement a) :
    familyEquiv a ha C (Sum.inr (vertex (isolated a) o)) = o.val := by
  change (label (isolated a) (vertex (isolated a) o)).val = o.val
  exact congrArg Subtype.val (label_vertex (isolated a) o)

/-- The SAME literal full original family reindexed onto the exact target labels. -/
def object : FixedObjects O := CarrierReindexing.object (family a C) (familyEquiv a ha C).symm

/-- Both complete original family maps form the genuine carrier isomorphism. -/
def familyIso : (object a ha C).val ≅ family a C :=
  CarrierReindexing.equivalenceIso (family a C) (familyEquiv a ha C).symm

/-- The SAME whole original source inclusion with every original coefficient preserved. -/
def inclusion : C.val ⟶ (object a ha C).val :=
  DisjointCoproduct.inl C.val (isolated a).val ≫ (familyIso a ha C).inv

/-- The actual source inclusion retains precisely every original injected vertex. -/
theorem inclusion_vertex (s : A) :
    (inclusion a ha C).obj (vertex C s) = vertex (object a ha C) (a s) :=
  familyEquiv_inl a ha C s

/-- Projection reads back the SAME complete original source family inclusion. -/
theorem inclusion_familyIso : inclusion a ha C ≫ (familyIso a ha C).hom =
    DisjointCoproduct.inl C.val (isolated a).val := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => DisjointCoproduct.inl C.val (isolated a).val ≫ k)
      (familyIso a ha C).inv_hom_id).trans (Category.comp_id _))

end CategoryTheory.SimplicialEnrichment.InjectiveLabelFamilies
