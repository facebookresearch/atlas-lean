/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerLocalClasses
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedObjectGlobalLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment

/-!
# Genuine original C0 cofibrations are injective on actual original objects

The original C0 lifting class lifts against the genuine codiscrete
object projection, whose full Hom maps are scalar identities. The
actual lift is a left inverse of the SAME original object function.
No global model or object-monicity certificate is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner

/-- The SAME original object function of a genuine global C0 cofibration is injective. -/
theorem cofibration_objects_injective {C D : Carrier.{u}} (i : C ⟶ D) (hi : cofibrations i) :
    Function.Injective i.obj := by
  intro a b hab
  let R : CodiscreteEnrichment.object (C : Type u) ⟶ CodiscreteEnrichment.object PUnit.{u+1} :=
    CodiscreteEnrichment.map (↾fun _ : C => PUnit.unit)
  have hr : generatingCofibrations.rlp R := by
    apply (generatingCofibrations_rlp_original_iff R).mpr
    constructor
    · intro y
      refine ⟨a, ?_⟩
      change (PUnit.unit : PUnit.{u+1}) = y
      exact Subsingleton.elim _ _
    · intro x y
      change Fibration (𝟙 (𝟙_ SSet.{u})) ∧ SSet.realizationWeakEquivalences (𝟙 (𝟙_ SSet.{u}))
      exact ⟨inferInstance, SSet.realizationWeakEquivalences.id_mem _⟩
  let top := CodiscreteEnrichment.adjunction.unit.app C
  let bottom := CodiscreteEnrichment.extend D PUnit.{u+1} (↾fun _ => PUnit.unit)
  let _ : HasLiftingProperty i R := hi R hr
  have sq : CommSq top i R bottom := ⟨by
    apply (CodiscreteEnrichment.homEquiv C PUnit.{u+1}).injective
    apply ConcreteCategory.hom_ext
    intro x
    rfl⟩
  let _ : sq.HasLift := (hi R hr).sq_hasLift sq
  let L := sq.lift
  have hl : i ≫ L = top := sq.fac_left
  have ha := congrArg (fun F : C ⟶ CodiscreteEnrichment.object (C : Type u) => F.obj a) hl
  have hb := congrArg (fun F : C ⟶ CodiscreteEnrichment.object (C : Type u) => F.obj b) hl
  change L.obj (i.obj a) = a at ha
  change L.obj (i.obj b) = b at hb
  exact ha.symm.trans ((congrArg L.obj hab).trans hb)

/-- Forgetting enrichment retains the SAME genuine monic original object map. -/
theorem cofibration_forgetObjects_mono {C D : Carrier.{u}} (i : C ⟶ D) (hi : cofibrations i) :
    Mono (forgetObjects.map i) :=
  (mono_iff_injective _).mpr (cofibration_objects_injective i hi)

end CategoryTheory.SimplicialEnrichment.Bergner
