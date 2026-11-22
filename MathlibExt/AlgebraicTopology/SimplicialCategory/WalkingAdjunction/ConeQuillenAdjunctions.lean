/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeWeakFunctoriality
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeSliceMate
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenRightMate

/-!
# The two actual cone adjunctions in the named Joyal model

Transport only the actual functors and adjunctions through the
existing designated-carrier and Under equivalences. Both named
model structures are unchanged. The proved original Mono and weak
preservation give the two left Quillen clauses. Their native right
mate is exactly the transported original slice comparison, and
the proved ordinary Ho mate theorem yields its weak equivalence.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeQuillenAdjunctions

attribute [local instance] JoyalSSet.modelCategory

/-- The existing equivalence under the same original point. -/
def pointEquivalence : Under (Δ[0] : SSet.{u}) ≌
    Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) :=
  Under.postEquiv (X := (Δ[0] : SSet.{u})) JoyalSSet.equivalenceSSet.symm

/-- The original fat-cone left functor on the named carrier. -/
def fatLeft : JoyalSSet.{u} ⥤ Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) :=
  JoyalSSet.forget ⋙ (FatCone.underFunctor ⋙ pointEquivalence.functor)

/-- The original path-slice right functor on the named carrier. -/
def fatRight : Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) ⥤ JoyalSSet.{u} :=
  (pointEquivalence.inverse ⋙ FatCone.pathFunctor) ⋙ JoyalSSet.ofSSet

/-- Compose the native fat-cone adjunction with the two original equivalence adjunctions. -/
def fatAdjunction : fatLeft.{u} ⊣ fatRight :=
  JoyalSSet.equivalenceSSet.toAdjunction.comp (FatCone.adjunction.comp pointEquivalence.toAdjunction)

/-- The original point-join left functor on the named carrier. -/
def joinLeft : JoyalSSet.{u} ⥤ Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) :=
  JoyalSSet.forget ⋙ (joinOver (Δ[0] : SSet.{u}) ⋙ pointEquivalence.functor)

/-- The original join-slice right functor on the named carrier. -/
def joinRight : Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) ⥤ JoyalSSet.{u} :=
  (pointEquivalence.inverse ⋙ joinRightDivision (Δ[0] : SSet.{u})) ⋙ JoyalSSet.ofSSet

/-- Compose the native join adjunction with the same original equivalence adjunctions. -/
def joinAdjunction : joinLeft.{u} ⊣ joinRight :=
  JoyalSSet.equivalenceSSet.toAdjunction.comp
    ((joinOverAdjunction (Δ[0] : SSet.{u})).comp pointEquivalence.toAdjunction)

/-- The identical original whole comparison on the two transported left functors. -/
def comparison : fatLeft.{u} ⟶ joinLeft :=
  Functor.whiskerLeft JoyalSSet.forget
    (Functor.whiskerRight FatCone.joinComparison pointEquivalence.functor)

private theorem wrap_isQuillen
    {L : SSet.{u} ⥤ Under (Δ[0] : SSet.{u})} {R : Under (Δ[0] : SSet.{u}) ⥤ SSet.{u}}
    (adj : L ⊣ R)
    (hmono : ∀ {X Y : SSet.{u}} (f : X ⟶ Y), Mono f → Mono (L.map f).right)
    (hweak : ∀ {X Y : SSet.{u}} (f : X ⟶ Y),
      categoricalEquivalences f → categoricalEquivalences (L.map f).right) :
    (JoyalSSet.equivalenceSSet.toAdjunction.comp (adj.comp pointEquivalence.toAdjunction)).IsQuillenAdjunction := by
  let F : JoyalSSet.{u} ⥤ Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) :=
    JoyalSSet.forget ⋙ (L ⋙ pointEquivalence.functor)
  have hcof : PreservesCofibrations F := by
    intro X Y f hf
    have hm : Mono f := by
      change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations f at hf
      rw [JoyalSSet.modelCategory_cofibrations] at hf
      exact hf
    let _ := hm
    have hraw : Mono (L.map (JoyalSSet.forget.map f)).right := hmono _ inferInstance
    let _ := hraw
    change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations
      (JoyalSSet.ofSSet.map (L.map (JoyalSSet.forget.map f)).right)
    rw [JoyalSSet.modelCategory_cofibrations]
    exact inferInstance
  refine ⟨hcof, ?_⟩
  intro X Y f hf
  refine ⟨hcof f hf.1, ?_⟩
  have hraw : categoricalEquivalences (JoyalSSet.forget.map f) := by
    have h := hf.2
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f at h
    rw [JoyalSSet.modelCategory_weakEquivalences] at h
    exact h
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (JoyalSSet.ofSSet.map (L.map (JoyalSSet.forget.map f)).right)
  rw [JoyalSSet.modelCategory_weakEquivalences]
  exact hweak _ hraw

/-- The actual fat-cone adjunction is Quillen from the same named Joyal model. -/
theorem fat_isQuillenAdjunction : fatAdjunction.{u}.IsQuillenAdjunction :=
  wrap_isQuillen FatCone.adjunction
    (fun f hf => by
      let _ := hf
      change Mono (FatCone.map f)
      exact inferInstance)
    (fun f hf => FatCone.map_categoricalEquivalence f hf)

/-- The actual original point-join adjunction is Quillen for those same named models. -/
theorem join_isQuillenAdjunction : joinAdjunction.{u}.IsQuillenAdjunction :=
  wrap_isQuillen (joinOverAdjunction (Δ[0] : SSet.{u}))
    (fun f hf => by
      let _ := hf
      exact mono_join_point f)
    (fun f hf => FatCone.join_map_categoricalEquivalence f hf)

/-- The whole left comparison is weak on every original designated source object. -/
theorem comparison_weak (X : JoyalSSet.{u}) : WeakEquivalence (comparison.app X) := by
  rw [weakEquivalence_iff]
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (JoyalSSet.ofSSet.map (FatCone.toJoin (JoyalSSet.forget.obj X)))
  rw [JoyalSSet.modelCategory_weakEquivalences]
  exact FatCone.toJoin_categoricalEquivalence _

/-- Native conjugation of the transported comparison is transport of the identical original slice mate. -/
theorem conjugate_comparison :
    conjugateEquiv joinAdjunction.{u} fatAdjunction comparison =
      Functor.whiskerRight (Functor.whiskerLeft pointEquivalence.inverse ConeSliceMate.comparison)
        JoyalSSet.ofSSet := by
  have h₁ := conjugateEquiv_whiskerLeft
    ((joinOverAdjunction (Δ[0] : SSet.{u})).comp pointEquivalence.toAdjunction)
    (FatCone.adjunction.comp pointEquivalence.toAdjunction)
    JoyalSSet.equivalenceSSet.toAdjunction
    (Functor.whiskerRight FatCone.joinComparison pointEquivalence.functor)
  have h₂ := conjugateEquiv_whiskerRight (joinOverAdjunction (Δ[0] : SSet.{u}))
    FatCone.adjunction pointEquivalence.toAdjunction FatCone.joinComparison
  exact h₁.trans (congrArg (fun p => Functor.whiskerRight p JoyalSSet.ofSSet) h₂)

private theorem source_cofibrant (X : JoyalSSet.{u}) : IsCofibrant X := by
  rcases X with ⟨K⟩
  apply (isCofibrant_iff_of_isInitial (JoyalSSet.ofSSet.map (initial.to K))
    (initialIsInitial.isInitialObj JoyalSSet.ofSSet (⊥_ SSet.{u}))).mpr
  rw [cofibration_iff]
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations _
  rw [JoyalSSet.modelCategory_cofibrations]
  exact inferInstance

/-- The actual native right mate is weak at every fibrant original structured target. -/
theorem mate_weak (P : Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u}))) [IsFibrant P] :
    WeakEquivalence ((conjugateEquiv joinAdjunction fatAdjunction comparison).app P) := by
  let _ : fatAdjunction.{u}.IsQuillenAdjunction := fat_isQuillenAdjunction
  let _ : joinAdjunction.{u}.IsQuillenAdjunction := join_isQuillenAdjunction
  let _ : IsCofibrant (fatRight.obj P) := source_cofibrant _
  let _ : IsCofibrant (joinRight.obj P) := source_cofibrant _
  let _ : WeakEquivalence (comparison.app (fatRight.obj P)) := comparison_weak _
  let _ : WeakEquivalence (comparison.app (joinRight.obj P)) := comparison_weak _
  exact QuillenRightMate.weakEquivalence_conjugate fatAdjunction joinAdjunction comparison P

end SSet.WalkingAdjunction.ConeQuillenAdjunctions
