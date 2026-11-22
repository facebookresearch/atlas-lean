/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectPullbackIntervalLift

/-!
# Full original interval lifts retain either original point label

Both original unit coefficients are paired in the SAME actual full
pullback. Their genuine component equivalence works in either direction
on the two original labels. In the reversed case, the actual inverse
component representative supplies the original section input. The whole
original lift and both projection maps remain unchanged.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalFixedLabelIntervalLift
open FixedObjects OriginalWalkingArrowFreeSingleHomIso ComponentCategory
open PullbackComponentEquivalence EnrichedHomWeakTransport
attribute [local instance] FixedObjectModel.modelCategory
variable {A D H : FixedObjects walking.{u}} (p : A ⟶ D) (b : H ⟶ D)

/-- The genuine full original interval lift works at both literal original two-label orientations. -/
theorem exists_lift_at_pair [IsCofibrant H] (hp : FixedObjectModel.fibrations walking p)
    (hH : FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal H))
    (x y : walking.{u})
    (hxy : (x = BergnerTwoObject.source (𝟙_ SSet.{u}) ∧ y = BergnerTwoObject.target (𝟙_ SSet.{u})) ∨
      (x = BergnerTwoObject.target (𝟙_ SSet.{u}) ∧ y = BergnerTwoObject.source (𝟙_ SSet.{u})))
    (qA : 𝟙_ SSet.{u} ⟶ hom A x y) (qH : 𝟙_ SSet.{u} ⟶ hom H x y)
    (hq : qA ≫ homMap p x y = qH ≫ homMap b x y)
    (hA : IsIso (arrowOf A.val (SSet.unitHomEquiv _ qA)))
    (hHom : IsIso (arrowOf H.val (SSet.unitHomEquiv _ qH))) :
    ∃ l : H ⟶ A, l ≫ p = b := by
  let P := pullback p b
  let sq := IsPullback.of_hasPullback p b
  let q := pairedUnit sq x y qA qH hq
  have hqP := pairedUnit_isIso sq hp x y qA qH hq hA hHom
  have hforward : ∃ q : 𝟙_ SSet.{u} ⟶ hom P
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})),
      IsIso (arrowOf P.val (SSet.unitHomEquiv _ q)) := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨q, hqP⟩
    · let e := @asIso _ _ _ _ (arrowOf P.val (SSet.unitHomEquiv _ q)) hqP
      exact ⟨inverseUnit e, (congrArg IsIso (inverseUnit_class e)).mpr e.isIso_inv⟩
  obtain ⟨q', hq'⟩ := hforward
  let _ : Fibration p := (fibration_iff p).mpr hp
  have hs : FixedObjectModel.fibrations walking (pullback.snd p b) :=
    (fibration_iff _).mp (inferInstance : Fibration (pullback.snd p b))
  obtain ⟨s, hs⟩ := OriginalFixedLabelIntervalSection.exists_section (pullback.snd p b)
    hs hH (SSet.unitHomEquiv _ q') hq'
  refine ⟨s ≫ pullback.fst p b, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => s ≫ k) (pullback.condition (f := p) (g := b))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ b) hs).trans (Category.id_comp b))))

end CategoryTheory.SimplicialEnrichment.OriginalFixedLabelIntervalLift
