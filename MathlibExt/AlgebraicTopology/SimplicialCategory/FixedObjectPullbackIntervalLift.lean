/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectPullbackComponentEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedLabelIntervalSection

/-!
# The SAME actual paired original coefficients give the full interval lift

The genuine full Hom pullback universal property pairs both unchanged
original unit coefficients with their exact original image equation.
Their original component equivalences prove that actual paired vertex
invertible. The proved native fixed-label section then gives the whole
original interval lift, with every object, Hom and projection retained.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.PullbackComponentEquivalence
open ComponentCategory
variable {O : Type u} {P A B D : FixedObjects O}
variable {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ D} {g : B ⟶ D}

/-- Pair both full original unit coefficients by the genuine actual original Hom pullback universal property. -/
def pairedUnit (sq : IsPullback fst snd f g) (x y : O)
    (qA : 𝟙_ SSet.{u} ⟶ hom A x y) (qB : 𝟙_ SSet.{u} ⟶ hom B x y)
    (hq : qA ≫ homMap f x y = qB ≫ homMap g x y) : 𝟙_ SSet.{u} ⟶ hom P x y :=
  (sq.map (evaluation x y)).lift qA qB hq

/-- The complete SAME original first paired coefficient projects to the entire original first unit map. -/
theorem pairedUnit_fst (sq : IsPullback fst snd f g) (x y : O)
    (qA : 𝟙_ SSet.{u} ⟶ hom A x y) (qB : 𝟙_ SSet.{u} ⟶ hom B x y)
    (hq : qA ≫ homMap f x y = qB ≫ homMap g x y) :
    pairedUnit sq x y qA qB hq ≫ homMap fst x y = qA :=
  (sq.map (evaluation x y)).lift_fst qA qB hq

/-- The complete SAME original second paired coefficient projects to the entire original second unit map. -/
theorem pairedUnit_snd (sq : IsPullback fst snd f g) (x y : O)
    (qA : 𝟙_ SSet.{u} ⟶ hom A x y) (qB : 𝟙_ SSet.{u} ⟶ hom B x y)
    (hq : qA ≫ homMap f x y = qB ≫ homMap g x y) :
    pairedUnit sq x y qA qB hq ≫ homMap snd x y = qB :=
  (sq.map (evaluation x y)).lift_snd qA qB hq

/-- Both original invertible component coefficients give the SAME actual paired original component equivalence. -/
theorem pairedUnit_isIso (sq : IsPullback fst snd f g) (hp : FixedObjectModel.fibrations O f)
    (x y : O) (qA : 𝟙_ SSet.{u} ⟶ hom A x y) (qB : 𝟙_ SSet.{u} ⟶ hom B x y)
    (hq : qA ≫ homMap f x y = qB ≫ homMap g x y)
    (hA : IsIso (arrowOf A.val (SSet.unitHomEquiv _ qA)))
    (hB : IsIso (arrowOf B.val (SSet.unitHomEquiv _ qB))) :
    IsIso (arrowOf P.val (SSet.unitHomEquiv _ (pairedUnit sq x y qA qB hq))) := by
  apply unit_isIso sq hp x y (pairedUnit sq x y qA qB hq)
  · exact (congrArg (fun q => IsIso (arrowOf A.val (SSet.unitHomEquiv _ q)))
      (pairedUnit_fst sq x y qA qB hq)).mpr hA
  · exact (congrArg (fun q => IsIso (arrowOf B.val (SSet.unitHomEquiv _ q)))
      (pairedUnit_snd sq x y qA qB hq)).mpr hB

end CategoryTheory.SimplicialEnrichment.FixedObjects.PullbackComponentEquivalence

namespace CategoryTheory.SimplicialEnrichment.OriginalFixedLabelIntervalLift
open FixedObjects OriginalWalkingArrowFreeSingleHomIso ComponentCategory PullbackComponentEquivalence
attribute [local instance] FixedObjectModel.modelCategory
variable {A D H : FixedObjects walking.{u}} (p : A ⟶ D) (b : H ⟶ D)

/-- Actual paired original unit coefficients and the SAME native section construct a full original interval lift. -/
theorem exists_lift [IsCofibrant H] (hp : FixedObjectModel.fibrations walking p)
    (hH : FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal H))
    (qA : 𝟙_ SSet.{u} ⟶ hom A (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})))
    (qH : 𝟙_ SSet.{u} ⟶ hom H (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})))
    (hq : qA ≫ homMap p (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) =
        qH ≫ homMap b (BergnerTwoObject.source (𝟙_ SSet.{u}))
          (BergnerTwoObject.target (𝟙_ SSet.{u})))
    (hA : IsIso (arrowOf A.val (SSet.unitHomEquiv _ qA)))
    (hHom : IsIso (arrowOf H.val (SSet.unitHomEquiv _ qH))) :
    ∃ l : H ⟶ A, l ≫ p = b := by
  let P := pullback p b
  let sq := IsPullback.of_hasPullback p b
  let q := pairedUnit sq (BergnerTwoObject.source (𝟙_ SSet.{u}))
    (BergnerTwoObject.target (𝟙_ SSet.{u})) qA qH hq
  have hqP := pairedUnit_isIso sq hp (BergnerTwoObject.source (𝟙_ SSet.{u}))
    (BergnerTwoObject.target (𝟙_ SSet.{u})) qA qH hq hA hHom
  let _ : Fibration p := (fibration_iff p).mpr hp
  have hs : FixedObjectModel.fibrations walking (pullback.snd p b) :=
    (fibration_iff _).mp (inferInstance : Fibration (pullback.snd p b))
  obtain ⟨s, hs⟩ := OriginalFixedLabelIntervalSection.exists_section (pullback.snd p b)
    hs hH (SSet.unitHomEquiv _ q) hqP
  refine ⟨s ≫ pullback.fst p b, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => s ≫ k) (pullback.condition (f := p) (g := b))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ b) hs).trans (Category.id_comp b))))

end CategoryTheory.SimplicialEnrichment.OriginalFixedLabelIntervalLift
