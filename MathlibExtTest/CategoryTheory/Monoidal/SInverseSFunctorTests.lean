/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSFunctor

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
public meta import Lean.PrivateName

/-!
# Ordinary use of additive stabilized-pair transport

The client keeps arbitrary raw arrows, the normalized equivalence unit,
the genuine negative Core map and every categorical component. All displayed
comparisons use the public transport and the original source maps.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SInverseS
open Algebra
open scoped ZeroObject

universe uC vC uD vD uK vK

namespace MathlibExtTest.CategoryTheory.Monoidal.SInverseSFunctorTests

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable {K : Type uK} [Category.{vK} K] [Preadditive K]
  [HasZeroObject K] [HasBinaryBiproducts K]

/-- The ordinary API retains raw maps, both Core signs and every transported component. -/
theorem additivePairTransportClient
    (F G : C ⥤ D) [F.Additive] [G.Additive] (α : F ≅ G)
    (H : D ⥤ K) [H.Additive] (E : C ≌ D) [E.functor.Additive]
    (X Y Z : Pair C) (f : RawHom X Y) (g : RawHom Y Z)
    (U : Core C) (A : C) (a : ConnectedComponents (Pair C))
    (k : GrothendieckAddGroup (Skeleton C)) (l : GrothendieckAddGroup (Skeleton D)) :
    letI (B B' : C) : PreservesBinaryBiproduct B B' F :=
      preservesBinaryBiproduct_of_preservesBiproduct F B B'
    let P := pairEquivalence E
    let PF := pairFunctor F
    let kF := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := F))
    let kE := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.functor))
    let kEi := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.inverse))
    let I := fun {B₁ B₂ B₁' B₂' : D} (e₁ : B₁ ≅ B₁') (e₂ : B₂ ≅ B₂') =>
      (corePairInclusion (C := D)).mapIso
        ((Core.isoMk (x := ⟨B₁⟩) (y := ⟨B₁'⟩) e₁).prod
          (Core.isoMk (x := ⟨B₂⟩) (y := ⟨B₂'⟩) e₂))
    let η₀ := (pairFunctorIdentity (C := C)).symm ≪≫
      pairFunctorNatIso (𝟭 C) (E.functor ⋙ E.inverse) E.unitIso ≪≫
        pairFunctorComposite E.functor E.inverse
    let ε₀ := (pairFunctorComposite E.inverse E.functor).symm ≪≫
      pairFunctorNatIso (E.inverse ⋙ E.functor) (𝟭 D) E.counitIso ≪≫
        pairFunctorIdentity (C := D)
    (pairFunctor F).obj X = ⟨F.obj X.fst, F.obj X.snd⟩ ∧
    (pairFunctor F).map (Hom.mk f) = Hom.mk (mapRawHom F f) ∧
    (mapRawHom F f).stabilizer = F.obj f.stabilizer ∧
    (mapRawHom F f).hom₁ =
      (F.mapBiprod f.stabilizer X.fst).symm ≪≫ F.mapIso f.hom₁ ∧
    (mapRawHom F f).hom₂ =
      (F.mapBiprod f.stabilizer X.snd).symm ≪≫ F.mapIso f.hom₂ ∧
    (mapRawHom F (f.comp g)).Rel ((mapRawHom F f).comp (mapRawHom F g)) ∧
    (pairFunctorNatIso F G α).app X = I (α.app X.fst) (α.app X.snd) ∧
    (pairFunctorIdentity (C := C)).app X = Iso.refl X ∧
    (pairFunctorComposite F H).app X = Iso.refl ((pairFunctor (F ⋙ H)).obj X) ∧
    P.functor = pairFunctor E.functor ∧
    P.inverse = pairFunctor E.inverse ∧
    P.unitIso = Equivalence.adjointifyη η₀ ε₀ ∧
    P.counitIso = ε₀ ∧
    (positiveCoreIso F).app U =
      I (Iso.refl (F.obj U.of)) F.mapZeroObject ∧
    (negativeCoreIso F).app U =
      I F.mapZeroObject (Iso.refl (F.obj U.of)) ∧
    swapFunctor (C := C) ⋙ pairFunctor F =
      pairFunctor F ⋙ swapFunctor (C := D) ∧
    (translateFirstIso F A).app Y =
      I (F.mapBiprod A Y.fst) (Iso.refl (F.obj Y.snd)) ∧
    (translateSecondIso F A).app Y =
      I (Iso.refl (F.obj Y.fst)) (F.mapBiprod A Y.snd) ∧
    (zeroPairIso F).hom = Hom.mk
      { stabilizer := (0 : D)
        hom₁ := (isoZeroBiprod (isZero_zero D)).symm ≪≫ F.mapZeroObject
        hom₂ := (isoZeroBiprod (isZero_zero D)).symm ≪≫ F.mapZeroObject } ∧
    (toZeroIso F X).app Y =
      (translateFirstIso F X.snd).app ((translateSecondFunctor X.fst).obj Y) ≪≫
        (translateFirstFunctor (F.obj X.snd)).mapIso
          ((translateSecondIso F X.fst).app Y) ∧
    PF.map (diagonalAddHom A X) ≫
        (I (F.mapBiprod A X.fst) (F.mapBiprod A X.snd)).hom =
      diagonalAddHom (F.obj A) (PF.obj X) ∧
    kF X.difference = (PF.obj X).difference ∧
    connectedComponentsToGrothendieck (PF.mapConnectedComponents a) =
      kF (connectedComponentsToGrothendieck a) ∧
    connectedComponentsToGrothendieck (PF.mapConnectedComponents
        (ConnectedComponents.mk ((negativeCoreInclusion (C := C)).obj U))) =
      -GrothendieckAddGroup.of (toSkeleton (F.obj U.of)) ∧
    connectedComponentsToGrothendieck ((swapFunctor (C := D)).mapConnectedComponents
        (PF.mapConnectedComponents a)) =
      -kF (connectedComponentsToGrothendieck a) ∧
    connectedComponentsToGrothendieck
        ((translateFirstFunctor (F.obj A)).mapConnectedComponents
          (PF.mapConnectedComponents a)) =
      GrothendieckAddGroup.of (toSkeleton (F.obj A)) +
        kF (connectedComponentsToGrothendieck a) ∧
    connectedComponentsToGrothendieck
        ((translateSecondFunctor (F.obj A)).mapConnectedComponents
          (PF.mapConnectedComponents a)) =
      kF (connectedComponentsToGrothendieck a) -
        GrothendieckAddGroup.of (toSkeleton (F.obj A)) ∧
    connectedComponentsToGrothendieck
        ((translateToZeroFunctor (PF.obj X)).mapConnectedComponents
          (PF.mapConnectedComponents a)) =
      kF (connectedComponentsToGrothendieck a - X.difference) ∧
    (translateToZeroFunctor (PF.obj X)).mapConnectedComponents
        (PF.mapConnectedComponents a) =
      PF.mapConnectedComponents ((translateToZeroFunctor X).mapConnectedComponents a) ∧
    connectedComponentsToGrothendieck
        ((translateToZeroFunctor (PF.obj X)).mapConnectedComponents
          (PF.mapConnectedComponents (ConnectedComponents.mk X))) = 0 ∧
    (Skeleton.mapAddMonoidHom (F := E.inverse)).comp
        (Skeleton.mapAddMonoidHom (F := E.functor)) = AddMonoidHom.id (Skeleton C) ∧
    (Skeleton.mapAddMonoidHom (F := E.functor)).comp
        (Skeleton.mapAddMonoidHom (F := E.inverse)) = AddMonoidHom.id (Skeleton D) ∧
    kEi.comp kE = AddMonoidHom.id (GrothendieckAddGroup (Skeleton C)) ∧
    kE.comp kEi = AddMonoidHom.id (GrothendieckAddGroup (Skeleton D)) ∧
    grothEquiv E k = kE k ∧
    (grothEquiv E).symm l = kEi l := by
  dsimp only
  have functorLaws := pairFunctor_characteristic F G α H
  have equivalenceLaws := pairEquivalence_characteristic E
  have coreLaws := coreTranslation_characteristic F
  have componentLaws := components_characteristic F
  have inverseLaws := grothEquivalence_characteristic E
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact functorLaws.1 X
  · exact functorLaws.2.1 f
  · exact functorLaws.2.2.1 f
  · exact functorLaws.2.2.2.1 f
  · exact functorLaws.2.2.2.2.1 f
  · exact functorLaws.2.2.2.2.2.2.2.1 f g
  · exact functorLaws.2.2.2.2.2.2.2.2.1 X
  · exact functorLaws.2.2.2.2.2.2.2.2.2.1 X
  · exact functorLaws.2.2.2.2.2.2.2.2.2.2.1 X
  · exact equivalenceLaws.1
  · exact equivalenceLaws.2.1
  · exact equivalenceLaws.2.2.1
  · exact equivalenceLaws.2.2.2.1
  · exact coreLaws.2.2.1 U
  · exact coreLaws.2.2.2.1 U
  · exact coreLaws.2.2.2.2.1
  · exact coreLaws.2.2.2.2.2.2.1 A Y
  · exact coreLaws.2.2.2.2.2.2.2.1 A Y
  · exact coreLaws.2.2.2.2.2.2.2.2.2.1
  · exact coreLaws.2.2.2.2.2.2.2.2.2.2.1 X Y
  · exact coreLaws.2.2.2.2.2.2.2.2.2.2.2.2 A X
  · exact componentLaws.1 X
  · exact componentLaws.2.1 a
  · exact componentLaws.2.2.2.1 U
  · exact componentLaws.2.2.2.2.1 a
  · exact componentLaws.2.2.2.2.2.1 A a
  · exact componentLaws.2.2.2.2.2.2.1 A a
  · exact componentLaws.2.2.2.2.2.2.2.1 X a
  · exact componentLaws.2.2.2.2.2.2.2.2.1 X a
  · exact componentLaws.2.2.2.2.2.2.2.2.2 X
  · exact inverseLaws.1
  · exact inverseLaws.2.1
  · exact inverseLaws.2.2.1
  · exact inverseLaws.2.2.2
  · exact grothEquiv_apply E k
  · exact grothEquiv_symm_apply E l


-- The public signatures remain independent of private implementation declarations.
run_cmd do
  let required : Array Lean.Name := #[
    `CategoryTheory.SInverseS.mapRawHom,
    `CategoryTheory.SInverseS.pairFunctor,
    `CategoryTheory.SInverseS.pairFunctorNatIso,
    `CategoryTheory.SInverseS.pairFunctorIdentity,
    `CategoryTheory.SInverseS.pairFunctorComposite,
    `CategoryTheory.SInverseS.pairEquivalence,
    `CategoryTheory.SInverseS.corePairIso,
    `CategoryTheory.SInverseS.positiveCoreIso,
    `CategoryTheory.SInverseS.negativeCoreIso,
    `CategoryTheory.SInverseS.translateFirstIso,
    `CategoryTheory.SInverseS.translateSecondIso,
    `CategoryTheory.SInverseS.zeroPairIso,
    `CategoryTheory.SInverseS.toZeroIso,
    `CategoryTheory.SInverseS.differenceIso,
    `CategoryTheory.SInverseS.grothEquiv,
    `CategoryTheory.SInverseS.grothEquiv_apply,
    `CategoryTheory.SInverseS.grothEquiv_symm_apply,
    `CategoryTheory.SInverseS.pairFunctor_characteristic,
    `CategoryTheory.SInverseS.pairEquivalence_characteristic,
    `CategoryTheory.SInverseS.coreTranslation_characteristic,
    `CategoryTheory.SInverseS.components_characteristic,
    `CategoryTheory.SInverseS.grothEquivalence_characteristic,
    `MathlibExtTest.CategoryTheory.Monoidal.SInverseSFunctorTests.additivePairTransportClient]
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for name in required do
    let some info := env.find? name | throwError "Required declaration missing: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial required declaration: {name}"
    info.type.getUsedConstants.forM fun used => do
      if Lean.isPrivateName used then
        throwError "Private TYPE dependency in {name}: {used}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
  Lean.logInfo m!"PAIR_PUBLIC_GUARD_OK named={required.size}; TYPE-private=0; safe; standard-AX"

end MathlibExtTest.CategoryTheory.Monoidal.SInverseSFunctorTests
