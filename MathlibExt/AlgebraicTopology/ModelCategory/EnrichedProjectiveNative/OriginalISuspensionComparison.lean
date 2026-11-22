/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPushout
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppe

/-!
# Cone suspensions and homotopy pushouts

The native cofibration cone defines a suspension functor by pushout and a natural comparison
with the homotopy pushout of the zero span. The comparison to the zero-span homotopy pushout
is weak for every object, while the comparison to the cone suspension is weak for cofibrant
objects. After the given cofibrant replacement, these comparisons yield a natural
isomorphism on the homotopy category, retaining its maps in both directions.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OriginalISuspension

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I

attribute [local instance] Native.modelCategory

private instance nativeFactorization :
    CategoryTheory.MorphismProperty.HasFunctorialFactorization
      (cofibrations (D (I := I))) (trivialFibrations (D (I := I))) :=
  (Native.functorialFactorizations (B := B) (A := I)).1

/-- The chosen pushout cocone for the original I-cone inclusion along the supplied arrow. -/
def cocone (F : Arrow (D (I := I))) :
    PushoutCocone ((OriginalICone.inclusion (B := B)).app F.left) F.hom :=
  (IsPushout.of_hasPushout ((OriginalICone.inclusion (B := B)).app F.left) F.hom).cocone

/-- The universal property of the chosen original I-cone pushout cocone. -/
def coconeIsColimit (F : Arrow (D (I := I))) : IsColimit (cocone (B := B) F) :=
  (IsPushout.of_hasPushout ((OriginalICone.inclusion (B := B)).app F.left) F.hom).isColimit

/-- Chosen Puppe suspension using the original I-cone and the original native zero object. -/
def suspension : D (I := I) ⥤ D (I := I) :=
  OrdinaryHoChosenPuppe.suspensionFunctor
    (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
    (cocone (B := B)) (coconeIsColimit (B := B))
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero

/-- The original cone span, with legs given by the I-cone inclusion and the map to native zero. -/
def coneSpan : D (I := I) ⥤ (WalkingSpan ⥤ D (I := I)) where
  obj X := span ((OriginalICone.inclusion (B := B)).app X) (Diagrams.toZero X)
  map f := spanHomMk f ((OriginalICone.cone (B := B)).map f) (𝟙 Diagrams.zeroDiagram)
    ((OriginalICone.inclusion (B := B)).naturality f).symm (by
      change Diagrams.toZero _ ≫ 𝟙 Diagrams.zeroDiagram = _ ≫ Diagrams.toZero _
      rw [Category.comp_id]
      exact (Diagrams.toZero_naturality f).symm)
  map_id X := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · exact (OriginalICone.cone (B := B)).map_id X
    · rfl
  map_comp f g := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · exact (OriginalICone.cone (B := B)).map_comp f g
    · exact (Category.id_comp _).symm

/-- The span whose two legs are the original maps from the source to native zero. -/
def zeroSpan : D (I := I) ⥤ (WalkingSpan ⥤ D (I := I)) where
  obj X := span (Diagrams.toZero X) (Diagrams.toZero X)
  map f := spanHomMk f (𝟙 Diagrams.zeroDiagram) (𝟙 Diagrams.zeroDiagram)
    (by
      change Diagrams.toZero _ ≫ 𝟙 Diagrams.zeroDiagram = _ ≫ Diagrams.toZero _
      rw [Category.comp_id]
      exact (Diagrams.toZero_naturality f).symm)
    (by
      change Diagrams.toZero _ ≫ 𝟙 Diagrams.zeroDiagram = _ ≫ Diagrams.toZero _
      rw [Category.comp_id]
      exact (Diagrams.toZero_naturality f).symm)
  map_id X := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _) <;> rfl
  map_comp f g := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm

/-- The natural map of spans induced by the original I-cone contraction. -/
def coneToZeroSpan : coneSpan (B := B) (I := I) ⟶ zeroSpan (I := I) where
  app X := spanHomMk (𝟙 X) ((OriginalICone.contraction (B := B)).app X)
    (𝟙 Diagrams.zeroDiagram)
    (by
      change (OriginalICone.inclusion (B := B)).app X ≫
        (OriginalICone.contraction (B := B)).app X = 𝟙 X ≫ Diagrams.toZero X
      rw [Category.id_comp]
      exact OriginalICone.inclusion_contraction X)
    (by
      change Diagrams.toZero X ≫ 𝟙 Diagrams.zeroDiagram = 𝟙 X ≫ Diagrams.toZero X
      simp)
  naturality X Y f := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · change f ≫ 𝟙 Y = 𝟙 X ≫ f
      simp
    · exact (OriginalICone.contraction (B := B)).naturality f
    · rfl

/-- The ordinary cone-span colimit agrees naturally with the chosen Puppe suspension. -/
def coneColimitIsoSuspension : coneSpan (B := B) (I := I) ⋙ colim ≅
    suspension (B := B) (I := I) :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change colim.map ((coneSpan (B := B)).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (suspension (B := B)).map f
    rw [Category.comp_id, Category.id_comp]
    apply pushout.hom_ext
    · exact (ι_colimMap ((coneSpan (B := B)).map f) WalkingSpan.left).trans
        (OrdinaryHoChosenPuppe.suspensionMap_cone
          (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
          (cocone (B := B)) (coconeIsColimit (B := B))
          Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero f).symm
    · have h := OrdinaryHoChosenPuppe.suspensionMap_zero
          (OriginalICone.cone (B := B)) (OriginalICone.inclusion (B := B))
          (cocone (B := B)) (coconeIsColimit (B := B))
          Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero f
      exact (ι_colimMap ((coneSpan (B := B)).map f) WalkingSpan.right).trans
        ((Category.id_comp _).trans h.symm))

/-- Comparison from the homotopy pushout of the original cone span to chosen suspension. -/
def toSuspension : coneSpan (B := B) (I := I) ⋙ homotopyPushout ⟶
    suspension (B := B) (I := I) :=
  Functor.whiskerLeft (coneSpan (B := B)) homotopyPushoutComparison ≫
    (coneColimitIsoSuspension (B := B)).hom

/-- The homotopy pushout map induced by the original I-cone contraction. -/
def toZeroPushout : coneSpan (B := B) (I := I) ⋙ homotopyPushout ⟶
    zeroSpan (I := I) ⋙ homotopyPushout :=
  Functor.whiskerRight (coneToZeroSpan (B := B)) homotopyPushout

/-- Contracting the original cone induces a weak equivalence of homotopy pushouts. -/
theorem toZeroPushout_weak (X : D (I := I)) :
    WeakEquivalence ((toZeroPushout (B := B)).app X) := by
  apply homotopyPushout_map_weakEquivalence ((coneToZeroSpan (B := B)).app X)
  intro j
  rcases j with (_ | _ | _)
  · change WeakEquivalence (𝟙 X)
    infer_instance
  · change WeakEquivalence ((OriginalICone.contraction (B := B)).app X)
    exact (weakEquivalence_iff _).mpr (OriginalICone.contraction_trivialFibration X).2
  · change WeakEquivalence (𝟙 Diagrams.zeroDiagram)
    infer_instance

/-- For a cofibrant source, the homotopy pushout comparison to chosen suspension is weak. -/
theorem toSuspension_weak (X : D (I := I)) [IsCofibrant X] :
    WeakEquivalence ((toSuspension (B := B)).app X) := by
  let _ : IsCofibrant ((coneSpan (B := B)).obj X |>.obj WalkingSpan.zero) := by
    change IsCofibrant X
    infer_instance
  let _ : IsCofibrant ((coneSpan (B := B)).obj X |>.obj WalkingSpan.right) := by
    change IsCofibrant (Diagrams.zeroDiagram (A := I))
    rw [isCofibrant_iff_of_isInitial (𝟙 Diagrams.zeroDiagram)
      Diagrams.zeroDiagramIsInitial]
    infer_instance
  let _ : Cofibration ((coneSpan (B := B)).obj X |>.map WalkingSpan.Hom.fst) :=
    (cofibration_iff _).mpr (OriginalICone.inclusion_cofibration X)
  have h := weakEquivalence_homotopyPushoutComparison_of_fst ((coneSpan (B := B)).obj X)
  let _ : WeakEquivalence
      ((homotopyPushoutComparison (C := D (I := I))).app ((coneSpan (B := B)).obj X)) := h
  change WeakEquivalence
    ((homotopyPushoutComparison (C := D (I := I))).app ((coneSpan (B := B)).obj X) ≫
      (coneColimitIsoSuspension (B := B)).hom.app X)
  let _ : WeakEquivalence ((coneColimitIsoSuspension (B := B)).hom.app X) := by
    infer_instance
  infer_instance

/-- Localize the two actual weak legs only after the original Q replacement.
The chosen Puppe suspension and the original zero-span homotopy pushout
have a complete natural isomorphism on all caller objects and maps. -/
def suspensionQIsoZeroPushoutQ :
    (Replacement.cofibrantReplacement (B := B) (A := I) ⋙ suspension (B := B)) ⋙
        toHomotopyCategory (D (I := I)) ≅
      (Replacement.cofibrantReplacement (B := B) (A := I) ⋙
        (zeroSpan (I := I) ⋙ homotopyPushout)) ⋙ toHomotopyCategory (D (I := I)) := by
  let Q := Replacement.cofibrantReplacement (B := B) (A := I)
  let H := toHomotopyCategory (D (I := I))
  let a := Functor.whiskerRight (Functor.whiskerLeft Q (toSuspension (B := B))) H
  let b := Functor.whiskerRight (Functor.whiskerLeft Q (toZeroPushout (B := B))) H
  let _ : ∀ X, IsIso (a.app X) := fun X => by
    let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := I) X
    change IsIso (H.map ((toSuspension (B := B)).app (Q.obj X)))
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      (toSuspension_weak (Q.obj X)).mem
  let _ : ∀ X, IsIso (b.app X) := fun X => by
    change IsIso (H.map ((toZeroPushout (B := B)).app (Q.obj X)))
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      (toZeroPushout_weak (Q.obj X)).mem
  let _ : IsIso a := NatIso.isIso_of_isIso_app a
  let _ : IsIso b := NatIso.isIso_of_isIso_app b
  exact (asIso a).symm ≪≫ asIso b

/-- The whole original source map of Q followed by chosen suspension is
retained in the forward comparison square. -/
theorem suspensionQIsoZeroPushoutQ_hom_naturality
    {X Y : D (I := I)} (f : X ⟶ Y) :
    (toHomotopyCategory (D (I := I))).map
        ((suspension (B := B)).map ((Replacement.cofibrantReplacement (B := B)).map f)) ≫
      (suspensionQIsoZeroPushoutQ (B := B)).hom.app Y =
    (suspensionQIsoZeroPushoutQ (B := B)).hom.app X ≫
      (toHomotopyCategory (D (I := I))).map
        (homotopyPushout.map ((zeroSpan (I := I)).map
          ((Replacement.cofibrantReplacement (B := B)).map f))) :=
  (suspensionQIsoZeroPushoutQ (B := B)).hom.naturality f

/-- The inverse comparison retains the same entire original source arrow. -/
theorem suspensionQIsoZeroPushoutQ_inv_naturality
    {X Y : D (I := I)} (f : X ⟶ Y) :
    (toHomotopyCategory (D (I := I))).map
        (homotopyPushout.map ((zeroSpan (I := I)).map
          ((Replacement.cofibrantReplacement (B := B)).map f))) ≫
      (suspensionQIsoZeroPushoutQ (B := B)).inv.app Y =
    (suspensionQIsoZeroPushoutQ (B := B)).inv.app X ≫
      (toHomotopyCategory (D (I := I))).map
        ((suspension (B := B)).map ((Replacement.cofibrantReplacement (B := B)).map f)) :=
  (suspensionQIsoZeroPushoutQ (B := B)).inv.naturality f

end HomotopicalAlgebra.EnrichedProjective.Native.OriginalISuspension
