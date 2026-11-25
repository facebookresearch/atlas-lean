/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberHomSequence
import Batteries.Tactic.Lint

/-!
# Full ordinary-Ho original fiber sequence clients

These clients retain the original first and zero projection functions,
arbitrary coefficients, and full source/target Hom transport functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OrdinaryHoChosenFiberHomSequence

namespace HomotopicalAlgebra.OrdinaryHoChosenFiberHomSequencePublicClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
  (Z : C) (hZ : IsZero Z)
  (s : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (hs : ∀ F, IsLimit (s F))

local notation "P" => OrdinaryHoChosenFiberMaps.fibrantFibrationProperty (C := C)

example (K : C) (F : (P).FullSubcategory) :
    Set.range (fun h : ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj
      ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).obj F.obj) =>
        h ≫ (firstProjection Z hZ s hs).app F) =
      {g | g ≫ ((weakEquivalences C).Q).map F.obj.hom =
        ((weakEquivalences C).Q).map (OrdinaryHoChosenFiberKernel.nullMap Z hZ K F.obj.right)} := by
  ext g
  exact first_exact Z hZ s hs K F g

example (F : (P).FullSubcategory) (E : C)
    (g : ((weakEquivalences C).Q).obj (s F.obj).pt ⟶ ((weakEquivalences C).Q).obj E) :
    fiberTargetHomEquiv Z hZ s hs F E ((fiberTargetHomEquiv Z hZ s hs F E).symm g) = g :=
  (fiberTargetHomEquiv Z hZ s hs F E).apply_symm_apply g

example (F : (P).FullSubcategory) :
    (fiberHoNatIso Z hZ s hs).hom.app F ≫ (firstProjection Z hZ s hs).app F =
        ((weakEquivalences C).Q).map (s F.obj).fst ∧
      (fiberHoNatIso Z hZ s hs).hom.app F ≫ (zeroProjection Z hZ s hs).app F =
        ((weakEquivalences C).Q).map (s F.obj).snd :=
  ⟨fiberHoNatIso_firstProjection Z hZ s hs F, fiberHoNatIso_zeroProjection Z hZ s hs F⟩

example {F G : (P).FullSubcategory} (q : F ⟶ G) {E E' : C} (p : E ⟶ E')
    (g : ((weakEquivalences C).Q).obj
      ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).obj G.obj) ⟶
      ((weakEquivalences C).Q).obj E) :
    fiberTargetHomEquiv Z hZ s hs F E'
        (((weakEquivalences C).Q).map
          ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).map q.hom) ≫
            (g ≫ ((weakEquivalences C).Q).map p)) =
      ((weakEquivalences C).Q).map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q.hom) ≫
        (fiberTargetHomEquiv Z hZ s hs G E g ≫ ((weakEquivalences C).Q).map p) := by
  rw [fiberTargetHomEquiv_source, fiberTargetHomEquiv_target]

section OriginalComparison

open OriginalJoin OrdinaryHoChosenFiberCofiberComparison.ArrowResolution

variable (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C)
  (hQ : ∀ X : C, IsCofibrant (Q.obj X))
  (hε : ∀ X : C, trivialFibrations C (ε.app X))
  (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))
  (hι : ∀ X : C, IsCofibrant X → cofibrations C (ι.app X))
  (hCone : ∀ X : C, IsCofibrant X →
    weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj X)))

example (F : Arrow C) :
    ((weakEquivalences C).Q).map (c (Q.mapArrow.obj F)).inr ≫
      (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F =
    ((weakEquivalences C).Q).map (c ((resolutionFunctor Q ε).obj F)).inr :=
  QCofiberToResolutionHoIso_target Z hZ Q ε hQ hε cone ι c hc hι hCone F

example (F : (P).FullSubcategory) :
    (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
      (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫
        (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F.obj =
    ((weakEquivalences C).Q).map
      (QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc ((resolutionFunctor Q ε).obj F.obj)) :=
  originalSuspendedFiberToQCofiber_equation Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F

example {F G : (P).FullSubcategory} (q : F ⟶ G) {E E' : C} (p : E ⟶ E')
    (g : ((weakEquivalences C).Q).obj (c (Q.mapArrow.obj G.obj)).pt ⟶
      ((weakEquivalences C).Q).obj E) :
    originalSuspendedFiberRestriction Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F E'
      (((weakEquivalences C).Q).map
        (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc (Q.mapArrow.map q.hom)) ≫
          (g ≫ ((weakEquivalences C).Q).map p)) =
    ((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q.hom))) ≫
      (originalSuspendedFiberRestriction Z hZ s hs Q ε hQ hε cone ι c hc hι hCone G E g ≫
        ((weakEquivalences C).Q).map p) := by
  rw [originalSuspendedFiberRestriction_source, originalSuspendedFiberRestriction_target]

variable (t : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (ht : ∀ F, IsLimit (t F))
  (d : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hd : ∀ F, IsColimit (d F))

example (F : (P).FullSubcategory) {E E' : C} (p : E ⟶ E')
    (g : ((weakEquivalences C).Q).obj (d (Q.mapArrow.obj F.obj)).pt ⟶
      ((weakEquivalences C).Q).obj E) :
    ((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F.obj).hom)) ≫
      ((weakEquivalences C).Q).map (OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceIso
        cone ι c hc d hd (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (t F.obj).pt)))).hom ≫
        ((originalSuspendedFiberToQCofiber Z hZ t ht Q ε hQ hε cone ι d hd hι hCone).app F ≫
          (g ≫ ((weakEquivalences C).Q).map p)) =
    (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫
      (((weakEquivalences C).Q).map (OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceIso
        cone ι c hc d hd (Q.mapArrow.obj F.obj)).hom ≫ (g ≫ ((weakEquivalences C).Q).map p)) := by
  let γf := ((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
    (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F.obj).hom))
  let γc := ((weakEquivalences C).Q).map (OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceIso
    cone ι c hc d hd (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (t F.obj).pt)))).hom
  let γq := ((weakEquivalences C).Q).map (OrdinaryHoChosenFiberCofiberComparison.cofiberChoiceIso
    cone ι c hc d hd (Q.mapArrow.obj F.obj)).hom
  let u := (originalSuspendedFiberToQCofiber Z hZ t ht Q ε hQ hε cone ι d hd hι hCone).app F
  let v := (originalSuspendedFiberToQCofiber Z hZ t ht Q ε hQ hε cone ι c hc hι hCone).app F
  let w := (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F
  have hCF : γc ≫ u = v ≫ γq := originalSuspendedFiberToQCofiber_cofiberChoice
    Z hZ t ht Q ε hQ hε cone ι c hc hι hCone d hd F
  have hF : γf ≫ v = w := originalSuspendedFiberToQCofiber_choice
    Z hZ s hs Q ε hQ hε cone ι c hc hι hCone t ht F
  change γf ≫ (γc ≫ (u ≫ (g ≫ ((weakEquivalences C).Q).map p))) =
    w ≫ (γq ≫ (g ≫ ((weakEquivalences C).Q).map p))
  calc
    _ = γf ≫ (v ≫ (γq ≫ (g ≫ ((weakEquivalences C).Q).map p))) := by
      simpa only [Category.assoc] using congrArg
        (fun m => γf ≫ (m ≫ (g ≫ ((weakEquivalences C).Q).map p))) hCF
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun m => m ≫ (γq ≫ (g ≫ ((weakEquivalences C).Q).map p))) hF

end OriginalComparison

#print axioms HomotopicalAlgebra.OrdinaryHoChosenFiberHomSequence.fiberHoNatIso
#print axioms HomotopicalAlgebra.OrdinaryHoChosenFiberHomSequence.first_exact
#print axioms HomotopicalAlgebra.OrdinaryHoChosenFiberHomSequence.fiberTargetHomEquiv

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberHomSequence

end HomotopicalAlgebra.OrdinaryHoChosenFiberHomSequencePublicClients
