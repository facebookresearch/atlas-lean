/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberCofiberComparison
import Batteries.Tactic.Lint

/-!
# Public original chosen-fiber and cofiber comparison clients

The clients retain both original projections, the actual source Arrow
components, and full Hom precomposition with target maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OrdinaryHoChosenFiberCofiberComparison

namespace HomotopicalAlgebra.OrdinaryHoChosenFiberCofiberComparisonPublicClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
  (Z : C) (hZ : IsZero Z)
  (s : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (hs : ∀ F, IsLimit (s F))

omit [ModelCategory C]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
theorem originalFiberCospan_eq (F : Arrow C) :
    (fiberDiagram Z hZ).obj F = cospan F.hom (hZ.isInitial.to F.right) := rfl

omit [ModelCategory C]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
theorem originalFiberCospan_map {F G : Arrow C} (q : F ⟶ G) :
    ((fiberDiagram Z hZ).map q).app WalkingCospan.one = q.right ∧
      ((fiberDiagram Z hZ).map q).app WalkingCospan.left = q.left ∧
      ((fiberDiagram Z hZ).map q).app WalkingCospan.right = 𝟙 Z :=
  ⟨rfl, rfl, rfl⟩

omit [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
theorem originalOrdinaryFiber_projections (F : Arrow C) :
    (ordinaryCone Z hZ F).fst =
      limit.π (cospan F.hom (hZ.isInitial.to F.right)) WalkingCospan.left ∧
    (ordinaryCone Z hZ F).snd =
      limit.π (cospan F.hom (hZ.isInitial.to F.right)) WalkingCospan.right :=
  ⟨rfl, rfl⟩

theorem originalHomotopyFiber_obj (F : Arrow C) :
    (originalHomotopyFiber Z hZ).obj F =
      homotopyPullback.obj (cospan F.hom (hZ.isInitial.to F.right)) := rfl

theorem originalHomotopyFiber_map {F G : Arrow C} (q : F ⟶ G) :
    (originalHomotopyFiber Z hZ).map q =
      homotopyPullback.map ((fiberDiagram Z hZ).map q) := rfl

omit [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
theorem canonicalZeroTransport_maps (F : Arrow C) :
    letI := hZ.hasZeroObject
    ((canonicalFiberCospanIso Z hZ).hom.app F).app WalkingCospan.right ≫
      initial.to F.right = hZ.isInitial.to F.right ∧
    ((canonicalFiberCospanIso Z hZ).inv.app F).app WalkingCospan.right ≫
      hZ.isInitial.to F.right = initial.to F.right := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact ⟨canonicalZeroIso_hom_to Z hZ F.right, canonicalZeroIso_inv_to Z hZ F.right⟩

omit [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
theorem canonicalOrdinaryTransport_projections (F : Arrow C) :
    letI := hZ.hasZeroObject
    (ordinaryFiberCanonicalIso Z hZ).hom.app F ≫
      limit.π ((fiberCospan (C := C)).obj F) WalkingCospan.left =
        (ordinaryCone Z hZ F).fst ∧
    (ordinaryFiberCanonicalIso Z hZ).hom.app F ≫
      limit.π ((fiberCospan (C := C)).obj F) WalkingCospan.right =
        (ordinaryCone Z hZ F).snd ≫ (canonicalZeroIso Z hZ).hom := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact ⟨ordinaryFiberCanonicalIso_hom_fst Z hZ F, ordinaryFiberCanonicalIso_hom_snd Z hZ F⟩

omit [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
theorem canonicalOrdinaryInverseTransport_projections (F : Arrow C) :
    letI := hZ.hasZeroObject
    (ordinaryFiberCanonicalIso Z hZ).inv.app F ≫ (ordinaryCone Z hZ F).fst =
      limit.π ((fiberCospan (C := C)).obj F) WalkingCospan.left ∧
    (ordinaryFiberCanonicalIso Z hZ).inv.app F ≫ (ordinaryCone Z hZ F).snd =
      limit.π ((fiberCospan (C := C)).obj F) WalkingCospan.right ≫
        (canonicalZeroIso Z hZ).inv := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact ⟨ordinaryFiberCanonicalIso_inv_fst Z hZ F, ordinaryFiberCanonicalIso_inv_snd Z hZ F⟩

theorem originalHomotopyComparison_map (F : Arrow C) :
    (originalToHomotopyFiber Z hZ s hs).app F =
      (originalToOrdinaryIso Z hZ s hs F).hom ≫
        homotopyPullbackComparison.app (cospan F.hom (hZ.isInitial.to F.right)) :=
  originalToHomotopyFiber_app Z hZ s hs F

example (F : Arrow C) :
    (originalToOrdinaryIso Z hZ s hs F).hom ≫ (ordinaryCone Z hZ F).fst = (s F).fst ∧
      (originalToOrdinaryIso Z hZ s hs F).hom ≫ (ordinaryCone Z hZ F).snd = (s F).snd :=
  ⟨originalToOrdinaryIso_fst Z hZ s hs F, originalToOrdinaryIso_snd Z hZ s hs F⟩

example {F G : Arrow C} (q : F ⟶ G)
    [Fibration F.hom] [Fibration G.hom] [IsFibrant F.right] [IsFibrant G.right]
    [WeakEquivalence q.left] [WeakEquivalence q.right] :
    weakEquivalences C (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q) :=
  originalChosenMap_weak Z hZ s hs q

variable (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

example {F G : Arrow C} (q : F ⟶ G) {E E' : C} (p : E ⟶ E')
    (g : ((weakEquivalences C).Q).obj (c G).pt ⟶ ((weakEquivalences C).Q).obj E) :
    ((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
        (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q)) ≫
      (((weakEquivalences C).Q).map (suspensionToCofiber Z hZ s cone ι c hc G) ≫
        (g ≫ ((weakEquivalences C).Q).map p)) =
      ((weakEquivalences C).Q).map (suspensionToCofiber Z hZ s cone ι c hc F) ≫
        (((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q) ≫
          (g ≫ ((weakEquivalences C).Q).map p)) := by
  rw [← Category.assoc, ← Functor.map_comp, suspensionToCofiber_naturality,
    Functor.map_comp, Category.assoc]

example (F : Arrow C) :
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (s F).pt).inl ≫
        (suspensionToCofiberNatTrans Z hZ s hs cone ι c hc).app F =
      cone.map (s F).fst ≫ (c F).inl :=
  suspensionToCofiber_cone Z hZ s cone ι c hc F

section Resolution

open ArrowResolution

variable (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C)
  (hQ : ∀ X : C, IsCofibrant (Q.obj X))
  (hε : ∀ X : C, trivialFibrations C (ε.app X))
  (hι : ∀ X : C, IsCofibrant X → cofibrations C (ι.app X))
  (hCone : ∀ X : C, IsCofibrant X →
    weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj X)))

example {F G : Arrow C} (q : F ⟶ G) :
    Q.map q.left ≫ sourceToCorner Q ε G = sourceToCorner Q ε F ≫ cornerMap Q ε q :=
  sourceToCorner_naturality Q ε q

example (F : Arrow C) :
    weakEquivalences C (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc
        (intermediateToQ Q ε F)) ∧
      weakEquivalences C (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc
        (intermediateToResolution Q ε F)) :=
  ⟨intermediateToQ_cofiber_weak Z hZ Q ε hQ hε cone ι c hc hι hCone F,
    intermediateToResolution_cofiber_weak Z hZ Q ε hQ hε cone ι c hc hι hCone F⟩

example (F : Arrow C) :
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (Q.obj (s F).pt)).inl ≫
        QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F =
      cone.map (ε.app (s F).pt ≫ (s F).fst) ≫ (c F).inl ∧
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (Q.obj (s F).pt)).inr ≫
        QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F =
      hZ.isInitial.to F.right ≫ (c F).inr :=
  ⟨QFiberSuspensionToCofiber_cone Z hZ s Q ε cone ι c hc F,
    QFiberSuspensionToCofiber_zero Z hZ s Q ε cone ι c hc F⟩

example (F : Arrow C) :
    QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F ≫
      OrdinaryHoChosenPuppe.boundary cone ι c hc Z hZ F =
    OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (ε.app (s F).pt ≫ (s F).fst) :=
  QFiberSuspensionToCofiber_boundary Z hZ s Q ε cone ι c hc F

example {F G : Arrow C} (q : F ⟶ G) {E E' : C} (p : E ⟶ E')
    (g : ((weakEquivalences C).Q).obj (c G).pt ⟶ ((weakEquivalences C).Q).obj E) :
    ((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q))) ≫
      (((weakEquivalences C).Q).map (QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc G) ≫
        (g ≫ ((weakEquivalences C).Q).map p)) =
    ((weakEquivalences C).Q).map (QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F) ≫
      (((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q) ≫
        (g ≫ ((weakEquivalences C).Q).map p)) := by
  rw [← Category.assoc, ← Functor.map_comp, QFiberSuspensionToCofiber_naturality,
    Functor.map_comp, Category.assoc]

example (F : Arrow C) [Fibration F.hom] [IsFibrant F.right] :
    weakEquivalences C
      ((resolvedQFiberSuspensionToOriginalNatTrans Z hZ s hs Q ε cone ι c hc).app F) :=
  resolvedQFiberSuspensionToOriginal_weak Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F

variable (t : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (ht : ∀ F, IsLimit (t F))
  (d : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hd : ∀ F, IsColimit (d F))

example (F : Arrow C) :
    (c F).inl ≫ (cofiberChoiceIso cone ι c hc d hd F).hom = (d F).inl ∧
      (c F).inr ≫ (cofiberChoiceIso cone ι c hc d hd F).hom = (d F).inr :=
  ⟨cofiberChoiceIso_hom_cone cone ι c hc d hd F,
    cofiberChoiceIso_hom_target cone ι c hc d hd F⟩

example (F : Arrow C) :
    (cofiberChoiceIso cone ι c hc d hd F).hom ≫
      OrdinaryHoChosenPuppe.boundary cone ι d hd Z hZ F =
    OrdinaryHoChosenPuppe.boundary cone ι c hc Z hZ F ≫
      (cofiberChoiceIso cone ι c hc d hd
        (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ F.left))).hom :=
  boundary_cofiberChoice Z hZ cone ι c hc d hd F

example (F : Arrow C) :
    OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F).hom) ≫
        QFiberSuspensionToCofiber Z hZ t Q ε cone ι c hc F =
      QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F :=
  QFiberSuspensionToCofiber_choice Z hZ s hs Q ε cone ι c hc t ht F

example (F : Arrow C) (K : C) (g : K ⟶ F.right)
    [IsCofibrant K] [IsCofibrant F.right] [IsFibrant (c F).pt]
    [Cofibration (ι.app K)] [Cofibration (ι.app F.right)]
    (hg : ((weakEquivalences C).Q).map (g ≫ (c F).inr) =
      ((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.nullMap Z hZ K (c F).pt))
    (E : C) (p : ((weakEquivalences C).Q).obj
      (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ F.right).pt ⟶
        ((weakEquivalences C).Q).obj E) :
    ∃ k : ((weakEquivalences C).Q).obj (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ K).pt ⟶
        ((weakEquivalences C).Q).obj
          (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ F.left).pt,
      (k ≫ ((weakEquivalences C).Q).map
        (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ F.hom)) ≫ p =
      ((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ g) ≫ p := by
  obtain ⟨k, hk⟩ := suspendedCoefficientLift_of_null Z hZ cone ι c hc F K g
    (hCone _ inferInstance) (hCone _ inferInstance) hg
  exact ⟨k, congrArg (fun m => m ≫ p) hk⟩

end Resolution

#print axioms HomotopicalAlgebra.OrdinaryHoChosenFiberCofiberComparison.originalToHomotopyFiber_weak
#print axioms HomotopicalAlgebra.OrdinaryHoChosenFiberCofiberComparison.originalChosenMap_weak
#print axioms HomotopicalAlgebra.OrdinaryHoChosenFiberCofiberComparison.suspensionToCofiber_naturality

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberCofiberComparison

end HomotopicalAlgebra.OrdinaryHoChosenFiberCofiberComparisonPublicClients
