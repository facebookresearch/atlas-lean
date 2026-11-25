/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberCofiberComparison

/-!
# Ordinary-Ho transport of the original chosen fiber Hom sequence

The weak comparison from the same original chosen fiber constructs its
ordinary-Ho Iso to the homotopy fiber. Both original projections are
transported through that actual Iso. Their full naturality and the
first image/null-kernel law retain every coefficient and original Arrow.

Contravariant Hom into every target is transported by the same whole
comparison functions. The native integer fiber/cofiber sequence requires
the further source-loop comparison and its native test proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryHoChosenFiberHomSequence

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
  (Z : C) (hZ : IsZero Z)
  (s : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (hs : ∀ F, IsLimit (s F))

local notation "H" => (MorphismProperty.Q (weakEquivalences C))
local notation "P" => OrdinaryHoChosenFiberMaps.fibrantFibrationProperty (C := C)

/-- The same original weak fiber comparison gives a complete ordinary-Ho natural Iso. -/
def fiberHoNatIso :
    (P).ι ⋙ OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙ (H) ≅
      (P).ι ⋙ OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ ⋙ (H) := by
  let τ := Functor.whiskerLeft (P).ι (Functor.whiskerRight
    (OrdinaryHoChosenFiberCofiberComparison.originalToHomotopyFiber Z hZ s hs) (H))
  let _ : ∀ F, IsIso (τ.app F) := fun F => by
    let _ : Fibration F.obj.hom := F.property.1
    let _ : IsFibrant F.obj.right := F.property.2
    exact Localization.inverts (H) (weakEquivalences C) _
      (OrdinaryHoChosenFiberCofiberComparison.originalToHomotopyFiber_weak Z hZ s hs F.obj)
  let _ : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- Its forward endpoint is the unchanged original continuous comparison. -/
theorem fiberHoNatIso_hom (F : (P).FullSubcategory) :
    (fiberHoNatIso Z hZ s hs).hom.app F = (H).map
      ((OrdinaryHoChosenFiberCofiberComparison.originalToHomotopyFiber Z hZ s hs).app F.obj) :=
  rfl

/-- The whole first projection is transported through the inverse of the actual comparison. -/
def firstProjection :
    (P).ι ⋙ OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ ⋙ (H) ⟶
      (P).ι ⋙ Arrow.leftFunc ⋙ (H) :=
  (fiberHoNatIso Z hZ s hs).inv ≫ Functor.whiskerLeft (P).ι
    (Functor.whiskerRight (OrdinaryHoChosenFiberMaps.firstLegNatTrans Z hZ s hs) (H))

/-- The whole original zero projection uses the same inverse comparison and original zero. -/
def zeroProjection :
    (P).ι ⋙ OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ ⋙ (H) ⟶
      (P).ι ⋙ (Functor.const (Arrow C)).obj Z ⋙ (H) :=
  (fiberHoNatIso Z hZ s hs).inv ≫ Functor.whiskerLeft (P).ι
    (Functor.whiskerRight (OrdinaryHoChosenFiberMaps.zeroLegNatTrans Z hZ s hs) (H))

/-- The transported complete first projection reconstructs the original first leg. -/
theorem fiberHoNatIso_firstProjection (F : (P).FullSubcategory) :
    (fiberHoNatIso Z hZ s hs).hom.app F ≫ (firstProjection Z hZ s hs).app F =
      (H).map (s F.obj).fst := by
  change (fiberHoNatIso Z hZ s hs).hom.app F ≫
    ((fiberHoNatIso Z hZ s hs).inv.app F ≫ (H).map (s F.obj).fst) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ (H).map (s F.obj).fst)
      (congr_app (fiberHoNatIso Z hZ s hs).hom_inv_id F)).trans (Category.id_comp _))

/-- The transported complete zero projection reconstructs the same original collapse. -/
theorem fiberHoNatIso_zeroProjection (F : (P).FullSubcategory) :
    (fiberHoNatIso Z hZ s hs).hom.app F ≫ (zeroProjection Z hZ s hs).app F =
      (H).map (s F.obj).snd := by
  change (fiberHoNatIso Z hZ s hs).hom.app F ≫
    ((fiberHoNatIso Z hZ s hs).inv.app F ≫ (H).map (s F.obj).snd) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ (H).map (s F.obj).snd)
      (congr_app (fiberHoNatIso Z hZ s hs).hom_inv_id F)).trans (Category.id_comp _))

/-- All actual Arrow source and target components retain full first-projection naturality. -/
theorem firstProjection_naturality {F G : (P).FullSubcategory} (q : F ⟶ G) :
    (H).map ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).map q.hom) ≫
        (firstProjection Z hZ s hs).app G =
      (firstProjection Z hZ s hs).app F ≫ (H).map q.hom.left :=
  (firstProjection Z hZ s hs).naturality q

/-- All complete source Arrows preserve the original zero projection after transport. -/
theorem zeroProjection_naturality {F G : (P).FullSubcategory} (q : F ⟶ G) :
    (H).map ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).map q.hom) ≫
        (zeroProjection Z hZ s hs).app G = (zeroProjection Z hZ s hs).app F := by
  have h := (zeroProjection Z hZ s hs).naturality q
  change (H).map
      ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).map q.hom) ≫
      (zeroProjection Z hZ s hs).app G =
    (zeroProjection Z hZ s hs).app F ≫ (H).map (𝟙 Z) at h
  exact h.trans ((congrArg (fun m => (zeroProjection Z hZ s hs).app F ≫ m)
    ((H).map_id Z)).trans (Category.comp_id _))

/-- The actual transported first-leg image is the original null kernel for every coefficient. -/
theorem first_exact (K : C) (F : (P).FullSubcategory)
    (g : (H).obj K ⟶ (H).obj F.obj.left) :
    (∃ h : (H).obj K ⟶ (H).obj
        ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).obj F.obj),
      h ≫ (firstProjection Z hZ s hs).app F = g) ↔
      g ≫ (H).map F.obj.hom =
        (H).map (OrdinaryHoChosenFiberKernel.nullMap Z hZ K F.obj.right) := by
  let _ : Fibration F.obj.hom := F.property.1
  let _ : IsFibrant F.obj.right := F.property.2
  constructor
  · rintro ⟨h, hh⟩
    apply (OrdinaryHoChosenFiberKernel.chosenFiberHoImage_anyCoefficient_iff
      Z hZ K F.obj.hom (s F.obj) (hs F.obj) g).mp
    refine ⟨h ≫ (fiberHoNatIso Z hZ s hs).inv.app F, ?_⟩
    exact (Category.assoc _ _ _).trans hh
  · intro hg
    obtain ⟨h, hh⟩ :=
      (OrdinaryHoChosenFiberKernel.chosenFiberHoImage_anyCoefficient_iff
        Z hZ K F.obj.hom (s F.obj) (hs F.obj) g).mpr hg
    refine ⟨h ≫ (fiberHoNatIso Z hZ s hs).hom.app F, ?_⟩
    rw [Category.assoc, fiberHoNatIso_firstProjection]
    exact hh

/-- Entire contravariant Hom tests transport through the original comparison and its actual
inverse. -/
def fiberTargetHomEquiv (F : (P).FullSubcategory) (E : C) :
    ((H).obj ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).obj F.obj) ⟶
        (H).obj E) ≃ ((H).obj (s F.obj).pt ⟶ (H).obj E) where
  toFun g := (fiberHoNatIso Z hZ s hs).hom.app F ≫ g
  invFun g := (fiberHoNatIso Z hZ s hs).inv.app F ≫ g
  left_inv g := by
    change (fiberHoNatIso Z hZ s hs).inv.app F ≫
      ((fiberHoNatIso Z hZ s hs).hom.app F ≫ g) = g
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ g) (congr_app (fiberHoNatIso Z hZ s hs).inv_hom_id F)).trans
        (Category.id_comp _))
  right_inv g := by
    change (fiberHoNatIso Z hZ s hs).hom.app F ≫
      ((fiberHoNatIso Z hZ s hs).inv.app F ≫ g) = g
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ g) (congr_app (fiberHoNatIso Z hZ s hs).hom_inv_id F)).trans
        (Category.id_comp _))

/-- Its complete forward function is the original ordinary-Ho comparison precomposition. -/
theorem fiberTargetHomEquiv_apply (F : (P).FullSubcategory) (E : C)
    (g : (H).obj
      ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).obj F.obj) ⟶ (H).obj E) :
    fiberTargetHomEquiv Z hZ s hs F E g =
      (H).map ((OrdinaryHoChosenFiberCofiberComparison.originalToHomotopyFiber Z hZ s hs).app
        F.obj) ≫ g := rfl

/-- Complete contravariant source Arrow functions commute
through original fiber Hom transport. -/
theorem fiberTargetHomEquiv_source {F G : (P).FullSubcategory} (q : F ⟶ G) (E : C)
    (g : (H).obj
      ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).obj G.obj) ⟶ (H).obj E) :
    fiberTargetHomEquiv Z hZ s hs F E
        ((H).map ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).map q.hom) ≫
          g) = (H).map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q.hom) ≫
        fiberTargetHomEquiv Z hZ s hs G E g := by
  change (fiberHoNatIso Z hZ s hs).hom.app F ≫ (_ ≫ g) =
    (H).map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q.hom) ≫
      ((fiberHoNatIso Z hZ s hs).hom.app G ≫ g)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun m => m ≫ g) ((fiberHoNatIso Z hZ s hs).hom.naturality q).symm

/-- Every whole target map commutes with the complete original fiber Hom functions. -/
theorem fiberTargetHomEquiv_target (F : (P).FullSubcategory) {E E' : C} (p : E ⟶ E')
    (g : (H).obj
      ((OrdinaryHoChosenFiberCofiberComparison.originalHomotopyFiber Z hZ).obj F.obj) ⟶ (H).obj E) :
    fiberTargetHomEquiv Z hZ s hs F E' (g ≫ (H).map p) =
      fiberTargetHomEquiv Z hZ s hs F E g ≫ (H).map p := by
  change (fiberHoNatIso Z hZ s hs).hom.app F ≫ (g ≫ (H).map p) =
    ((fiberHoNatIso Z hZ s hs).hom.app F ≫ g) ≫ (H).map p
  exact (Category.assoc _ _ _).symm

namespace OriginalJoin

open OrdinaryHoChosenFiberCofiberComparison
open OrdinaryHoChosenFiberCofiberComparison.ArrowResolution

variable (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C)
  (hQ : ∀ X : C, IsCofibrant (Q.obj X))
  (hε : ∀ X : C, trivialFibrations C (ε.app X))
  (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))
  (hι : ∀ X : C, IsCofibrant X → cofibrations C (ι.app X))
  (hCone : ∀ X : C, IsCofibrant X →
    weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj X)))

local notation "CF" => OrdinaryHoChosenPuppe.cofiberFunctor cone ι c hc
local notation "S" => OrdinaryHoChosenPuppe.suspensionFunctor cone ι c hc Z hZ
local notation "Fib" => OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs
local notation "R" => resolutionFunctor Q ε
local notation "T" => intermediateFunctor Q ε

/-- The first complete common-resolution cofiber map gives its actual natural Iso in ordinary Ho. -/
def commonToQHoIso : (T) ⋙ (CF) ⋙ (H) ≅ Q.mapArrow ⋙ (CF) ⋙ (H) := by
  let τ := Functor.whiskerRight
    (Functor.whiskerRight (intermediateToQNatTrans Q ε) (CF)) (H)
  let _ : ∀ F, IsIso (τ.app F) := fun F => Localization.inverts (H)
    (weakEquivalences C) _
    (intermediateToQ_cofiber_weak Z hZ Q ε hQ hε cone ι c hc hι hCone F)
  let _ : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- The second common-resolution cofiber map gives the natural Iso to the resolved cofiber. -/
def commonToResolutionHoIso : (T) ⋙ (CF) ⋙ (H) ≅ (R) ⋙ (CF) ⋙ (H) := by
  let τ := Functor.whiskerRight
    (Functor.whiskerRight (intermediateToResolutionNatTrans Q ε) (CF)) (H)
  let _ : ∀ F, IsIso (τ.app F) := fun F => Localization.inverts (H)
    (weakEquivalences C) _
    (intermediateToResolution_cofiber_weak Z hZ Q ε hQ hε cone ι c hc hι hCone F)
  let _ : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- The original chosen Q cofiber and resolved cofiber are joined by their two actual weak legs. -/
def QCofiberToResolutionHoIso : Q.mapArrow ⋙ (CF) ⋙ (H) ≅ (R) ⋙ (CF) ⋙ (H) :=
  (commonToQHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).symm ≪≫
    commonToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone

omit [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
/-- The entire common-resolution zigzag is recovered on its original chosen cofiber functions. -/
theorem QCofiberToResolutionHoIso_equation (F : Arrow C) :
    (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc (intermediateToQ Q ε F)) ≫
      (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F =
        (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc
          (intermediateToResolution Q ε F)) := by
  change (commonToQHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
    ((commonToQHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).inv.app F ≫
      (commonToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F) = _
  rw [← Category.assoc, show (commonToQHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
    (commonToQHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).inv.app F = 𝟙 _ from
      congr_app (commonToQHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom_inv_id F,
    Category.id_comp]
  rfl

omit [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
/-- The complete first chosen-cofiber legs retain both actual common-source cone functions. -/
theorem QCofiberToResolutionHoIso_cone (F : Arrow C) :
    (H).map (cone.map (ε.app (Q.obj F.left))) ≫ (H).map (c (Q.mapArrow.obj F)).inl ≫
      (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F =
        (H).map (cone.map (Q.map (sourceToCorner Q ε F))) ≫
          (H).map (c ((R).obj F)).inl := by
  have h := congrArg (fun m => (H).map (c ((T).obj F)).inl ≫ m)
    (QCofiberToResolutionHoIso_equation Z hZ Q ε hQ hε cone ι c hc hι hCone F)
  simp only [← Category.assoc, ← Functor.map_comp,
    OrdinaryHoChosenPuppe.cofiberMap_cone] at h
  change (H).map (cone.map (ε.app (Q.obj F.left)) ≫ (c (Q.mapArrow.obj F)).inl) ≫
    (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F =
      (H).map (cone.map (Q.map (sourceToCorner Q ε F)) ≫ (c ((R).obj F)).inl) at h
  simpa only [Functor.map_comp, Category.assoc] using h

omit [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
/-- The second whole chosen-cofiber legs are the original Q-target functions on both sides. -/
theorem QCofiberToResolutionHoIso_target (F : Arrow C) :
    (H).map (c (Q.mapArrow.obj F)).inr ≫
      (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F =
        (H).map (c ((R).obj F)).inr := by
  have h := congrArg (fun m => (H).map (c ((T).obj F)).inr ≫ m)
    (QCofiberToResolutionHoIso_equation Z hZ Q ε hQ hε cone ι c hc hι hCone F)
  simp only [← Category.assoc, ← Functor.map_comp,
    OrdinaryHoChosenPuppe.cofiberMap_target] at h
  change (H).map (𝟙 (Q.obj F.right) ≫ (c (Q.mapArrow.obj F)).inr) ≫
    (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F =
      (H).map (𝟙 (Q.obj F.right) ≫ (c ((R).obj F)).inr) at h
  rw [show 𝟙 (Q.obj F.right) ≫ (c (Q.mapArrow.obj F)).inr = (c (Q.mapArrow.obj F)).inr from
    Category.id_comp _,
    show 𝟙 (Q.obj F.right) ≫ (c ((R).obj F)).inr = (c ((R).obj F)).inr from
      Category.id_comp _] at h
  exact h

/-- The actual resolved-to-original suspended Q-fiber map is a full ordinary-Ho natural Iso. -/
def resolvedQFiberSuspensionHoIso :
    (P).ι ⋙ (R) ⋙ (Fib) ⋙ Q ⋙ (S) ⋙ (H) ≅ (P).ι ⋙ (Fib) ⋙ Q ⋙ (S) ⋙ (H) := by
  let τ := Functor.whiskerLeft (P).ι (Functor.whiskerRight
    (resolvedQFiberSuspensionToOriginalNatTrans Z hZ s hs Q ε cone ι c hc) (H))
  let _ : ∀ F, IsIso (τ.app F) := fun F => by
    let _ : Fibration F.obj.hom := F.property.1
    let _ : IsFibrant F.obj.right := F.property.2
    exact Localization.inverts (H) (weakEquivalences C) _
      (resolvedQFiberSuspensionToOriginal_weak Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F.obj)
  let _ : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- The suspended-original-fiber to original Q-cofiber map uses the constructed zigzags. -/
def originalSuspendedFiberToQCofiber :
    (P).ι ⋙ (Fib) ⋙ Q ⋙ (S) ⋙ (H) ⟶ (P).ι ⋙ Q.mapArrow ⋙ (CF) ⋙ (H) :=
  (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).inv ≫
    Functor.whiskerLeft ((P).ι ⋙ (R))
      (Functor.whiskerRight (QFiberSuspensionToCofiberNatTrans Z hZ s hs Q ε cone ι c hc) (H)) ≫
    (Functor.isoWhiskerLeft (P).ι
      (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone)).inv

/-- Transport recovers the exact actual resolved Q-fiber null square and chosen cofiber function. -/
theorem originalSuspendedFiberToQCofiber_equation (F : (P).FullSubcategory) :
    (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
      (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫
        (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F.obj =
      (H).map (QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc ((R).obj F.obj)) := by
  let eF := resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone
  let eC := QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone
  change eF.hom.app F ≫ ((eF.inv.app F ≫ _ ≫ eC.inv.app F.obj) ≫ eC.hom.app F.obj) = _
  simp only [← Category.assoc]
  rw [show eF.hom.app F ≫ eF.inv.app F = 𝟙 _ from congr_app eF.hom_inv_id F,
    Category.id_comp, Category.assoc,
    show eC.inv.app F.obj ≫ eC.hom.app F.obj = 𝟙 _ from congr_app eC.inv_hom_id F.obj,
    Category.comp_id]
  rfl

/-- The complete original comparison is natural on every actual fibrant-fibration Arrow square. -/
theorem originalSuspendedFiberToQCofiber_naturality
    {F G : (P).FullSubcategory} (q : F ⟶ G) :
    (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q.hom))) ≫
        (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app G =
      (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫
        (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc (Q.mapArrow.map q.hom)) :=
  (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).naturality q

/-- The full cone leg of the original comparison recovers the actual resolved fiber inclusion. -/
theorem originalSuspendedFiberToQCofiber_cone (F : (P).FullSubcategory) :
    (H).map (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ
      (Q.obj (s ((R).obj F.obj)).pt)).inl ≫
      (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
        (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫
          (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F.obj =
      (H).map (cone.map (ε.app (s ((R).obj F.obj)).pt ≫ (s ((R).obj F.obj)).fst) ≫
        (c ((R).obj F.obj)).inl) := by
  have h := congrArg (fun m => (H).map (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ
    (Q.obj (s ((R).obj F.obj)).pt)).inl ≫ m)
    (originalSuspendedFiberToQCofiber_equation Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F)
  rw [← Functor.map_comp, QFiberSuspensionToCofiber_cone] at h
  exact h

/-- The whole original zero leg of the comparison is recovered through the same actual zigzags. -/
theorem originalSuspendedFiberToQCofiber_zero (F : (P).FullSubcategory) :
    (H).map (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ
      (Q.obj (s ((R).obj F.obj)).pt)).inr ≫
      (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
        (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫
          (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F.obj =
      (H).map (hZ.isInitial.to ((R).obj F.obj).right ≫ (c ((R).obj F.obj)).inr) := by
  have h := congrArg (fun m => (H).map (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ
    (Q.obj (s ((R).obj F.obj)).pt)).inr ≫ m)
    (originalSuspendedFiberToQCofiber_equation Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F)
  rw [← Functor.map_comp, QFiberSuspensionToCofiber_zero] at h
  exact h

/-- The original boundary recovers the suspension of the actual resolved Q-fiber projection. -/
theorem originalSuspendedFiberToQCofiber_boundary (F : (P).FullSubcategory) :
    (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
      (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫
        (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F.obj ≫
          (H).map (OrdinaryHoChosenPuppe.boundary cone ι c hc Z hZ ((R).obj F.obj)) =
      (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
        (ε.app (s ((R).obj F.obj)).pt ≫ (s ((R).obj F.obj)).fst)) := by
  have h := congrArg (fun m => m ≫
    (H).map (OrdinaryHoChosenPuppe.boundary cone ι c hc Z hZ ((R).obj F.obj)))
    (originalSuspendedFiberToQCofiber_equation Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F)
  rw [← Functor.map_comp, QFiberSuspensionToCofiber_boundary] at h
  simpa only [Category.assoc] using h

/-- The complete source Hom test is restriction along the constructed original fiber comparison. -/
def originalSuspendedFiberRestriction (F : (P).FullSubcategory) (E : C)
    (g : (H).obj (c (Q.mapArrow.obj F.obj)).pt ⟶ (H).obj E) :
    (H).obj (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (Q.obj (s F.obj).pt)).pt ⟶
      (H).obj E :=
  (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫ g

/-- Contravariant restriction retains every original whole Arrow map. -/
theorem originalSuspendedFiberRestriction_source {F G : (P).FullSubcategory} (q : F ⟶ G)
    (E : C) (g : (H).obj (c (Q.mapArrow.obj G.obj)).pt ⟶ (H).obj E) :
    originalSuspendedFiberRestriction Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F E
      ((H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc (Q.mapArrow.map q.hom)) ≫ g) =
    (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q.hom))) ≫
      originalSuspendedFiberRestriction Z hZ s hs Q ε hQ hε cone ι c hc hι hCone G E g := by
  change _ ≫ (_ ≫ g) = _ ≫ (_ ≫ g)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun m => m ≫ g)
    (originalSuspendedFiberToQCofiber_naturality Z hZ s hs Q ε hQ hε cone ι c hc hι hCone q).symm

/-- Every whole target map is retained by the same original fiber restriction function. -/
theorem originalSuspendedFiberRestriction_target (F : (P).FullSubcategory) {E E' : C}
    (p : E ⟶ E') (g : (H).obj (c (Q.mapArrow.obj F.obj)).pt ⟶ (H).obj E) :
    originalSuspendedFiberRestriction Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F E'
      (g ≫ (H).map p) =
    originalSuspendedFiberRestriction Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F E g ≫
      (H).map p := by
  exact (Category.assoc _ _ _).symm

variable (t : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (ht : ∀ F, IsLimit (t F))

/-- The entire suspended Q-fiber resolution is natural in both original chosen limit families. -/
theorem resolvedQFiberSuspensionHoIso_choice (F : (P).FullSubcategory) :
    (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
      (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
        (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F.obj).hom)) =
    (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht ((R).obj F.obj)).hom)) ≫
      (resolvedQFiberSuspensionHoIso Z hZ t ht Q ε hQ hε cone ι c hc hι hCone).hom.app F := by
  have hFiber := OrdinaryHoChosenFiberMaps.choiceIso_naturality Z hZ s hs t ht
    (toOriginal Q ε F.obj)
  have h := (H).congr_map ((S).congr_map (Q.congr_map hFiber))
  change (H).map ((S).map (Q.map (OrdinaryHoChosenFiberMaps.chosenMap
    Z hZ s hs (toOriginal Q ε F.obj)))) ≫
      (H).map ((S).map (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F.obj).hom)) =
    (H).map ((S).map (Q.map
      (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht ((R).obj F.obj)).hom)) ≫
      (H).map ((S).map (Q.map (OrdinaryHoChosenFiberMaps.chosenMap
        Z hZ t ht (toOriginal Q ε F.obj))))
  simpa only [Functor.map_comp] using h

/-- The full original suspended-fiber/Q-cofiber comparison retains every caller's limit choice. -/
theorem originalSuspendedFiberToQCofiber_choice (F : (P).FullSubcategory) :
    (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F.obj).hom)) ≫
      (originalSuspendedFiberToQCofiber Z hZ t ht Q ε hQ hε cone ι c hc hι hCone).app F =
    (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F := by
  let A := resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone
  let B := resolvedQFiberSuspensionHoIso Z hZ t ht Q ε hQ hε cone ι c hc hι hCone
  let J := QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone
  let γP := (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
    (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F.obj).hom))
  let γR := (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
    (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht ((R).obj F.obj)).hom))
  let ψA := (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F
  let ψB := (originalSuspendedFiberToQCofiber Z hZ t ht Q ε hQ hε cone ι c hc hι hCone).app F
  have hChoice : A.hom.app F ≫ γP = γR ≫ B.hom.app F :=
    resolvedQFiberSuspensionHoIso_choice Z hZ s hs Q ε hQ hε cone ι c hc hι hCone t ht F
  have hA := originalSuspendedFiberToQCofiber_equation
    Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F
  have hB := originalSuspendedFiberToQCofiber_equation
    Z hZ t ht Q ε hQ hε cone ι c hc hι hCone F
  have hNullChoice := (H).congr_map (QFiberSuspensionToCofiber_choice
    Z hZ s hs Q ε cone ι c hc t ht ((R).obj F.obj))
  change γP ≫ ψB = ψA
  apply (cancel_epi (A.hom.app F)).mp
  apply (cancel_mono (J.hom.app F.obj)).mp
  calc
    (A.hom.app F ≫ (γP ≫ ψB)) ≫ J.hom.app F.obj =
        γR ≫ (B.hom.app F ≫ ψB ≫ J.hom.app F.obj) := by
      rw [← Category.assoc, hChoice]
      simp only [Category.assoc]
    _ = γR ≫ (H).map (QFiberSuspensionToCofiber Z hZ t Q ε cone ι c hc ((R).obj F.obj)) := by
      rw [hB]
    _ = (H).map (QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc ((R).obj F.obj)) := by
      simpa only [Functor.map_comp] using hNullChoice
    _ = (A.hom.app F ≫ ψA) ≫ J.hom.app F.obj := by
      simpa only [Category.assoc] using hA.symm

variable (d : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hd : ∀ F, IsColimit (d F))

omit [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
/-- The entire original Q/corner cofiber zigzag retains both caller-chosen pushout families. -/
theorem QCofiberToResolutionHoIso_cofiberChoice (F : Arrow C) :
    (H).map (cofiberChoiceIso cone ι c hc d hd (Q.mapArrow.obj F)).hom ≫
      (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι d hd hι hCone).hom.app F =
    (QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
      (H).map (cofiberChoiceIso cone ι c hc d hd ((R).obj F)).hom := by
  let A := (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc (intermediateToQ Q ε F))
  let Ad := (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι d hd (intermediateToQ Q ε F))
  let B := (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc
    (intermediateToResolution Q ε F))
  let Bd := (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι d hd
    (intermediateToResolution Q ε F))
  let Jc := QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone
  let Jd := QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι d hd hι hCone
  let γT := (H).map (cofiberChoiceIso cone ι c hc d hd ((T).obj F)).hom
  let γQ := (H).map (cofiberChoiceIso cone ι c hc d hd (Q.mapArrow.obj F)).hom
  let γR := (H).map (cofiberChoiceIso cone ι c hc d hd ((R).obj F)).hom
  let _ : IsIso A := Localization.inverts (H) (weakEquivalences C) _
    (intermediateToQ_cofiber_weak Z hZ Q ε hQ hε cone ι c hc hι hCone F)
  have hChoiceA : A ≫ γQ = γT ≫ Ad := by
    simpa only [Functor.map_comp] using (H).congr_map
      (cofiberChoiceIso_naturality cone ι c hc d hd (intermediateToQ Q ε F))
  have hChoiceB : B ≫ γR = γT ≫ Bd := by
    simpa only [Functor.map_comp] using (H).congr_map
      (cofiberChoiceIso_naturality cone ι c hc d hd (intermediateToResolution Q ε F))
  have hA : A ≫ Jc.hom.app F = B :=
    QCofiberToResolutionHoIso_equation Z hZ Q ε hQ hε cone ι c hc hι hCone F
  have hAd : Ad ≫ Jd.hom.app F = Bd :=
    QCofiberToResolutionHoIso_equation Z hZ Q ε hQ hε cone ι d hd hι hCone F
  change γQ ≫ Jd.hom.app F = Jc.hom.app F ≫ γR
  apply (cancel_epi A).mp
  calc
    A ≫ (γQ ≫ Jd.hom.app F) = (γT ≫ Ad) ≫ Jd.hom.app F := by
      rw [← Category.assoc, hChoiceA]
    _ = γT ≫ Bd := by rw [Category.assoc, hAd]
    _ = B ≫ γR := hChoiceB.symm
    _ = A ≫ (Jc.hom.app F ≫ γR) := by rw [← hA, Category.assoc]

/-- The original suspended-fiber resolution retains the entire choice of its suspension cocones. -/
theorem resolvedQFiberSuspensionHoIso_cofiberChoice (F : (P).FullSubcategory) :
    (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).hom.app F ≫
      (H).map (cofiberChoiceIso cone ι c hc d hd
        (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s F.obj).pt)))).hom =
    (H).map (cofiberChoiceIso cone ι c hc d hd
      (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s ((R).obj F.obj)).pt)))).hom ≫
      (resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι d hd hι hCone).hom.app F := by
  let q := (OrdinaryHoChosenPuppe.zeroArrowFunctor Z hZ).map
    (Q.map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs (toOriginal Q ε F.obj)))
  have h := (H).congr_map (cofiberChoiceIso_naturality cone ι c hc d hd q)
  change (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q) ≫
      (H).map (cofiberChoiceIso cone ι c hc d hd
        (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s F.obj).pt)))).hom =
    (H).map (cofiberChoiceIso cone ι c hc d hd
      (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s ((R).obj F.obj)).pt)))).hom ≫
      (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι d hd q)
  simp only [Functor.map_comp] at h
  exact h

/-- Both original cofiber and suspension choices commute with the entire fiber comparison. -/
theorem originalSuspendedFiberToQCofiber_cofiberChoice (F : (P).FullSubcategory) :
    (H).map (cofiberChoiceIso cone ι c hc d hd
      (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s F.obj).pt)))).hom ≫
      (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι d hd hι hCone).app F =
    (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F ≫
      (H).map (cofiberChoiceIso cone ι c hc d hd (Q.mapArrow.obj F.obj)).hom := by
  let A := resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι c hc hι hCone
  let B := resolvedQFiberSuspensionHoIso Z hZ s hs Q ε hQ hε cone ι d hd hι hCone
  let Jc := QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι c hc hι hCone
  let Jd := QCofiberToResolutionHoIso Z hZ Q ε hQ hε cone ι d hd hι hCone
  let γP := (H).map (cofiberChoiceIso cone ι c hc d hd
    (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s F.obj).pt)))).hom
  let γSr := (H).map (cofiberChoiceIso cone ι c hc d hd
    (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s ((R).obj F.obj)).pt)))).hom
  let γQ := (H).map (cofiberChoiceIso cone ι c hc d hd (Q.mapArrow.obj F.obj)).hom
  let γR := (H).map (cofiberChoiceIso cone ι c hc d hd ((R).obj F.obj)).hom
  let ψc := (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι c hc hι hCone).app F
  let ψd := (originalSuspendedFiberToQCofiber Z hZ s hs Q ε hQ hε cone ι d hd hι hCone).app F
  have hS : A.hom.app F ≫ γP = γSr ≫ B.hom.app F :=
    resolvedQFiberSuspensionHoIso_cofiberChoice
      Z hZ s hs Q ε hQ hε cone ι c hc hι hCone d hd F
  have hJ : γQ ≫ Jd.hom.app F.obj = Jc.hom.app F.obj ≫ γR :=
    QCofiberToResolutionHoIso_cofiberChoice Z hZ Q ε hQ hε cone ι c hc hι hCone d hd F.obj
  have hcEq := originalSuspendedFiberToQCofiber_equation
    Z hZ s hs Q ε hQ hε cone ι c hc hι hCone F
  have hdEq := originalSuspendedFiberToQCofiber_equation
    Z hZ s hs Q ε hQ hε cone ι d hd hι hCone F
  have hNullChoice := (H).congr_map (QFiberSuspensionToCofiber_cofiberChoice
    Z hZ s Q ε cone ι c hc d hd ((R).obj F.obj))
  change γP ≫ ψd = ψc ≫ γQ
  apply (cancel_epi (A.hom.app F)).mp
  apply (cancel_mono (Jd.hom.app F.obj)).mp
  calc
    (A.hom.app F ≫ (γP ≫ ψd)) ≫ Jd.hom.app F.obj =
        γSr ≫ (B.hom.app F ≫ ψd ≫ Jd.hom.app F.obj) := by
      rw [← Category.assoc, hS]
      simp only [Category.assoc]
    _ = γSr ≫ (H).map (QFiberSuspensionToCofiber Z hZ s Q ε cone ι d hd ((R).obj F.obj)) := by
      rw [hdEq]
    _ = (H).map (QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc ((R).obj F.obj)) ≫ γR := by
      simpa only [Functor.map_comp] using hNullChoice
    _ = (A.hom.app F ≫ ψc) ≫ (Jc.hom.app F.obj ≫ γR) := by
      rw [← hcEq]
      simp only [Category.assoc]
      rfl
    _ = (A.hom.app F ≫ (ψc ≫ γQ)) ≫ Jd.hom.app F.obj := by
      rw [← hJ]
      simp only [Category.assoc]

end OriginalJoin

end HomotopicalAlgebra.OrdinaryHoChosenFiberHomSequence
