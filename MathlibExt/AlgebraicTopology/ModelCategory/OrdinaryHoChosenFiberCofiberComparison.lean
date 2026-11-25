/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberMaps
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFiber
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppe
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeRotation

/-!
# Original chosen fibers and their actual cofiber comparison maps

The original zero, chosen fiber carrier, both projections and limit proofs
are retained. The chosen fiber is compared with the functorial homotopy
pullback of its same original cospan; this comparison is weak for a
fibration over a fibrant base.

The strict fiber equation also constructs the full Arrow square from the
fiber-to-zero map to the original input map. Its chosen cofiber map is the
actual suspended-fiber-to-cofiber comparison. Its two legs and full Arrow
naturality are proved. A stable-test equivalence assertion for this latter
map requires the subsequent native source-loop comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryHoChosenFiberCofiberComparison

variable {C : Type u} [Category.{v} C] (Z : C) (hZ : IsZero Z)
  (s : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (hs : ∀ F, IsLimit (s F))

/-- The actual fiber cospan keeps the caller's original zero object.
`canonicalFiberCospanIso` transports this cospan to the canonical fiber API. -/
def fiberDiagram : Arrow C ⥤ (WalkingCospan ⥤ C) where
  obj F := cospan F.hom (hZ.isInitial.to F.right)
  map q := cospanHomMk q.right q.left (𝟙 Z) q.w.symm (by
    exact hZ.isInitial.hom_ext _ _)
  map_id F := by
    ext j
    rcases j with (_ | _ | _) <;> simp
  map_comp q r := by
    ext j
    rcases j with (_ | _ | _) <;> simp

/-- The caller's zero is related to the selected initial object by its actual universal property.
The selected initial object need not be definitionally equal to the caller's zero. -/
def canonicalZeroIso : letI := hZ.hasZeroObject; Z ≅ ⊥_ C := by
  letI := hZ.hasZeroObject
  exact hZ.isInitial.uniqueUpToIso initialIsInitial

/-- The entire original zero-to-target map is recovered through the forward zero Iso. -/
theorem canonicalZeroIso_hom_to (Y : C) :
    letI := hZ.hasZeroObject
    (canonicalZeroIso Z hZ).hom ≫ initial.to Y = hZ.isInitial.to Y := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact hZ.isInitial.hom_ext _ _

/-- The inverse zero Iso recovers the selected initial-to-target map. -/
theorem canonicalZeroIso_inv_to (Y : C) :
    letI := hZ.hasZeroObject
    (canonicalZeroIso Z hZ).inv ≫ hZ.isInitial.to Y = initial.to Y := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact initialIsInitial.hom_ext _ _

/-- Full original cospans are naturally isomorphic to the canonical fiber cospans.
Both nonzero components are identities; the zero component is the actual zero Iso. -/
def canonicalFiberCospanIso :
    letI := hZ.hasZeroObject
    fiberDiagram Z hZ ≅ fiberCospan (C := C) := by
  letI := hZ.hasZeroObject
  refine NatIso.ofComponents (fun F =>
    cospanIsoMk (Iso.refl F.right) (Iso.refl F.left) (canonicalZeroIso Z hZ) ?_ ?_) ?_
  · change F.hom ≫ 𝟙 F.right = 𝟙 F.left ≫ F.hom
    simp
  · change hZ.isInitial.to F.right ≫ 𝟙 F.right =
      (canonicalZeroIso Z hZ).hom ≫ initial.to F.right
    rw [Category.comp_id, canonicalZeroIso_hom_to]
  · intro F G q
    ext j
    rcases j with (_ | _ | _)
    · change q.right ≫ 𝟙 G.right = 𝟙 F.right ≫ q.right
      simp
    · change q.left ≫ 𝟙 G.left = 𝟙 F.left ≫ q.left
      simp
    · change 𝟙 Z ≫ (canonicalZeroIso Z hZ).hom =
        (canonicalZeroIso Z hZ).hom ≫ 𝟙 (⊥_ C)
      simp

/-- The target component of the full cospan comparison is the identity. -/
theorem canonicalFiberCospanIso_hom_one (F : Arrow C) :
    letI := hZ.hasZeroObject
    ((canonicalFiberCospanIso Z hZ).hom.app F).app WalkingCospan.one = 𝟙 F.right := rfl

/-- The source component of the full cospan comparison is the identity. -/
theorem canonicalFiberCospanIso_hom_left (F : Arrow C) :
    letI := hZ.hasZeroObject
    ((canonicalFiberCospanIso Z hZ).hom.app F).app WalkingCospan.left = 𝟙 F.left := rfl

/-- The zero component retains the entire forward map of the original zero Iso. -/
theorem canonicalFiberCospanIso_hom_right (F : Arrow C) :
    letI := hZ.hasZeroObject
    ((canonicalFiberCospanIso Z hZ).hom.app F).app WalkingCospan.right =
      (canonicalZeroIso Z hZ).hom := rfl

/-- The inverse zero component retains the entire inverse of the original zero Iso. -/
theorem canonicalFiberCospanIso_inv_right (F : Arrow C) :
    letI := hZ.hasZeroObject
    ((canonicalFiberCospanIso Z hZ).inv.app F).app WalkingCospan.right =
      (canonicalZeroIso Z hZ).inv := rfl

section Limits

variable [HasLimitsOfShape WalkingCospan C]

/-- The limiting cone is over the same original input arrow and original zero. -/
abbrev ordinaryCone (F : Arrow C) : PullbackCone F.hom (hZ.isInitial.to F.right) :=
  limit.cone ((fiberDiagram Z hZ).obj F)

/-- Its limit proof is the actual selected cospan limit proof. -/
def ordinaryConeIsLimit (F : Arrow C) : IsLimit (ordinaryCone Z hZ F) :=
  limit.isLimit ((fiberDiagram Z hZ).obj F)

/-- Both original projections determine the full given-to-ordinary fiber Iso. -/
def originalToOrdinaryIso (F : Arrow C) : (s F).pt ≅ (ordinaryCone Z hZ F).pt :=
  (hs F).conePointUniqueUpToIso (ordinaryConeIsLimit Z hZ F)

/-- The first endpoint function is the unchanged original first projection. -/
theorem originalToOrdinaryIso_fst (F : Arrow C) :
    (originalToOrdinaryIso Z hZ s hs F).hom ≫ (ordinaryCone Z hZ F).fst = (s F).fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

/-- The zero endpoint function is the unchanged original zero projection. -/
theorem originalToOrdinaryIso_snd (F : Arrow C) :
    (originalToOrdinaryIso Z hZ s hs F).hom ≫ (ordinaryCone Z hZ F).snd = (s F).snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

/-- The inverse retains the entire first projection of the other actual limit. -/
theorem originalToOrdinaryIso_inv_fst (F : Arrow C) :
    (originalToOrdinaryIso Z hZ s hs F).inv ≫ (s F).fst = (ordinaryCone Z hZ F).fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left

/-- The inverse retains the entire original zero endpoint as well. -/
theorem originalToOrdinaryIso_inv_snd (F : Arrow C) :
    (originalToOrdinaryIso Z hZ s hs F).inv ≫ (s F).snd = (ordinaryCone Z hZ F).snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right

/-- Every whole input Arrow square acts on the same original first projection. -/
theorem ordinaryMap_fst {F G : Arrow C} (q : F ⟶ G) :
    lim.map ((fiberDiagram Z hZ).map q) ≫ (ordinaryCone Z hZ G).fst =
      (ordinaryCone Z hZ F).fst ≫ q.left :=
  limMap_π ((fiberDiagram Z hZ).map q) WalkingCospan.left

/-- Every whole input Arrow square preserves the same original zero projection. -/
theorem ordinaryMap_snd {F G : Arrow C} (q : F ⟶ G) :
    lim.map ((fiberDiagram Z hZ).map q) ≫ (ordinaryCone Z hZ G).snd =
      (ordinaryCone Z hZ F).snd := by
  exact (limMap_π ((fiberDiagram Z hZ).map q) WalkingCospan.right).trans
    (Category.comp_id _)

/-- Both projection equations prove naturality of the entire original fiber comparison. -/
theorem originalToOrdinaryIso_naturality {F G : Arrow C} (q : F ⟶ G) :
    OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q ≫
        (originalToOrdinaryIso Z hZ s hs G).hom =
      (originalToOrdinaryIso Z hZ s hs F).hom ≫ lim.map ((fiberDiagram Z hZ).map q) := by
  apply PullbackCone.IsLimit.hom_ext (ordinaryConeIsLimit Z hZ G)
  · rw [Category.assoc, originalToOrdinaryIso_fst,
      OrdinaryHoChosenFiberMaps.chosenMap_fst, Category.assoc, ordinaryMap_fst,
      ← Category.assoc, originalToOrdinaryIso_fst]
  · rw [Category.assoc, originalToOrdinaryIso_snd,
      OrdinaryHoChosenFiberMaps.chosenMap_snd, Category.assoc, ordinaryMap_snd,
      originalToOrdinaryIso_snd]

/-- The original carrier and both projections have a complete natural Iso to its same limit. -/
def originalToOrdinaryNatIso : OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ≅
    fiberDiagram Z hZ ⋙ lim :=
  NatIso.ofComponents (originalToOrdinaryIso Z hZ s hs)
    (originalToOrdinaryIso_naturality Z hZ s hs)

/-- The original selected limits are transported to the canonical ordinary-fiber functor. -/
def ordinaryFiberCanonicalIso :
    letI := hZ.hasZeroObject
    fiberDiagram Z hZ ⋙ lim ≅ ordinaryFiber (C := C) := by
  letI := hZ.hasZeroObject
  exact Functor.isoWhiskerRight (canonicalFiberCospanIso Z hZ) lim

/-- Canonical ordinary-fiber transport preserves the entire original first projection. -/
theorem ordinaryFiberCanonicalIso_hom_fst (F : Arrow C) :
    letI := hZ.hasZeroObject
    (ordinaryFiberCanonicalIso Z hZ).hom.app F ≫
      limit.π ((fiberCospan (C := C)).obj F) WalkingCospan.left =
        (ordinaryCone Z hZ F).fst := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact (limMap_π ((canonicalFiberCospanIso Z hZ).hom.app F) WalkingCospan.left).trans
    (Category.comp_id _)

/-- Canonical ordinary-fiber transport keeps the full original zero projection and zero Iso. -/
theorem ordinaryFiberCanonicalIso_hom_snd (F : Arrow C) :
    letI := hZ.hasZeroObject
    (ordinaryFiberCanonicalIso Z hZ).hom.app F ≫
      limit.π ((fiberCospan (C := C)).obj F) WalkingCospan.right =
        (ordinaryCone Z hZ F).snd ≫ (canonicalZeroIso Z hZ).hom := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact limMap_π ((canonicalFiberCospanIso Z hZ).hom.app F) WalkingCospan.right

/-- The inverse canonical transport recovers the same entire first projection. -/
theorem ordinaryFiberCanonicalIso_inv_fst (F : Arrow C) :
    letI := hZ.hasZeroObject
    (ordinaryFiberCanonicalIso Z hZ).inv.app F ≫ (ordinaryCone Z hZ F).fst =
      limit.π ((fiberCospan (C := C)).obj F) WalkingCospan.left := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact (limMap_π ((canonicalFiberCospanIso Z hZ).inv.app F) WalkingCospan.left).trans
    (Category.comp_id _)

/-- The inverse canonical transport recovers the full original zero projection. -/
theorem ordinaryFiberCanonicalIso_inv_snd (F : Arrow C) :
    letI := hZ.hasZeroObject
    (ordinaryFiberCanonicalIso Z hZ).inv.app F ≫ (ordinaryCone Z hZ F).snd =
      limit.π ((fiberCospan (C := C)).obj F) WalkingCospan.right ≫
        (canonicalZeroIso Z hZ).inv := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  exact limMap_π ((canonicalFiberCospanIso Z hZ).inv.app F) WalkingCospan.right

/-- The full original chosen fibers map to the canonical ordinary fibers
through both actual Isos. -/
def originalToCanonicalOrdinaryNatIso :
    letI := hZ.hasZeroObject
    OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ≅ ordinaryFiber (C := C) := by
  letI := hZ.hasZeroObject
  exact originalToOrdinaryNatIso Z hZ s hs ≪≫ ordinaryFiberCanonicalIso Z hZ

end Limits

section HomotopyFiber

variable [ModelCategory C]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- Functorial homotopy fibers are formed over the caller's unchanged original zero.
`homotopyFiberCanonicalIso` identifies this functor with the canonical homotopy fibers. -/
def originalHomotopyFiber : Arrow C ⥤ C := fiberDiagram Z hZ ⋙ homotopyPullback

/-- The same original homotopy fibers are naturally transported to the canonical fiber API. -/
def homotopyFiberCanonicalIso :
    letI := hZ.hasZeroObject
    originalHomotopyFiber Z hZ ≅ homotopyFiber (C := C) := by
  letI := hZ.hasZeroObject
  exact Functor.isoWhiskerRight (canonicalFiberCospanIso Z hZ) homotopyPullback

/-- The canonical ordinary-to-homotopy comparison is transported through the original zero Isos. -/
def originalToHomotopyFiber : OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⟶
    originalHomotopyFiber Z hZ := by
  letI := hZ.hasZeroObject
  exact (originalToCanonicalOrdinaryNatIso Z hZ s hs).hom ≫
    homotopyFiberComparison ≫ (homotopyFiberCanonicalIso Z hZ).inv

/-- Canonical comparison naturality recovers the whole previous original comparison map. -/
theorem originalToHomotopyFiber_app (F : Arrow C) :
    (originalToHomotopyFiber Z hZ s hs).app F =
      (originalToOrdinaryIso Z hZ s hs F).hom ≫
        homotopyPullbackComparison.app ((fiberDiagram Z hZ).obj F) := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  let e := (canonicalFiberCospanIso Z hZ).app F
  change ((originalToOrdinaryIso Z hZ s hs F).hom ≫ lim.map e.hom) ≫
      (homotopyPullbackComparison.app ((fiberCospan (C := C)).obj F) ≫
        homotopyPullback.map e.inv) = _
  have h := homotopyPullbackComparison.naturality e.hom
  rw [Category.assoc, ← Category.assoc (lim.map e.hom)
      (homotopyPullbackComparison.app ((fiberCospan (C := C)).obj F))
      (homotopyPullback.map e.inv), h, Category.assoc, ← homotopyPullback.map_comp,
    e.hom_inv_id, homotopyPullback.map_id, Category.comp_id]

/-- Every original Arrow square commutes with the entire original-to-homotopy fiber map. -/
theorem originalToHomotopyFiber_naturality {F G : Arrow C} (q : F ⟶ G) :
    OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q ≫
        (originalToHomotopyFiber Z hZ s hs).app G =
      (originalToHomotopyFiber Z hZ s hs).app F ≫
        (originalHomotopyFiber Z hZ).map q :=
  (originalToHomotopyFiber Z hZ s hs).naturality q

/-- Fibrations over fibrant bases give a genuinely weak comparison from the same original fiber. -/
theorem originalToHomotopyFiber_weak (F : Arrow C) [Fibration F.hom] [IsFibrant F.right] :
    weakEquivalences C ((originalToHomotopyFiber Z hZ s hs).app F) := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  have h := weakEquivalence_homotopyFiberComparison_of_fibration_fibrant F
  change weakEquivalences C ((originalToCanonicalOrdinaryNatIso Z hZ s hs).hom.app F ≫
    ((homotopyFiberComparison (C := C)).app F ≫ (homotopyFiberCanonicalIso Z hZ).inv.app F))
  exact (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences _)
    ((weakEquivalences C).comp_mem _ _ h.mem (mem_weakEquivalences _))

/-- The complete original fiber comparison preserves weak equivalences on both Arrow endpoints. -/
theorem originalHomotopyFiber_map_weak {F G : Arrow C} (q : F ⟶ G)
    [WeakEquivalence q.left] [WeakEquivalence q.right] :
    weakEquivalences C ((originalHomotopyFiber Z hZ).map q) := by
  let _ : HasZeroObject C := hZ.hasZeroObject
  let e := homotopyFiberCanonicalIso Z hZ
  have h := homotopyFiber_map_weakEquivalence q inferInstance inferInstance
  apply (weakEquivalences C).of_postcomp _ _ (mem_weakEquivalences (e.hom.app G))
  rw [e.hom.naturality q]
  exact (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences (e.hom.app F)) h.mem

/-- Two actual fibration fibers are weakly related by the entire original chosen-fiber Arrow map. -/
theorem originalChosenMap_weak {F G : Arrow C} (q : F ⟶ G)
    [Fibration F.hom] [Fibration G.hom] [IsFibrant F.right] [IsFibrant G.right]
    [WeakEquivalence q.left] [WeakEquivalence q.right] :
    weakEquivalences C (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q) := by
  have hF := originalToHomotopyFiber_weak Z hZ s hs F
  have hG := originalToHomotopyFiber_weak Z hZ s hs G
  have hq := originalHomotopyFiber_map_weak Z hZ q
  apply (weakEquivalences C).of_postcomp _ _ hG
  rw [originalToHomotopyFiber_naturality]
  exact (weakEquivalences C).comp_mem _ _ hF hq

end HomotopyFiber

section Cofiber

variable (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

/-- The original fiber equation constructs the actual fiber-to-zero/input Arrow square. -/
def fiberNullSquare (F : Arrow C) :
    Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (s F).pt) ⟶ F :=
  Arrow.homMk (s F).fst (hZ.isInitial.to F.right) (by
    change (s F).fst ≫ F.hom = hZ.isTerminal.from (s F).pt ≫ hZ.isInitial.to F.right
    exact (s F).condition.trans
      (congrArg (fun m => m ≫ hZ.isInitial.to F.right) (hZ.isTerminal.hom_ext _ _)))

/-- The entire square is natural on both components of every original input Arrow. -/
def fiberNullSquareNatTrans :
    OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙
      OrdinaryHoChosenPuppe.zeroArrowFunctor Z hZ ⟶ 𝟭 (Arrow C) where
  app F := fiberNullSquare Z hZ s F
  naturality F G q := by
    apply Arrow.hom_ext
    · exact OrdinaryHoChosenFiberMaps.chosenMap_fst Z hZ s hs q
    · exact hZ.isInitial.hom_ext _ _

/-- The suspended original fiber maps to the original cofiber by the same chosen cofiber functor. -/
def suspensionToCofiber (F : Arrow C) :
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (s F).pt).pt ⟶ (c F).pt :=
  OrdinaryHoChosenPuppe.cofiberMap cone ι c hc (fiberNullSquare Z hZ s F)

/-- Its whole cone leg is the original cone map of the original first fiber projection. -/
theorem suspensionToCofiber_cone (F : Arrow C) :
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (s F).pt).inl ≫
        suspensionToCofiber Z hZ s cone ι c hc F =
      cone.map (s F).fst ≫ (c F).inl :=
  OrdinaryHoChosenPuppe.cofiberMap_cone cone ι c hc (fiberNullSquare Z hZ s F)

/-- Its whole zero leg is the original zero-to-target map and original second cofiber leg. -/
theorem suspensionToCofiber_zero (F : Arrow C) :
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (s F).pt).inr ≫
        suspensionToCofiber Z hZ s cone ι c hc F =
      hZ.isInitial.to F.right ≫ (c F).inr :=
  OrdinaryHoChosenPuppe.cofiberMap_target cone ι c hc (fiberNullSquare Z hZ s F)

/-- The same actual suspended-fiber comparison is natural on every whole original Arrow square. -/
def suspensionToCofiberNatTrans :
    OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙
      OrdinaryHoChosenPuppe.suspensionFunctor cone ι c hc Z hZ ⟶
        OrdinaryHoChosenPuppe.cofiberFunctor cone ι c hc :=
  Functor.whiskerRight (fiberNullSquareNatTrans Z hZ s hs)
    (OrdinaryHoChosenPuppe.cofiberFunctor cone ι c hc)

/-- Every full source square is retained in the suspended original fiber/cofiber equation. -/
theorem suspensionToCofiber_naturality {F G : Arrow C} (q : F ⟶ G) :
    OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
        (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q) ≫
          suspensionToCofiber Z hZ s cone ι c hc G =
      suspensionToCofiber Z hZ s cone ι c hc F ≫
        OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q :=
  (suspensionToCofiberNatTrans Z hZ s hs cone ι c hc).naturality q

end Cofiber

section CofiberChoices

variable (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))
  (d : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hd : ∀ F, IsColimit (d F))

/-- Both original cofiber legs construct the full Iso between the actual chosen pushouts. -/
def cofiberChoiceIso (F : Arrow C) : (c F).pt ≅ (d F).pt :=
  (hc F).coconePointUniqueUpToIso (hd F)

/-- The complete forward cofiber function retains the caller's original cone leg. -/
theorem cofiberChoiceIso_hom_cone (F : Arrow C) :
    (c F).inl ≫ (cofiberChoiceIso cone ι c hc d hd F).hom = (d F).inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingSpan.left

/-- The complete forward cofiber function retains the original target leg. -/
theorem cofiberChoiceIso_hom_target (F : Arrow C) :
    (c F).inr ≫ (cofiberChoiceIso cone ι c hc d hd F).hom = (d F).inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingSpan.right

/-- The inverse cofiber function recovers the same full original cone leg. -/
theorem cofiberChoiceIso_inv_cone (F : Arrow C) :
    (d F).inl ≫ (cofiberChoiceIso cone ι c hc d hd F).inv = (c F).inl :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ WalkingSpan.left

/-- The inverse cofiber function recovers the same full original target leg. -/
theorem cofiberChoiceIso_inv_target (F : Arrow C) :
    (d F).inr ≫ (cofiberChoiceIso cone ι c hc d hd F).inv = (c F).inr :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ WalkingSpan.right

/-- Both chosen pushout legs retain full naturality on every original whole Arrow square. -/
theorem cofiberChoiceIso_naturality {F G : Arrow C} (q : F ⟶ G) :
    OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q ≫
      (cofiberChoiceIso cone ι c hc d hd G).hom =
    (cofiberChoiceIso cone ι c hc d hd F).hom ≫
      OrdinaryHoChosenPuppe.cofiberMap cone ι d hd q := by
  apply PushoutCocone.IsColimit.hom_ext (hc F)
  · rw [← Category.assoc, OrdinaryHoChosenPuppe.cofiberMap_cone, Category.assoc,
      cofiberChoiceIso_hom_cone, ← Category.assoc, cofiberChoiceIso_hom_cone,
      OrdinaryHoChosenPuppe.cofiberMap_cone]
  · rw [← Category.assoc, OrdinaryHoChosenPuppe.cofiberMap_target, Category.assoc,
      cofiberChoiceIso_hom_target, ← Category.assoc, cofiberChoiceIso_hom_target,
      OrdinaryHoChosenPuppe.cofiberMap_target]

/-- The full original chosen cofiber functors retain all their actual choice functions. -/
def cofiberChoiceNatIso : OrdinaryHoChosenPuppe.cofiberFunctor cone ι c hc ≅
    OrdinaryHoChosenPuppe.cofiberFunctor cone ι d hd :=
  NatIso.ofComponents (cofiberChoiceIso cone ι c hc d hd)
    (cofiberChoiceIso_naturality cone ι c hc d hd)

/-- Both original suspension legs are transported by the same actual chosen pushout Iso. -/
def suspensionChoiceNatIso : OrdinaryHoChosenPuppe.suspensionFunctor cone ι c hc Z hZ ≅
    OrdinaryHoChosenPuppe.suspensionFunctor cone ι d hd Z hZ :=
  Functor.isoWhiskerLeft (OrdinaryHoChosenPuppe.zeroArrowFunctor Z hZ)
    (cofiberChoiceNatIso cone ι c hc d hd)

/-- The complete original boundary retains the same choice transport on cofiber and suspension. -/
theorem boundary_cofiberChoice (F : Arrow C) :
    (cofiberChoiceIso cone ι c hc d hd F).hom ≫
      OrdinaryHoChosenPuppe.boundary cone ι d hd Z hZ F =
    OrdinaryHoChosenPuppe.boundary cone ι c hc Z hZ F ≫
      (cofiberChoiceIso cone ι c hc d hd
        (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ F.left))).hom := by
  apply PushoutCocone.IsColimit.hom_ext (hc F)
  · rw [← Category.assoc, cofiberChoiceIso_hom_cone, OrdinaryHoChosenPuppe.boundary_cone,
      ← Category.assoc, OrdinaryHoChosenPuppe.boundary_cone, cofiberChoiceIso_hom_cone]
  · rw [← Category.assoc, cofiberChoiceIso_hom_target, OrdinaryHoChosenPuppe.boundary_target,
      ← Category.assoc, OrdinaryHoChosenPuppe.boundary_target, Category.assoc,
      cofiberChoiceIso_hom_target]

end CofiberChoices

section CofibrantCofiber

variable [ModelCategory C]
  (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

/-- The whole original chosen cofiber map is weak by cofibrant gluing of its two actual legs.
Weakness of the cone component follows from the two original cone contractions. -/
theorem chosenCofiberMap_weak {F G : Arrow C} (q : F ⟶ G)
    [IsCofibrant F.left] [IsCofibrant G.left]
    [IsCofibrant F.right] [IsCofibrant G.right]
    [Cofibration (ι.app F.left)] [Cofibration (ι.app G.left)]
    [WeakEquivalence q.left] [WeakEquivalence q.right]
    (hF : weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.left)))
    (hG : weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj G.left))) :
    weakEquivalences C (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q) := by
  let _ : WeakEquivalence (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.left)) :=
    (weakEquivalence_iff _).mpr hF
  let _ : WeakEquivalence (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj G.left)) :=
    (weakEquivalence_iff _).mpr hG
  let _ : WeakEquivalence (cone.map q.left) :=
    weakEquivalence_of_postcomp_of_fac (OrdinaryHoChosenPuppe.toZero_comp Z hZ (cone.map q.left))
  apply (weakEquivalence_iff _).mp
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (A := F.left) (A' := G.left) (X := F.right) (X' := G.right)
    (IsPushout.of_isColimit (hc F)) (IsPushout.of_isColimit (hc G))
    (a := q.left) (b := cone.map q.left) (c := q.right)
    (ι.naturality q.left).symm q.w.symm
    (OrdinaryHoChosenPuppe.cofiberMap_cone cone ι c hc q)
    (OrdinaryHoChosenPuppe.cofiberMap_target cone ι c hc q)

end CofibrantCofiber

section SuspendedCoefficientLift

variable [ModelCategory C]
  (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

local notation "H" => (MorphismProperty.Q (weakEquivalences C))

/-- An actual null coefficient map extends over its original cone by a good-path lift. -/
theorem coneExtension_of_null {K E : C} [IsCofibrant K] [IsFibrant E]
    [Cofibration (ι.app K)] (f : K ⟶ E)
    (hf : (H).map f = (H).map (OrdinaryHoChosenPuppe.nullMap Z hZ K E)) :
    ∃ h : cone.obj K ⟶ E, ι.app K ≫ h = f := by
  have hRel : RightHomotopyRel f (OrdinaryHoChosenPuppe.nullMap Z hZ K E) := by
    rw [RightHomotopyRel.iff_map_eq (H)]
    exact hf
  obtain ⟨P, hP, ⟨T⟩⟩ := hRel.exists_good_pathObject
  let _ : P.IsGood := hP
  have hZero : ι.app K ≫ OrdinaryHoChosenPuppe.nullMap Z hZ (cone.obj K) E =
      OrdinaryHoChosenPuppe.nullMap Z hZ K E := by
    rw [OrdinaryHoChosenPuppe.nullMap, ← Category.assoc,
      OrdinaryHoChosenPuppe.toZero_comp]
    rfl
  let sq : CommSq T.h (ι.app K) P.p₁
      (OrdinaryHoChosenPuppe.nullMap Z hZ (cone.obj K) E) :=
    ⟨T.h₁.trans hZero.symm⟩
  refine ⟨sq.lift ≫ P.p₀, ?_⟩
  rw [← Category.assoc, sq.fac_left, T.h₀]

/-- The original coefficient extension constructs the whole square into the cofiber inclusion. -/
def coneToCofiberSquare (F : Arrow C) (K : C) (g : K ⟶ F.right)
    (h : cone.obj K ⟶ (c F).pt) (hh : ι.app K ≫ h = g ≫ (c F).inr) :
    Arrow.mk (ι.app K) ⟶ OrdinaryHoChosenPuppeRotation.targetArrow cone ι c F :=
  Arrow.homMk g h hh.symm

/-- A null original coefficient has a suspended lift through the actual original source arrow.
The construction keeps the two weak double-cone collapses and their reversal. -/
theorem suspendedCoefficientLift_of_null
    (F : Arrow C) (K : C) (g : K ⟶ F.right)
    [IsCofibrant K] [IsCofibrant F.right] [IsFibrant (c F).pt]
    [Cofibration (ι.app K)] [Cofibration (ι.app F.right)]
    (hK : weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj K)))
    (hY : weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.right)))
    (hg : (H).map (g ≫ (c F).inr) =
      (H).map (OrdinaryHoChosenPuppe.nullMap Z hZ K (c F).pt)) :
    ∃ k : (H).obj (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ K).pt ⟶
        (H).obj (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ F.left).pt,
      k ≫ (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ F.hom) =
        (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ g) := by
  obtain ⟨h, hh⟩ := coneExtension_of_null Z hZ cone ι (g ≫ (c F).inr) hg
  let q := coneToCofiberSquare cone ι c F K g h hh
  let A := (H).map (OrdinaryHoChosenPuppeRotation.collapseRight cone ι c hc Z hZ K)
  let _ : IsIso A := Localization.inverts (H) (weakEquivalences C) _
    (OrdinaryHoChosenPuppeRotation.collapseRight_weak cone ι c hc Z hZ K hK)
  let rK := OrdinaryHoChosenPuppeRotation.suspensionReversal cone ι c hc Z hZ K hK
  let rY := OrdinaryHoChosenPuppeRotation.suspensionReversal cone ι c hc Z hZ F.right hY
  let u := inv A ≫ (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q) ≫
    (H).map (OrdinaryHoChosenPuppeRotation.rotationComparison cone ι c hc Z hZ F)
  have hBoundary :
      (H).map (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q) ≫
        (H).map (OrdinaryHoChosenPuppe.boundary cone ι c hc Z hZ
          (OrdinaryHoChosenPuppeRotation.targetArrow cone ι c F)) =
      A ≫ (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ g) := by
    have hNat := (H).congr_map
      (OrdinaryHoChosenPuppe.boundary_naturality cone ι c hc Z hZ q)
    simp only [Functor.map_comp] at hNat
    exact hNat
  have hRot := OrdinaryHoChosenPuppeRotation.rotationComparison_boundary
    cone ι c hc Z hZ F hY
  have hReversalY : rY.hom ≫ rY.hom = 𝟙 _ :=
    OrdinaryHoChosenPuppeRotation.suspensionReversal_involutive cone ι c hc Z hZ F.right hY
  have hUg : u ≫ (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ F.hom) ≫
      rY.hom = (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ g) := by
    change (inv A ≫ _ ≫ _) ≫ _ ≫ rY.hom = _
    simp only [Category.assoc]
    rw [hRot, hBoundary]
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hU : u ≫ (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ F.hom) =
      (H).map (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ g) ≫ rY.hom := by
    apply (cancel_mono rY.hom).mp
    simp only [Category.assoc]
    rw [hReversalY, Category.comp_id]
    exact hUg
  refine ⟨rK.hom ≫ u, ?_⟩
  rw [Category.assoc, hU, ← Category.assoc,
    ← OrdinaryHoChosenPuppeRotation.suspensionReversal_naturality cone ι c hc Z hZ g hK hY,
    Category.assoc, hReversalY, Category.comp_id]

end SuspendedCoefficientLift

namespace ArrowResolution

variable [ModelCategory C] (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C)
  (hQ : ∀ X : C, IsCofibrant (Q.obj X))
  (hε : ∀ X : C, trivialFibrations C (ε.app X))

/-- The original target counit is pulled back along the unchanged caller arrow. -/
abbrev corner (F : Arrow C) := pullback F.hom (ε.app F.right)

/-- The entire original Arrow square gives the map of actual counit pullbacks. -/
def cornerMap {F G : Arrow C} (q : F ⟶ G) : corner Q ε F ⟶ corner Q ε G :=
  pullback.map F.hom (ε.app F.right) G.hom (ε.app G.right)
    q.left (Q.map q.right) q.right q.w.symm (ε.naturality q.right).symm

/-- The corner retains the original source component of every Arrow map. -/
theorem cornerMap_fst {F G : Arrow C} (q : F ⟶ G) :
    cornerMap Q ε q ≫ pullback.fst G.hom (ε.app G.right) =
      pullback.fst F.hom (ε.app F.right) ≫ q.left :=
  pullback.lift_fst _ _ _

/-- The corner retains the original Q map of the target component. -/
theorem cornerMap_snd {F G : Arrow C} (q : F ⟶ G) :
    cornerMap Q ε q ≫ pullback.snd G.hom (ε.app G.right) =
      pullback.snd F.hom (ε.app F.right) ≫ Q.map q.right :=
  pullback.lift_snd _ _ _

/-- The actual original target-counit corners form a complete functor on all Arrows. -/
def cornerFunctor : Arrow C ⥤ C where
  obj F := corner Q ε F
  map q := cornerMap Q ε q
  map_id F := by
    apply pullback.hom_ext <;> simp [cornerMap]
  map_comp q r := by
    apply pullback.hom_ext
    · rw [cornerMap_fst, Category.assoc, cornerMap_fst,
        ← Category.assoc, cornerMap_fst]
      exact (Category.assoc _ _ _).symm
    · rw [cornerMap_snd, Category.assoc, cornerMap_snd,
        ← Category.assoc, cornerMap_snd]
      change _ ≫ Q.map (q.right ≫ r.right) = _
      rw [Q.map_comp, Category.assoc]

/-- The original Q source maps to the actual corner by the two original counit functions. -/
def sourceToCorner (F : Arrow C) : Q.obj F.left ⟶ corner Q ε F :=
  pullback.lift (ε.app F.left) (Q.map F.hom) (ε.naturality F.hom).symm

/-- Its first whole component is the same original source counit. -/
theorem sourceToCorner_fst (F : Arrow C) :
    sourceToCorner Q ε F ≫ pullback.fst F.hom (ε.app F.right) = ε.app F.left :=
  pullback.lift_fst _ _ _

/-- Its second whole component is the unchanged original Q arrow. -/
theorem sourceToCorner_snd (F : Arrow C) :
    sourceToCorner Q ε F ≫ pullback.snd F.hom (ε.app F.right) = Q.map F.hom :=
  pullback.lift_snd _ _ _

/-- Both actual corner components prove full source-to-corner naturality. -/
theorem sourceToCorner_naturality {F G : Arrow C} (q : F ⟶ G) :
    Q.map q.left ≫ sourceToCorner Q ε G = sourceToCorner Q ε F ≫ cornerMap Q ε q := by
  apply pullback.hom_ext
  · rw [Category.assoc, sourceToCorner_fst, Category.assoc, cornerMap_fst,
      ← Category.assoc, sourceToCorner_fst]
    exact ε.naturality q.left
  · rw [Category.assoc, sourceToCorner_snd, Category.assoc, cornerMap_snd,
      ← Category.assoc, sourceToCorner_snd, ← Q.map_comp, ← Q.map_comp, q.w]

include hε in
/-- The original corner-to-source function is a trivial fibration by actual base change. -/
theorem corner_fst_trivialFibration (F : Arrow C) :
    trivialFibrations C (pullback.fst F.hom (ε.app F.right)) :=
  (trivialFibrations C).of_isPullback (IsPullback.of_hasPullback _ _).flip (hε F.right)

include hε in
/-- The entire original source-to-corner map is weak by its actual source counit equation. -/
theorem sourceToCorner_weak (F : Arrow C) : weakEquivalences C (sourceToCorner Q ε F) := by
  apply (weakEquivalences C).of_postcomp _ _ (corner_fst_trivialFibration Q ε hε F).2
  rw [sourceToCorner_fst]
  exact (hε F.left).2

/-- The same original Q applied to the actual corner supplies the cofibrant source. -/
def resolvedMap (F : Arrow C) : Q.obj (corner Q ε F) ⟶ Q.obj F.right :=
  ε.app (corner Q ε F) ≫ pullback.snd F.hom (ε.app F.right)

/-- The complete original Q/corner construction gives the full resolved Arrow functor. -/
def resolutionFunctor : Arrow C ⥤ Arrow C where
  obj F := Arrow.mk (resolvedMap Q ε F)
  map q := Arrow.homMk (Q.map (cornerMap Q ε q)) (Q.map q.right) (by
    change Q.map (cornerMap Q ε q) ≫
        (ε.app (corner Q ε _) ≫ pullback.snd _ _) =
      (ε.app (corner Q ε _) ≫ pullback.snd _ _) ≫ Q.map q.right
    rw [← Category.assoc, ε.naturality, Functor.id_map,
      Category.assoc, cornerMap_snd, Category.assoc])
  map_id F := by
    apply Arrow.hom_ext
    · change Q.map (cornerMap Q ε (𝟙 F)) = 𝟙 (Q.obj (corner Q ε F))
      rw [show cornerMap Q ε (𝟙 F) = 𝟙 _ from (cornerFunctor Q ε).map_id F, Q.map_id]
    · change Q.map (𝟙 F.right) = 𝟙 (Q.obj F.right)
      exact Q.map_id F.right
  map_comp q r := by
    apply Arrow.hom_ext
    · change Q.map (cornerMap Q ε (q ≫ r)) = Q.map (cornerMap Q ε q) ≫ Q.map (cornerMap Q ε r)
      rw [show cornerMap Q ε (q ≫ r) = cornerMap Q ε q ≫ cornerMap Q ε r from
        (cornerFunctor Q ε).map_comp q r, Q.map_comp]
    · change Q.map (q.right ≫ r.right) = Q.map q.right ≫ Q.map r.right
      exact Q.map_comp q.right r.right

/-- Both original projections define the whole resolved-to-original Arrow comparison. -/
def toOriginal (F : Arrow C) : (resolutionFunctor Q ε).obj F ⟶ F :=
  Arrow.homMk
    (ε.app (corner Q ε F) ≫ pullback.fst F.hom (ε.app F.right))
    (ε.app F.right) (by
      change (ε.app _ ≫ pullback.fst _ _) ≫ F.hom = resolvedMap Q ε F ≫ ε.app F.right
      rw [Category.assoc, pullback.condition]
      change ε.app (corner Q ε F) ≫
        (pullback.snd F.hom (ε.app F.right) ≫ ε.app F.right) =
        (ε.app (corner Q ε F) ≫ pullback.snd F.hom (ε.app F.right)) ≫ ε.app F.right
      exact (Category.assoc _ _ _).symm)

/-- The complete original comparison is natural on every source and target component. -/
def toOriginalNatTrans : resolutionFunctor Q ε ⟶ 𝟭 (Arrow C) where
  app F := toOriginal Q ε F
  naturality F G q := by
    apply Arrow.hom_ext
    · change Q.map (cornerMap Q ε q) ≫
        (ε.app _ ≫ pullback.fst _ _) = (ε.app _ ≫ pullback.fst _ _) ≫ q.left
      rw [← Category.assoc, ε.naturality, Functor.id_map,
        Category.assoc, cornerMap_fst, Category.assoc]
      rfl
    · exact ε.naturality q.right

include hQ in
/-- Both complete resolved Arrow endpoints are cofibrant under the same original Q. -/
theorem resolution_cofibrant (F : Arrow C) :
    IsCofibrant ((resolutionFunctor Q ε).obj F).left ∧
      IsCofibrant ((resolutionFunctor Q ε).obj F).right :=
  ⟨hQ (corner Q ε F), hQ F.right⟩

include hε in
/-- The actual resolved map remains a fibration when the original map is a fibration. -/
theorem resolvedMap_fibration (F : Arrow C) [Fibration F.hom] :
    Fibration (resolvedMap Q ε F) := by
  let _ : Fibration (ε.app (corner Q ε F)) :=
    (mem_trivialFibrations_iff _).mp (hε (corner Q ε F)) |>.1
  let _ : Fibration (pullback.snd F.hom (ε.app F.right)) := by
    rw [fibration_iff]
    exact (fibrations C).of_isPullback (IsPullback.of_hasPullback _ _)
      (mem_fibrations F.hom)
  unfold resolvedMap
  infer_instance

include hε in
/-- Both entire resolved-to-original Arrow components are actual trivial fibrations. -/
theorem toOriginal_trivialFibrations (F : Arrow C) :
    trivialFibrations C (toOriginal Q ε F).left ∧
      trivialFibrations C (toOriginal Q ε F).right := by
  refine ⟨?_, hε F.right⟩
  exact (trivialFibrations C).comp_mem _ _ (hε (corner Q ε F))
    (corner_fst_trivialFibration Q ε hε F)

include hε in
/-- The same original Q preserves weak maps by its original counit naturality. -/
theorem Q_map_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C (Q.map f) := by
  apply (weakEquivalences C).of_postcomp _ _ (hε Y).2
  rw [ε.naturality f, Functor.id_map]
  exact (weakEquivalences C).comp_mem _ _ (hε X).2 hf

/-- The common actual Q-source resolution of the original Q arrow and corner arrow. -/
def intermediateMap (F : Arrow C) : Q.obj (Q.obj F.left) ⟶ Q.obj F.right :=
  ε.app (Q.obj F.left) ≫ Q.map F.hom

/-- Every entire source Arrow acts on the same common Q-source resolution. -/
def intermediateFunctor : Arrow C ⥤ Arrow C where
  obj F := Arrow.mk (intermediateMap Q ε F)
  map q := Arrow.homMk (Q.map (Q.map q.left)) (Q.map q.right) (by
    change Q.map (Q.map q.left) ≫ (ε.app _ ≫ Q.map _) =
      (ε.app _ ≫ Q.map _) ≫ Q.map q.right
    rw [← Category.assoc, ε.naturality, Functor.id_map, Category.assoc,
      ← Q.map_comp, q.w, Q.map_comp, Category.assoc])
  map_id F := by
    apply Arrow.hom_ext
    · change Q.map (Q.map (𝟙 F.left)) = 𝟙 _
      rw [Q.map_id, Q.map_id]
    · change Q.map (𝟙 F.right) = 𝟙 _
      exact Q.map_id F.right
  map_comp q r := by
    apply Arrow.hom_ext
    · change Q.map (Q.map (q.left ≫ r.left)) = _
      rw [Q.map_comp, Q.map_comp]
      rfl
    · change Q.map (q.right ≫ r.right) = _
      exact Q.map_comp q.right r.right

/-- The entire common resolution maps to the original Q arrow by its actual Q-source counit. -/
def intermediateToQ (F : Arrow C) :
    (intermediateFunctor Q ε).obj F ⟶ Q.mapArrow.obj F :=
  Arrow.homMk (ε.app (Q.obj F.left)) (𝟙 (Q.obj F.right)) (by
    change ε.app (Q.obj F.left) ≫ Q.map F.hom = intermediateMap Q ε F ≫ 𝟙 _
    exact (Category.comp_id _).symm)

/-- Both endpoint functions are retained by the full common-to-Q natural transformation. -/
def intermediateToQNatTrans : intermediateFunctor Q ε ⟶ Q.mapArrow where
  app F := intermediateToQ Q ε F
  naturality F G q := by
    apply Arrow.hom_ext
    · exact ε.naturality (Q.map q.left)
    · change Q.map q.right ≫ 𝟙 _ = 𝟙 _ ≫ Q.map q.right
      simp

/-- The same common resolution maps to the actual corner resolution by Q of its original lift. -/
def intermediateToResolution (F : Arrow C) :
    (intermediateFunctor Q ε).obj F ⟶ (resolutionFunctor Q ε).obj F :=
  Arrow.homMk (Q.map (sourceToCorner Q ε F)) (𝟙 (Q.obj F.right)) (by
    change Q.map (sourceToCorner Q ε F) ≫
      (ε.app (corner Q ε F) ≫ pullback.snd _ _) = intermediateMap Q ε F ≫ 𝟙 _
    rw [← Category.assoc, ε.naturality, Functor.id_map, Category.assoc,
      sourceToCorner_snd, Category.comp_id]
    rfl)

/-- The two actual corner projection laws retain naturality on both common-resolution endpoints. -/
def intermediateToResolutionNatTrans :
    intermediateFunctor Q ε ⟶ resolutionFunctor Q ε where
  app F := intermediateToResolution Q ε F
  naturality F G q := by
    apply Arrow.hom_ext
    · change Q.map (Q.map q.left) ≫ Q.map (sourceToCorner Q ε G) =
        Q.map (sourceToCorner Q ε F) ≫ Q.map (cornerMap Q ε q)
      rw [← Q.map_comp, sourceToCorner_naturality, Q.map_comp]
    · change Q.map q.right ≫ 𝟙 _ = 𝟙 _ ≫ Q.map q.right
      simp

include hQ in
/-- Both original common-resolution endpoints are cofibrant under the unchanged Q. -/
theorem intermediate_cofibrant (F : Arrow C) :
    IsCofibrant ((intermediateFunctor Q ε).obj F).left ∧
      IsCofibrant ((intermediateFunctor Q ε).obj F).right :=
  ⟨hQ (Q.obj F.left), hQ F.right⟩

include hε in
/-- Both whole common-to-Q Arrow endpoint functions are genuinely weak. -/
theorem intermediateToQ_weak (F : Arrow C) :
    weakEquivalences C (intermediateToQ Q ε F).left ∧
      weakEquivalences C (intermediateToQ Q ε F).right :=
  ⟨(hε (Q.obj F.left)).2, mem_weakEquivalences (𝟙 (Q.obj F.right))⟩

include hε in
/-- Both whole common-to-corner Arrow endpoint functions are weak by the actual corner lift. -/
theorem intermediateToResolution_weak (F : Arrow C) :
    weakEquivalences C (intermediateToResolution Q ε F).left ∧
      weakEquivalences C (intermediateToResolution Q ε F).right :=
  ⟨Q_map_weak Q ε hε _ (sourceToCorner_weak Q ε hε F),
    mem_weakEquivalences (𝟙 (Q.obj F.right))⟩

section ChosenCofibers

variable (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))
  (hι : ∀ X : C, IsCofibrant X → cofibrations C (ι.app X))
  (hCone : ∀ X : C, IsCofibrant X →
    weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj X)))

include hQ hε hι hCone in
/-- The first original chosen-cofiber zigzag leg is weak on its literal actual carriers. -/
theorem intermediateToQ_cofiber_weak (F : Arrow C) :
    weakEquivalences C (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc
      (intermediateToQ Q ε F)) := by
  let _ : IsCofibrant ((intermediateFunctor Q ε).obj F).left := hQ (Q.obj F.left)
  let _ : IsCofibrant (Q.mapArrow.obj F).left := hQ F.left
  let _ : IsCofibrant ((intermediateFunctor Q ε).obj F).right := hQ F.right
  let _ : IsCofibrant (Q.mapArrow.obj F).right := hQ F.right
  let _ : Cofibration (ι.app ((intermediateFunctor Q ε).obj F).left) :=
    (cofibration_iff _).mpr (hι _ inferInstance)
  let _ : Cofibration (ι.app (Q.mapArrow.obj F).left) :=
    (cofibration_iff _).mpr (hι _ inferInstance)
  let _ : WeakEquivalence (intermediateToQ Q ε F).left :=
    (weakEquivalence_iff _).mpr (intermediateToQ_weak Q ε hε F).1
  let _ : WeakEquivalence (intermediateToQ Q ε F).right :=
    (weakEquivalence_iff _).mpr (intermediateToQ_weak Q ε hε F).2
  exact chosenCofiberMap_weak Z hZ cone ι c hc (intermediateToQ Q ε F)
    (hCone _ inferInstance) (hCone _ inferInstance)

include hQ hε hι hCone in
/-- The second original chosen-cofiber zigzag leg is weak by the actual Q corner lift. -/
theorem intermediateToResolution_cofiber_weak (F : Arrow C) :
    weakEquivalences C (OrdinaryHoChosenPuppe.cofiberMap cone ι c hc
      (intermediateToResolution Q ε F)) := by
  let _ : IsCofibrant ((intermediateFunctor Q ε).obj F).left := hQ (Q.obj F.left)
  let _ : IsCofibrant ((resolutionFunctor Q ε).obj F).left := hQ (corner Q ε F)
  let _ : IsCofibrant ((intermediateFunctor Q ε).obj F).right := hQ F.right
  let _ : IsCofibrant ((resolutionFunctor Q ε).obj F).right := hQ F.right
  let _ : Cofibration (ι.app ((intermediateFunctor Q ε).obj F).left) :=
    (cofibration_iff _).mpr (hι _ inferInstance)
  let _ : Cofibration (ι.app ((resolutionFunctor Q ε).obj F).left) :=
    (cofibration_iff _).mpr (hι _ inferInstance)
  let _ : WeakEquivalence (intermediateToResolution Q ε F).left :=
    (weakEquivalence_iff _).mpr (intermediateToResolution_weak Q ε hε F).1
  let _ : WeakEquivalence (intermediateToResolution Q ε F).right :=
    (weakEquivalence_iff _).mpr (intermediateToResolution_weak Q ε hε F).2
  exact chosenCofiberMap_weak Z hZ cone ι c hc (intermediateToResolution Q ε F)
    (hCone _ inferInstance) (hCone _ inferInstance)

end ChosenCofibers

section ChosenFibers

/-- The complete resolution Arrow transports both original chosen fiber projections. -/
def resolvedToOriginalFiberNatTrans :
    resolutionFunctor Q ε ⋙ OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⟶
      OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs :=
  Functor.whiskerRight (toOriginalNatTrans Q ε)
    (OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs)

include hε in
/-- The resolved-to-original fiber map is weak at every fibration over a fibrant base. -/
theorem resolvedToOriginalFiber_weak
    [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
    (F : Arrow C) [Fibration F.hom] [IsFibrant F.right] :
    weakEquivalences C ((resolvedToOriginalFiberNatTrans Z hZ s hs Q ε).app F) := by
  let _ : Fibration ((resolutionFunctor Q ε).obj F).hom := resolvedMap_fibration Q ε hε F
  let _ : Fibration (ε.app F.right) := (mem_trivialFibrations_iff _).mp (hε F.right) |>.1
  let _ : IsFibrant ((𝟭 C).obj F.right) := inferInstanceAs (IsFibrant F.right)
  let _ : IsFibrant (Q.obj F.right) := isFibrant_of_fibration (ε.app F.right)
  let _ : IsFibrant ((resolutionFunctor Q ε).obj F).right :=
    inferInstanceAs (IsFibrant (Q.obj F.right))
  let _ : WeakEquivalence (toOriginal Q ε F).left :=
    (weakEquivalence_iff _).mpr (toOriginal_trivialFibrations Q ε hε F).1.2
  let _ : WeakEquivalence (toOriginal Q ε F).right :=
    (weakEquivalence_iff _).mpr (toOriginal_trivialFibrations Q ε hε F).2.2
  exact originalChosenMap_weak Z hZ s hs (toOriginal Q ε F)

/-- The unchanged Q acts on the same entire resolved-to-original chosen fiber map. -/
def resolvedQToOriginalQFiberNatTrans :
    resolutionFunctor Q ε ⋙ OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙ Q ⟶
      OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙ Q :=
  Functor.whiskerRight (resolvedToOriginalFiberNatTrans Z hZ s hs Q ε) Q

include hε in
/-- Q of the actual complete resolved-to-original fiber map is weak. -/
theorem resolvedQToOriginalQFiber_weak
    [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
    (F : Arrow C) [Fibration F.hom] [IsFibrant F.right] :
    weakEquivalences C ((resolvedQToOriginalQFiberNatTrans Z hZ s hs Q ε).app F) :=
  Q_map_weak Q ε hε _ (resolvedToOriginalFiber_weak Z hZ s hs Q ε hε F)

/-- The same original Q-fiber carrier gives its strict null Arrow square to the unchanged input. -/
def QFiberNullSquare (F : Arrow C) :
    Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s F).pt)) ⟶ F :=
  Arrow.homMk (ε.app (s F).pt ≫ (s F).fst) (hZ.isInitial.to F.right) (by
    change (ε.app (s F).pt ≫ (s F).fst) ≫ F.hom =
      OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s F).pt) ≫ hZ.isInitial.to F.right
    rw [Category.assoc, (s F).condition, ← Category.assoc]
    exact congrArg (fun m => m ≫ hZ.isInitial.to F.right) (hZ.isTerminal.hom_ext _ _))

/-- Both complete Q-fiber null-square components are natural on every original Arrow map. -/
def QFiberNullSquareNatTrans :
    OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙ Q ⋙
      OrdinaryHoChosenPuppe.zeroArrowFunctor Z hZ ⟶ 𝟭 (Arrow C) where
  app F := QFiberNullSquare Z hZ s Q ε F
  naturality F G q := by
    apply Arrow.hom_ext
    · change Q.map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q) ≫
        (ε.app (s G).pt ≫ (s G).fst) = (ε.app (s F).pt ≫ (s F).fst) ≫ q.left
      rw [← Category.assoc, ε.naturality, Functor.id_map, Category.assoc,
        OrdinaryHoChosenFiberMaps.chosenMap_fst, Category.assoc]
    · exact hZ.isInitial.hom_ext _ _

variable (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

/-- The literal chosen suspension of the original Q fiber maps to the actual chosen cofiber. -/
def QFiberSuspensionToCofiber (F : Arrow C) :
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (Q.obj (s F).pt)).pt ⟶ (c F).pt :=
  OrdinaryHoChosenPuppe.cofiberMap cone ι c hc (QFiberNullSquare Z hZ s Q ε F)

omit [ModelCategory C] in
/-- Its first whole chosen leg retains Q's actual counit and the original fiber projection. -/
theorem QFiberSuspensionToCofiber_cone (F : Arrow C) :
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (Q.obj (s F).pt)).inl ≫
      QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F =
        cone.map (ε.app (s F).pt ≫ (s F).fst) ≫ (c F).inl :=
  OrdinaryHoChosenPuppe.cofiberMap_cone cone ι c hc (QFiberNullSquare Z hZ s Q ε F)

omit [ModelCategory C] in
/-- Its second whole leg retains the original initial endpoint and target cofiber leg. -/
theorem QFiberSuspensionToCofiber_zero (F : Arrow C) :
    (OrdinaryHoChosenPuppe.suspensionCone cone ι c Z hZ (Q.obj (s F).pt)).inr ≫
      QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F =
        hZ.isInitial.to F.right ≫ (c F).inr :=
  OrdinaryHoChosenPuppe.cofiberMap_target cone ι c hc (QFiberNullSquare Z hZ s Q ε F)

omit [ModelCategory C] in
/-- The original boundary is the suspension of the same complete Q-fiber inclusion. -/
theorem QFiberSuspensionToCofiber_boundary (F : Arrow C) :
    QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F ≫
      OrdinaryHoChosenPuppe.boundary cone ι c hc Z hZ F =
        OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
          (ε.app (s F).pt ≫ (s F).fst) := by
  apply PushoutCocone.IsColimit.hom_ext
    (hc (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s F).pt))))
  · rw [← Category.assoc, QFiberSuspensionToCofiber_cone, Category.assoc,
      OrdinaryHoChosenPuppe.boundary_cone, OrdinaryHoChosenPuppe.suspensionMap_cone]
  · rw [← Category.assoc, QFiberSuspensionToCofiber_zero, Category.assoc,
      OrdinaryHoChosenPuppe.boundary_target, ← Category.assoc]
    rw [show hZ.isInitial.to F.right ≫ OrdinaryHoChosenPuppe.toZero Z hZ F.right = 𝟙 Z
      from hZ.isTerminal.hom_ext _ _]
    exact (Category.id_comp _).trans
      (OrdinaryHoChosenPuppe.suspensionMap_zero cone ι c hc Z hZ
        (ε.app (s F).pt ≫ (s F).fst)).symm

/-- The entire Q-fiber suspension comparison preserves every input Arrow map. -/
def QFiberSuspensionToCofiberNatTrans :
    OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙ Q ⋙
      OrdinaryHoChosenPuppe.suspensionFunctor cone ι c hc Z hZ ⟶
        OrdinaryHoChosenPuppe.cofiberFunctor cone ι c hc :=
  Functor.whiskerRight (QFiberNullSquareNatTrans Z hZ s hs Q ε)
    (OrdinaryHoChosenPuppe.cofiberFunctor cone ι c hc)

omit [ModelCategory C] in
/-- The complete source and target actions commute with the same actual Q-fiber comparison. -/
theorem QFiberSuspensionToCofiber_naturality {F G : Arrow C} (q : F ⟶ G) :
    OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.chosenMap Z hZ s hs q)) ≫
        QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc G =
      QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F ≫
        OrdinaryHoChosenPuppe.cofiberMap cone ι c hc q :=
  (QFiberSuspensionToCofiberNatTrans Z hZ s hs Q ε cone ι c hc).naturality q

/-- Original suspension transports the complete Q-fiber resolution map and its two projections. -/
def resolvedQFiberSuspensionToOriginalNatTrans :
    resolutionFunctor Q ε ⋙ OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙ Q ⋙
      OrdinaryHoChosenPuppe.suspensionFunctor cone ι c hc Z hZ ⟶
        OrdinaryHoChosenFiberMaps.chosenFunctor Z hZ s hs ⋙ Q ⋙
          OrdinaryHoChosenPuppe.suspensionFunctor cone ι c hc Z hZ :=
  Functor.whiskerRight (resolvedQToOriginalQFiberNatTrans Z hZ s hs Q ε)
    (OrdinaryHoChosenPuppe.suspensionFunctor cone ι c hc Z hZ)

include hQ hε in
/-- The suspended original Q-fiber resolution map is weak by its original cone contractions. -/
theorem resolvedQFiberSuspensionToOriginal_weak
    [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
    (hι : ∀ X : C, IsCofibrant X → cofibrations C (ι.app X))
    (hCone : ∀ X : C, IsCofibrant X →
      weakEquivalences C (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj X)))
    (F : Arrow C) [Fibration F.hom] [IsFibrant F.right] :
    weakEquivalences C
      ((resolvedQFiberSuspensionToOriginalNatTrans Z hZ s hs Q ε cone ι c hc).app F) := by
  let _ : IsCofibrant (Q.obj (s ((resolutionFunctor Q ε).obj F)).pt) :=
    hQ (s ((resolutionFunctor Q ε).obj F)).pt
  let _ : IsCofibrant (Q.obj (s F).pt) := hQ (s F).pt
  let _ : Cofibration (ι.app (Q.obj (s ((resolutionFunctor Q ε).obj F)).pt)) :=
    (cofibration_iff _).mpr (hι _ inferInstance)
  let _ : Cofibration (ι.app (Q.obj (s F).pt)) := (cofibration_iff _).mpr (hι _ inferInstance)
  let _ : WeakEquivalence (Q.map ((resolvedToOriginalFiberNatTrans Z hZ s hs Q ε).app F)) :=
    (weakEquivalence_iff _).mpr (resolvedQToOriginalQFiber_weak Z hZ s hs Q ε hε F)
  exact OrdinaryHoChosenPuppeRotation.suspensionMap_weak_of_cofibrant cone ι c hc Z hZ
    (X := Q.obj (s ((resolutionFunctor Q ε).obj F)).pt) (Y := Q.obj (s F).pt)
    (Q.map ((resolvedToOriginalFiberNatTrans Z hZ s hs Q ε).app F))
    (hCone _ inferInstance) (hCone _ inferInstance)

variable (t : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (ht : ∀ F, IsLimit (t F))

omit [ModelCategory C] in
/-- Both original projections identify the entire Q-fiber null square under a change of choice. -/
theorem QFiberNullSquare_choice (F : Arrow C) :
    (OrdinaryHoChosenPuppe.zeroArrowFunctor Z hZ).map
      (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F).hom) ≫
        QFiberNullSquare Z hZ t Q ε F = QFiberNullSquare Z hZ s Q ε F := by
  apply Arrow.hom_ext
  · change Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F).hom ≫
      (ε.app (t F).pt ≫ (t F).fst) = ε.app (s F).pt ≫ (s F).fst
    rw [← Category.assoc, ε.naturality, Functor.id_map, Category.assoc,
      OrdinaryHoChosenFiberMaps.choiceIso_hom_fst]
  · change 𝟙 Z ≫ hZ.isInitial.to F.right = hZ.isInitial.to F.right
    exact Category.id_comp _

omit [ModelCategory C] in
/-- The actual suspended Q-fiber map preserves every original limiting-cone choice. -/
theorem QFiberSuspensionToCofiber_choice (F : Arrow C) :
    OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ
      (Q.map (OrdinaryHoChosenFiberMaps.choiceIso Z hZ s hs t ht F).hom) ≫
        QFiberSuspensionToCofiber Z hZ t Q ε cone ι c hc F =
      QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F := by
  have h := congrArg (fun m => OrdinaryHoChosenPuppe.cofiberMap cone ι c hc m)
    (QFiberNullSquare_choice Z hZ s hs Q ε t ht F)
  rw [OrdinaryHoChosenPuppe.cofiberMap_comp] at h
  exact h

variable (d : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hd : ∀ F, IsColimit (d F))

omit [ModelCategory C] in
/-- The whole Q-fiber/cofiber comparison retains the original suspension and cofiber choices. -/
theorem QFiberSuspensionToCofiber_cofiberChoice (F : Arrow C) :
    (cofiberChoiceIso cone ι c hc d hd
      (Arrow.mk (OrdinaryHoChosenPuppe.toZero Z hZ (Q.obj (s F).pt)))).hom ≫
        QFiberSuspensionToCofiber Z hZ s Q ε cone ι d hd F =
      QFiberSuspensionToCofiber Z hZ s Q ε cone ι c hc F ≫
        (cofiberChoiceIso cone ι c hc d hd F).hom :=
  ((cofiberChoiceNatIso cone ι c hc d hd).hom.naturality
    (QFiberNullSquare Z hZ s Q ε F)).symm

end ChosenFibers

end ArrowResolution

end HomotopicalAlgebra.OrdinaryHoChosenFiberCofiberComparison
