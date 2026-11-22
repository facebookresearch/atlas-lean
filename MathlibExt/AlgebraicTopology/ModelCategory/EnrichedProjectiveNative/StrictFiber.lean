/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero
public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
public import MathlibExt.Topology.Category.CGWH.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Full original native spectrum strict fibers and chosen-fiber maps

The zero endpoint is the original `zeroDiagram`; the fiber is its actual
pullback along the original arrow. All maps are constructed by that
pullback universal property. The objects and maps are genuine enriched
diagrams, so the complete enriched action is preserved.

An arbitrary caller-chosen pullback cone has its own unchanged carrier and
projections. Its universal property constructs the comparison and every
map; no comparison maps or functor laws are incoming. Both directions,
both projections, all Arrow components and the whole choice-family natural
isomorphism are proved explicitly.

No stable model, stable properness or fiber-nullity law is used here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The actual original chosen zero cospan defining the strict fiber. -/
def fiberCospan {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    WalkingCospan ⥤ EnrichedFunctorCat PointedCGWH.{u, v} A := cospan f (zeroTo Y)

/-- The original strict fiber is the selected pullback of the unchanged map and zero. -/
abbrev fiber {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    EnrichedFunctorCat PointedCGWH.{u, v} A := pullback f (zeroTo Y)

/-- The original full spectrum fiber projects to its unchanged total spectrum. -/
abbrev fiberToTotal {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    fiber f ⟶ X := pullback.fst f (zeroTo Y)

/-- The original full spectrum fiber collapses to the same original zero diagram. -/
abbrev fiberToZero {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    fiber f ⟶ zeroDiagram := pullback.snd f (zeroTo Y)

/-- The original two fiber projections satisfy their full spectrum equation. -/
theorem fiber_condition {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    fiberToTotal f ≫ f = fiberToZero f ≫ zeroTo Y := pullback.condition

/-- The full selected original spectrum fiber cone. -/
def fiberCone {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    PullbackCone f (zeroTo Y) :=
  PullbackCone.mk (fiberToTotal f) (fiberToZero f) (fiber_condition f)

/-- The full original chosen spectrum fiber has its actual limit universal property. -/
def fiberConeIsLimit {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    IsLimit (fiberCone f) := pullbackIsPullback f (zeroTo Y)

/-- Every original Arrow square induces the full strict-fiber spectrum map. -/
def fiberMap {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    fiber F.hom ⟶ fiber G.hom :=
  pullback.lift (fiberToTotal F.hom ≫ q.left) (fiberToZero F.hom) (by
    calc
      (fiberToTotal F.hom ≫ q.left) ≫ G.hom =
          (fiberToTotal F.hom ≫ F.hom) ≫ q.right := by
            rw [Category.assoc, Arrow.w q, ← Category.assoc]
      _ = (fiberToZero F.hom ≫ zeroTo F.right) ≫ q.right := by
            rw [fiber_condition]
      _ = fiberToZero F.hom ≫ zeroTo G.right := by
            rw [Category.assoc, zeroTo_naturality])

/-- Every original fiber map retains the entire total-spectrum projection square. -/
theorem fiberMap_fst {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    fiberMap q ≫ fiberToTotal G.hom = fiberToTotal F.hom ≫ q.left :=
  pullback.lift_fst _ _ _

/-- Every original fiber map retains the same original zero-spectrum projection. -/
theorem fiberMap_snd {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    fiberMap q ≫ fiberToZero G.hom = fiberToZero F.hom := pullback.lift_snd _ _ _

/-- The full original enriched strict-fiber construction is a genuine functor. -/
def fiberFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A where
  obj F := fiber F.hom
  map q := fiberMap q
  map_id F := by
    apply pullback.hom_ext
    · rw [fiberMap_fst, Category.id_comp]
      exact Category.comp_id _
    · rw [fiberMap_snd, Category.id_comp]
  map_comp {F G H} q r := by
    apply pullback.hom_ext
    · rw [fiberMap_fst, Category.assoc, fiberMap_fst,
        ← Category.assoc, fiberMap_fst]
      rw [Arrow.comp_left, Category.assoc]
    · rw [fiberMap_snd, Category.assoc, fiberMap_snd, fiberMap_snd]

/-- The complete original total projections form a natural transformation. -/
def fiberToTotalNatTrans : fiberFunctor (A := A) ⟶ Arrow.leftFunc where
  app F := fiberToTotal F.hom
  naturality {F G} q := by
    change fiberMap q ≫ fiberToTotal G.hom = fiberToTotal F.hom ≫ q.left
    exact fiberMap_fst q

/-- The complete original zero projections form a natural transformation. -/
def fiberToZeroNatTrans : fiberFunctor (A := A) ⟶
    (Functor.const (Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))).obj zeroDiagram where
  app F := fiberToZero F.hom
  naturality {F G} q := by
    change fiberMap q ≫ fiberToZero G.hom = fiberToZero F.hom ≫ 𝟙 zeroDiagram
    rw [Category.comp_id]
    exact fiberMap_snd q

/-- The whole total-projection Arrow functor retains the original spectrum endpoints. -/
def fiberToTotalArrowFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) where
  obj F := Arrow.mk (fiberToTotal F.hom)
  map q := Arrow.homMk (fiberFunctor.map q) q.left (fiberMap_fst q)
  map_id F := by
    apply Arrow.hom_ext
    · change fiberFunctor.map (𝟙 F) = 𝟙 (fiberFunctor.obj F)
      exact fiberFunctor.map_id F
    · rfl
  map_comp q r := by
    apply Arrow.hom_ext
    · change fiberFunctor.map (q ≫ r) = fiberFunctor.map q ≫ fiberFunctor.map r
      exact fiberFunctor.map_comp q r
    · rfl

/-- The whole collapse Arrow functor retains the same chosen original zero endpoint. -/
def fiberToZeroArrowFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) where
  obj F := Arrow.mk (fiberToZero F.hom)
  map {F G} q := Arrow.homMk (fiberFunctor.map q) (𝟙 zeroDiagram) (by
    change fiberMap q ≫ fiberToZero G.hom = fiberToZero F.hom ≫ 𝟙 zeroDiagram
    rw [Category.comp_id]
    exact fiberMap_snd q)
  map_id F := by
    apply Arrow.hom_ext
    · change fiberFunctor.map (𝟙 F) = 𝟙 (fiberFunctor.obj F)
      exact fiberFunctor.map_id F
    · rfl
  map_comp q r := by
    apply Arrow.hom_ext
    · change fiberFunctor.map (q ≫ r) = fiberFunctor.map q ≫ fiberFunctor.map r
      exact fiberFunctor.map_comp q r
    · exact (Category.comp_id _).symm

/-- A full Arrow square determines the full cone used for maps of arbitrary chosen fibers. -/
def chosenMapCone {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)}
    (q : F ⟶ G) (s : PullbackCone F.hom (zeroTo F.right)) :
    PullbackCone G.hom (zeroTo G.right) :=
  PullbackCone.mk (s.fst ≫ q.left) s.snd (by
    calc
      (s.fst ≫ q.left) ≫ G.hom = (s.fst ≫ F.hom) ≫ q.right := by
        rw [Category.assoc, Arrow.w q, ← Category.assoc]
      _ = (s.snd ≫ zeroTo F.right) ≫ q.right := by rw [s.condition]
      _ = s.snd ≫ zeroTo G.right := by rw [Category.assoc, zeroTo_naturality])

/-- The target's actual universal property constructs a map between caller-chosen fibers. -/
def chosenFiberMap {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)}
    (q : F ⟶ G) (s : PullbackCone F.hom (zeroTo F.right))
    (t : PullbackCone G.hom (zeroTo G.right)) (ht : IsLimit t) : s.pt ⟶ t.pt :=
  ht.lift (chosenMapCone q s)

/-- The constructed chosen-fiber map preserves its caller's actual total projection. -/
theorem chosenFiberMap_fst {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)}
    (q : F ⟶ G) (s : PullbackCone F.hom (zeroTo F.right))
    (t : PullbackCone G.hom (zeroTo G.right)) (ht : IsLimit t) :
    chosenFiberMap q s t ht ≫ t.fst = s.fst ≫ q.left :=
  ht.fac (chosenMapCone q s) WalkingCospan.left

/-- The constructed chosen-fiber map preserves its caller's actual zero projection. -/
theorem chosenFiberMap_snd {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)}
    (q : F ⟶ G) (s : PullbackCone F.hom (zeroTo F.right))
    (t : PullbackCone G.hom (zeroTo G.right)) (ht : IsLimit t) :
    chosenFiberMap q s t ht ≫ t.snd = s.snd :=
  ht.fac (chosenMapCone q s) WalkingCospan.right

/-- A caller-chosen fiber is compared with the selected original fiber by their actual limits. -/
def chosenFiberIso {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) : s.pt ≅ fiber f :=
  hs.conePointUniqueUpToIso (t := fiberCone f) (fiberConeIsLimit f)

/-- The entire forward comparison retains the caller's original total projection. -/
theorem chosenFiberIso_hom_fst {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberIso f s hs).hom ≫ fiberToTotal f = s.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp hs (fiberConeIsLimit f) WalkingCospan.left

/-- The entire forward comparison retains the caller's original zero projection. -/
theorem chosenFiberIso_hom_snd {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberIso f s hs).hom ≫ fiberToZero f = s.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp hs (fiberConeIsLimit f) WalkingCospan.right

/-- The entire inverse comparison retains the same original total projection. -/
theorem chosenFiberIso_inv_fst {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberIso f s hs).inv ≫ s.fst = fiberToTotal f := by
  rw [← chosenFiberIso_hom_fst f s hs, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The entire inverse comparison retains the same original zero projection. -/
theorem chosenFiberIso_inv_snd {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (s : PullbackCone f (zeroTo Y)) (hs : IsLimit s) :
    (chosenFiberIso f s hs).inv ≫ s.snd = fiberToZero f := by
  rw [← chosenFiberIso_hom_snd f s hs, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- All nonidentity original Arrow squares commute with the complete chosen-fiber comparison. -/
theorem chosenFiberIso_naturality {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)}
    (q : F ⟶ G) (s : PullbackCone F.hom (zeroTo F.right)) (hs : IsLimit s)
    (t : PullbackCone G.hom (zeroTo G.right)) (ht : IsLimit t) :
    chosenFiberMap q s t ht ≫ (chosenFiberIso G.hom t ht).hom =
      (chosenFiberIso F.hom s hs).hom ≫ fiberFunctor.map q := by
  change chosenFiberMap q s t ht ≫ (chosenFiberIso G.hom t ht).hom =
    (chosenFiberIso F.hom s hs).hom ≫ fiberMap q
  apply pullback.hom_ext
  · rw [Category.assoc, chosenFiberIso_hom_fst, chosenFiberMap_fst,
      Category.assoc, fiberMap_fst, ← Category.assoc, chosenFiberIso_hom_fst]
  · rw [Category.assoc, chosenFiberIso_hom_snd, chosenFiberMap_snd,
      Category.assoc, fiberMap_snd, chosenFiberIso_hom_snd]

variable
  (s : ∀ F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A),
    PullbackCone F.hom (zeroTo F.right))
  (hs : ∀ F, IsLimit (s F))

/-- An arbitrary family of actual chosen fibers forms a functor by its own universal properties. -/
def chosenFiberFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A where
  obj F := (s F).pt
  map {F G} q := chosenFiberMap q (s F) (s G) (hs G)
  map_id F := by
    apply PullbackCone.IsLimit.hom_ext (hs F)
    · rw [chosenFiberMap_fst, Category.id_comp]
      exact Category.comp_id _
    · rw [chosenFiberMap_snd, Category.id_comp]
  map_comp {F G H} q r := by
    apply PullbackCone.IsLimit.hom_ext (hs H)
    · rw [chosenFiberMap_fst, Category.assoc, chosenFiberMap_fst,
        ← Category.assoc, chosenFiberMap_fst]
      rw [Arrow.comp_left, Category.assoc]
    · rw [chosenFiberMap_snd, Category.assoc, chosenFiberMap_snd, chosenFiberMap_snd]

/-- The entire original chosen-fiber functor is naturally isomorphic to the actual selected one. -/
def chosenFiberNatIso : chosenFiberFunctor s hs ≅ fiberFunctor (A := A) :=
  NatIso.ofComponents (fun F => chosenFiberIso F.hom (s F) (hs F)) (by
    intro F G q
    exact chosenFiberIso_naturality q (s F) (hs F) (s G) (hs G))

/-- The whole chosen-fiber comparison has the caller's exact constructed component. -/
theorem chosenFiberNatIso_app (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (chosenFiberNatIso s hs).app F = chosenFiberIso F.hom (s F) (hs F) := rfl

/-- Every inverse chosen-functor component satisfies full source-first naturality. -/
theorem chosenFiberNatIso_inv_naturality
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    fiberFunctor.map q ≫ (chosenFiberNatIso s hs).inv.app G =
      (chosenFiberNatIso s hs).inv.app F ≫ (chosenFiberFunctor s hs).map q :=
  (chosenFiberNatIso s hs).inv.naturality q



variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable
  (s : ∀ F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A),
    PullbackCone F.hom (zeroTo F.right))
  (hs : ∀ F, IsLimit (s F))

/-- The entire chosen total projection keeps the actual caller's first leg. -/
def chosenFiberToTotalNatTrans : chosenFiberFunctor s hs ⟶ Arrow.leftFunc where
  app F := (s F).fst
  naturality {F G} q := chosenFiberMap_fst q (s F) (s G) (hs G)

/-- The entire chosen collapse keeps the actual caller's second leg. -/
def chosenFiberToZeroNatTrans : chosenFiberFunctor s hs ⟶
    (Functor.const (Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))).obj zeroDiagram where
  app F := (s F).snd
  naturality {F G} q := by
    change chosenFiberMap q (s F) (s G) (hs G) ≫ (s G).snd = (s F).snd ≫ 𝟙 _
    rw [Category.comp_id]
    exact chosenFiberMap_snd q (s F) (s G) (hs G)

/-- The whole total-projection Arrow functor retains both original endpoints. -/
def chosenFiberToTotalArrowFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) where
  obj F := Arrow.mk (s F).fst
  map q := Arrow.homMk ((chosenFiberFunctor s hs).map q) q.left
    (chosenFiberMap_fst q (s _) (s _) (hs _))
  map_id F := by
    apply Arrow.hom_ext
    · exact (chosenFiberFunctor s hs).map_id F
    · rfl
  map_comp q r := by
    apply Arrow.hom_ext
    · exact (chosenFiberFunctor s hs).map_comp q r
    · rfl

/-- The whole collapse Arrow functor retains the actual original zero endpoint. -/
def chosenFiberToZeroArrowFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) where
  obj F := Arrow.mk (s F).snd
  map {F G} q := Arrow.homMk ((chosenFiberFunctor s hs).map q) (𝟙 zeroDiagram) (by
    change chosenFiberMap q (s F) (s G) (hs G) ≫ (s G).snd =
      (s F).snd ≫ 𝟙 zeroDiagram
    rw [Category.comp_id]
    exact chosenFiberMap_snd q (s F) (s G) (hs G))
  map_id F := by
    apply Arrow.hom_ext
    · exact (chosenFiberFunctor s hs).map_id F
    · rfl
  map_comp q r := by
    apply Arrow.hom_ext
    · exact (chosenFiberFunctor s hs).map_comp q r
    · exact (Category.comp_id _).symm

/-- The same chosen total transformation retains its complete first projection. -/
theorem chosenFiberToTotalNatTrans_app (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (chosenFiberToTotalNatTrans s hs).app F = (s F).fst := rfl

/-- The same chosen collapse transformation retains its complete second projection. -/
theorem chosenFiberToZeroNatTrans_app (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (chosenFiberToZeroNatTrans s hs).app F = (s F).snd := rfl

/-- Every nonidentity input keeps the complete chosen fiber map as the first Arrow field. -/
theorem chosenFiberToTotalArrowFunctor_map_left
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    ((chosenFiberToTotalArrowFunctor s hs).map q).left =
      chosenFiberMap q (s F) (s G) (hs G) := rfl

/-- Every nonidentity input keeps its actual original source map as the second Arrow field. -/
theorem chosenFiberToTotalArrowFunctor_map_right
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    ((chosenFiberToTotalArrowFunctor s hs).map q).right = q.left := rfl

/-- Every collapse input keeps the complete actual chosen fiber map. -/
theorem chosenFiberToZeroArrowFunctor_map_left
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    ((chosenFiberToZeroArrowFunctor s hs).map q).left =
      chosenFiberMap q (s F) (s G) (hs G) := rfl

/-- Every collapse input keeps identity on the actual original zero diagram. -/
theorem chosenFiberToZeroArrowFunctor_map_right
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (q : F ⟶ G) :
    ((chosenFiberToZeroArrowFunctor s hs).map q).right = 𝟙 zeroDiagram := rfl

/-- The full chosen comparison forward map commutes with the first projection. -/
theorem chosenFiberNatIso_hom_toTotal (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (chosenFiberNatIso s hs).hom.app F ≫ fiberToTotal F.hom = (s F).fst :=
  chosenFiberIso_hom_fst F.hom (s F) (hs F)

/-- The full chosen comparison inverse map commutes with the first projection. -/
theorem chosenFiberNatIso_inv_toTotal (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (chosenFiberNatIso s hs).inv.app F ≫ (s F).fst = fiberToTotal F.hom :=
  chosenFiberIso_inv_fst F.hom (s F) (hs F)

/-- The full chosen comparison forward map commutes with the original zero projection. -/
theorem chosenFiberNatIso_hom_toZero (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (chosenFiberNatIso s hs).hom.app F ≫ fiberToZero F.hom = (s F).snd :=
  chosenFiberIso_hom_snd F.hom (s F) (hs F)

/-- The full chosen comparison inverse map commutes with the original zero projection. -/
theorem chosenFiberNatIso_inv_toZero (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (chosenFiberNatIso s hs).inv.app F ≫ (s F).snd = fiberToZero F.hom :=
  chosenFiberIso_inv_snd F.hom (s F) (hs F)

/-- The complete caller collapse is the original zero functor on the same chosen fiber. -/
def chosenFiberCollapseNatIso : chosenFiberToZeroArrowFunctor s hs ≅
    chosenFiberFunctor s hs ⋙ toZeroArrow :=
  NatIso.ofComponents (fun F => Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 (s F).pt ≫ toZero (s F).pt = (s F).snd ≫ 𝟙 zeroDiagram
      rw [Category.id_comp, Category.comp_id]
      exact zeroDiagramIsTerminal.hom_ext _ _)) (by
    intro F G q
    apply Arrow.hom_ext
    · change chosenFiberMap q (s F) (s G) (hs G) ≫ 𝟙 (s G).pt =
        𝟙 (s F).pt ≫ chosenFiberMap q (s F) (s G) (hs G)
      rw [Category.comp_id, Category.id_comp]
    · change 𝟙 zeroDiagram ≫ 𝟙 zeroDiagram = 𝟙 zeroDiagram ≫ 𝟙 zeroDiagram
      rfl)

/-- The forward collapse comparison changes no actual chosen fiber map. -/
theorem chosenFiberCollapseNatIso_hom_left
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    ((chosenFiberCollapseNatIso s hs).hom.app F).left = 𝟙 (s F).pt := rfl

/-- The inverse collapse comparison changes no actual chosen fiber map. -/
theorem chosenFiberCollapseNatIso_inv_left
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    ((chosenFiberCollapseNatIso s hs).inv.app F).left = 𝟙 (s F).pt := rfl

/-- The forward collapse comparison changes no original zero endpoint. -/
theorem chosenFiberCollapseNatIso_hom_right
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    ((chosenFiberCollapseNatIso s hs).hom.app F).right = 𝟙 zeroDiagram := rfl

/-- The inverse collapse comparison changes no original zero endpoint. -/
theorem chosenFiberCollapseNatIso_inv_right
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    ((chosenFiberCollapseNatIso s hs).inv.app F).right = 𝟙 zeroDiagram := rfl



end HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
