/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Filtered.NatTail
import MathlibExt.CategoryTheory.Functor.CoaugmentationIteration
import MathlibExt.Topology.Category.PointedCGWH.Colimits.AtPoints
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.LoopPowerAtPoints

/-!
# Loop-tail iteration and physical-point comparisons

These constructions use arbitrary categories, original input coaugmentations,
and actual CGWH diagram points. They provide both maps of the pointwise loop
comparison without selecting a spectrum index. The established public names
are retained for clients of the original loop-tail comparison module.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC uV vV uA vA

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalLoopTailAllPointComparison

attribute [local instance] PointedCGWH.PointedAtGeometry.pointedNatColimits

section OriginalInputSequence

variable {C : Type uC} [Category.{vC} C]

/-- The original ordered successor sends every index and every order arrow to its successor. -/
def nextIndex : ℕ ⥤ ℕ :=
  (show Monotone (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_le_add_right h 1).functor

/-- Both successor-tail maps retain the literal equality of their original ordered indices. -/
def nextTailIso (r : ℕ) :
    NatTail.tailFunctor (r + 1) ≅ NatTail.tailFunctor r ⋙ nextIndex :=
  NatIso.ofComponents
    (fun n => eqToIso (Nat.add_right_comm r 1 n))
    (fun _ => Subsingleton.elim _ _)

/-- The successor input transformation is the image of the preceding original input map. -/
def inputNextHom {F : C ⥤ C} (η : 𝟭 C ⟶ F) (X : C) :
    nextIndex ⋙ Functor.Iteration.inputDiagram η X ⟶
      Functor.Iteration.inputDiagram η X ⋙ F :=
  NatTrans.ofSequence
    (fun n => 𝟙 (F.obj ((Functor.Iteration.iterate F n).obj X)))
    (fun n => by
      change (Functor.Iteration.inputDiagram η X).map (homOfLE (Nat.le_succ (n + 1))) ≫
        𝟙 _ = 𝟙 _ ≫ F.map ((Functor.Iteration.inputDiagram η X).map
          (homOfLE (Nat.le_succ n)))
      rw [Category.comp_id, Category.id_comp,
        Functor.Iteration.inputDiagram_map_succ, Functor.Iteration.inputDiagram_map_succ]
      exact Functor.Iteration.inputTransition_succ_app η n X)

/-- Both full sequence maps retain the original input-coaugmentation successors. -/
def inputNextIso {F : C ⥤ C} (η : 𝟭 C ⟶ F) (X : C) :
    nextIndex ⋙ Functor.Iteration.inputDiagram η X ≅
      Functor.Iteration.inputDiagram η X ⋙ F :=
  NatIso.ofComponents
    (fun n => Iso.refl (F.obj ((Functor.Iteration.iterate F n).obj X)))
    (fun f => (inputNextHom η X).naturality f)

/-- Every forward successor component is the original identity on the iterated source. -/
theorem inputNextIso_hom_app {F : C ⥤ C} (η : 𝟭 C ⟶ F) (X : C) (n : ℕ) :
    (inputNextIso η X).hom.app n =
      𝟙 (F.obj ((Functor.Iteration.iterate F n).obj X)) := rfl

/-- Every inverse successor component retains the same entire original object. -/
theorem inputNextIso_inv_app {F : C ⥤ C} (η : 𝟭 C ⟶ F) (X : C) (n : ℕ) :
    (inputNextIso η X).inv.app n =
      𝟙 (F.obj ((Functor.Iteration.iterate F n).obj X)) := rfl

/-- The whole input-map square uses the actual successor iterate of the same original map. -/
theorem inputNextIso_input_naturality {F : C ⥤ C} (η : 𝟭 C ⟶ F)
    {X Y : C} (f : X ⟶ Y) :
    Functor.whiskerLeft nextIndex (Functor.Iteration.inputDiagramMap η f) ≫
        (inputNextIso η Y).hom =
      (inputNextIso η X).hom ≫
        Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) F := by
  apply NatTrans.ext
  funext n
  change (Functor.Iteration.iterate F (n + 1)).map f ≫ 𝟙 _ =
    𝟙 _ ≫ F.map ((Functor.Iteration.iterate F n).map f)
  rw [Category.comp_id, Category.id_comp]
  exact Functor.Iteration.map_succ F n f

/-- The complete inverse sequence square keeps that same input arrow. -/
theorem inputNextIso_input_inv_naturality {F : C ⥤ C} (η : 𝟭 C ⟶ F)
    {X Y : C} (f : X ⟶ Y) :
    Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) F ≫
        (inputNextIso η Y).inv =
      (inputNextIso η X).inv ≫
        Functor.whiskerLeft nextIndex (Functor.Iteration.inputDiagramMap η f) :=
  (CommSq.vert_inv (g := inputNextIso η X) (h := inputNextIso η Y)
    ⟨inputNextIso_input_naturality η f⟩).w

/-- Every source equality keeps the original input-diagram whole functor transport. -/
theorem inputDiagram_map_eqToHom {F : C ⥤ C} (η : 𝟭 C ⟶ F) (X : C)
    {i j : ℕ} (h : i = j) :
    (Functor.Iteration.inputDiagram η X).map (eqToHom h) =
      (eqToHom (congrArg (Functor.Iteration.iterate F) h)).app X := by
  cases h
  exact (Functor.Iteration.inputDiagram η X).map_id i

variable {V : Type uV} [Category.{vV} V] {A : Type uA} [Category.{vA} A]

/-- The full original evaluation comparison is pasted from the supplied actual functor maps. -/
def evaluatedDiagramIso (P D : A ⥤ C) (F : C ⥤ C)
    (L L' : C ⥤ V) (R : V ⥤ V) (e : P ≅ D ⋙ F) (s : F ⋙ L ≅ L' ⋙ R) :
    P ⋙ L ≅ (D ⋙ L') ⋙ R :=
  Functor.isoWhiskerRight e L ≪≫ Functor.associator D F L ≪≫
    Functor.isoWhiskerLeft D s ≪≫ (Functor.associator D L' R).symm

/-- Both original evaluation factors give their exact whole component map. -/
theorem evaluatedDiagramIso_hom_app (P D : A ⥤ C) (F : C ⥤ C)
    (L L' : C ⥤ V) (R : V ⥤ V) (e : P ≅ D ⋙ F) (s : F ⋙ L ≅ L' ⋙ R) (X : A) :
    (evaluatedDiagramIso P D F L L' R e s).hom.app X =
      L.map (e.hom.app X) ≫ s.hom.app (D.obj X) := by
  change L.map (e.hom.app X) ≫ 𝟙 _ ≫ s.hom.app (D.obj X) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The full positive-tail map retains the original ordered tail and evaluation comparison. -/
def positiveDiagramIso (D : ℕ ⥤ C) (F : C ⥤ C) (L L' : C ⥤ V) (R : V ⥤ V)
    (e : nextIndex ⋙ D ≅ D ⋙ F) (s : F ⋙ L ≅ L' ⋙ R) (r : ℕ) :
    NatTail.tailFunctor (r + 1) ⋙ (D ⋙ L) ≅ (NatTail.tailFunctor r ⋙ (D ⋙ L')) ⋙ R :=
  Functor.isoWhiskerRight (nextTailIso r) (D ⋙ L) ≪≫
    Functor.associator (NatTail.tailFunctor r) nextIndex (D ⋙ L) ≪≫
    Functor.isoWhiskerLeft (NatTail.tailFunctor r) (Functor.associator nextIndex D L).symm ≪≫
    Functor.isoWhiskerLeft (NatTail.tailFunctor r)
      (evaluatedDiagramIso (nextIndex ⋙ D) D F L L' R e s) ≪≫
    (Functor.associator (NatTail.tailFunctor r) (D ⋙ L') R).symm

/-- Every tail component is the exact original index map followed by its evaluation map. -/
theorem positiveDiagramIso_hom_app (D : ℕ ⥤ C) (F : C ⥤ C) (L L' : C ⥤ V) (R : V ⥤ V)
    (e : nextIndex ⋙ D ≅ D ⋙ F) (s : F ⋙ L ≅ L' ⋙ R) (r n : ℕ) :
    (positiveDiagramIso D F L L' R e s r).hom.app n =
      (D ⋙ L).map ((nextTailIso r).hom.app n) ≫
        (evaluatedDiagramIso (nextIndex ⋙ D) D F L L' R e s).hom.app (r + n) := by
  change (D ⋙ L).map ((nextTailIso r).hom.app n) ≫ 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

end OriginalInputSequence

section ActualPoints

open PointedCGWH.PointedAtGeometry PointedCGWH.LoopPowerAtPoints

/-- Repointing both maps of an actual carrier isomorphism preserves the given point equation. -/
def carrierPointIso {A D : CGWH.{u, v}} (e : A ≅ D)
    (p : A) (q : D) (h : e.hom p = q) :
    PointedCGWH.pointedAt A p ≅ PointedCGWH.pointedAt D q where
  hom := PointedCGWH.pointedAtMap e.hom p q h
  inv := PointedCGWH.pointedAtMap e.inv q p (by
    rw [← h]
    exact ConcreteCategory.congr_hom e.hom_inv_id p)
  hom_inv_id := by
    apply PointedCGWH.pointedToCGWH.map_injective
    exact e.hom_inv_id
  inv_hom_id := by
    apply PointedCGWH.pointedToCGWH.map_injective
    exact e.inv_hom_id

/-- Every forward carrier function is the original isomorphism's entire forward map. -/
theorem carrierPointIso_hom_right {A D : CGWH.{u, v}} (e : A ≅ D)
    (p : A) (q : D) (h : e.hom p = q) :
    (carrierPointIso e p q h).hom.right = e.hom := rfl

/-- Every inverse carrier function retains the original isomorphism's entire inverse map. -/
theorem carrierPointIso_inv_right {A D : CGWH.{u, v}} (e : A ≅ D)
    (p : A) (q : D) (h : e.hom p = q) :
    (carrierPointIso e p q h).inv.right = e.inv := rfl

/-- Both original diagram maps are repointed at the actual image of the zero-stage point. -/
def basedDiagramIso {D E : ℕ ⥤ CGWH.{u, v}} (e : D ≅ E) (p : D.obj 0) :
    diagramAt D p ≅ diagramAt E (e.hom.app 0 p) :=
  NatIso.ofComponents
    (fun n => carrierPointIso (e.app n) (diagramPoint D p n)
      (diagramPoint E (e.hom.app 0 p) n) (diagramPoint_map e.hom p n))
    (fun f => by
      apply PointedCGWH.pointedToCGWH.map_injective
      exact e.hom.naturality f)

/-- The full forward based transformation retains every original carrier component. -/
theorem basedDiagramIso_hom {D E : ℕ ⥤ CGWH.{u, v}} (e : D ≅ E) (p : D.obj 0) :
    (basedDiagramIso e p).hom = diagramAtMap e.hom p := by
  apply NatTrans.ext
  funext n
  rfl

/-- Every full inverse based component is the original inverse component at the same index. -/
theorem basedDiagramIso_inv_right {D E : ℕ ⥤ CGWH.{u, v}}
    (e : D ≅ E) (p : D.obj 0) (n : ℕ) :
    ((basedDiagramIso e p).inv.app n).right = e.inv.app n := rfl

/-- Given image-point equality changes no component of the complete original diagram map. -/
def basedDiagramMap {D E : ℕ ⥤ CGWH.{u, v}} (α : D ⟶ E)
    (p : D.obj 0) (q : E.obj 0) (h : α.app 0 p = q) :
    diagramAt D p ⟶ diagramAt E q :=
  { app := fun n => PointedCGWH.pointedAtMap (α.app n) _ _
      ((diagramPoint_map α p n).trans
        (congrArg (fun b => diagramPoint E b n) h))
    naturality := fun _ _ f => by
      apply PointedCGWH.pointedToCGWH.map_injective
      exact α.naturality f }

/-- Each repointed input component is the same complete original input component. -/
theorem basedDiagramMap_right {D E : ℕ ⥤ CGWH.{u, v}} (α : D ⟶ E)
    (p : D.obj 0) (q : E.obj 0) (h : α.app 0 p = q) (n : ℕ) :
    ((basedDiagramMap α p q h).app n).right = α.app n := rfl

/-- The arbitrary loop point is transported by every original predecessor arrow. -/
def loopDiagramPoint (D : ℕ ⥤ PointedCGWH.{u, v})
    (p : (PointedCGWH.loop.obj (D.obj 0)).right) (n : ℕ) :
    (PointedCGWH.loop.obj (D.obj n)).right :=
  diagramPoint ((D ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH) p n

/-- The same original loop map transports the given point across every full ordered arrow. -/
theorem loopDiagramPoint_naturality (D : ℕ ⥤ PointedCGWH.{u, v})
    (p : (PointedCGWH.loop.obj (D.obj 0)).right) {i j : ℕ} (f : i ⟶ j) :
    (PointedCGWH.loop.map (D.map f)).right (loopDiagramPoint D p i) =
      loopDiagramPoint D p j :=
  diagramPoint_naturality ((D ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH) p f

/-- Both all-degree maps at every loop component use the actual one-outer-loop comparison. -/
def loopBasedTypeComponent (D : ℕ ⥤ PointedCGWH.{u, v})
    (p : (PointedCGWH.loop.obj (D.obj 0)).right) (k n : ℕ) :
    (PointedCGWH.piNFunctor k).obj
      ((diagramAt ((D ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH) p).obj n) ≅
        (PointedCGWH.piNFunctor (k + 1)).obj (D.obj n) :=
  allPointComparison 0 k (D.obj n) (loopDiagramPoint D p n)

/-- The full arbitrary-point loop shift forms an isomorphism of the original Type diagrams. -/
def loopBasedTypeIso (D : ℕ ⥤ PointedCGWH.{u, v})
    (p : (PointedCGWH.loop.obj (D.obj 0)).right) (k : ℕ) :
    diagramAt ((D ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH) p ⋙
        PointedCGWH.piNFunctor k ≅ D ⋙ PointedCGWH.piNFunctor (k + 1) :=
  NatIso.ofComponents (fun n => loopBasedTypeComponent D p k n)
    (fun {i j} f => by
      exact allPointComparison_hom_naturality 0 k (D.map f)
        (loopDiagramPoint D p i) (loopDiagramPoint D p j)
        (loopDiagramPoint_naturality D p f))

/-- Each forward Type component is the full original one-loop arbitrary-point shift. -/
theorem loopBasedTypeIso_hom_app (D : ℕ ⥤ PointedCGWH.{u, v})
    (p : (PointedCGWH.loop.obj (D.obj 0)).right) (k n : ℕ) :
    (loopBasedTypeIso D p k).hom.app n =
      (allPointComparison 0 k (D.obj n) (loopDiagramPoint D p n)).hom := rfl

/-- Each inverse Type component is the same full original one-loop inverse shift. -/
theorem loopBasedTypeIso_inv_app (D : ℕ ⥤ PointedCGWH.{u, v})
    (p : (PointedCGWH.loop.obj (D.obj 0)).right) (k n : ℕ) :
    (loopBasedTypeIso D p k).inv.app n =
      (allPointComparison 0 k (D.obj n) (loopDiagramPoint D p n)).inv := rfl

/-- The complete arbitrary-point loop input map retains its original predecessor transformation. -/
def loopBasedMap {D E : ℕ ⥤ PointedCGWH.{u, v}} (α : D ⟶ E)
    (p : (PointedCGWH.loop.obj (D.obj 0)).right)
    (q : (PointedCGWH.loop.obj (E.obj 0)).right)
    (h : (PointedCGWH.loop.map (α.app 0)).right p = q) :
    diagramAt ((D ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH) p ⟶
      diagramAt ((E ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH) q :=
  basedDiagramMap
    (Functor.whiskerRight (Functor.whiskerRight α PointedCGWH.loop) PointedCGWH.pointedToCGWH)
    p q h

/-- The actual loop-map point equation holds at every original input index. -/
theorem loopBasedMap_point_naturality {D E : ℕ ⥤ PointedCGWH.{u, v}} (α : D ⟶ E)
    (p : (PointedCGWH.loop.obj (D.obj 0)).right)
    (q : (PointedCGWH.loop.obj (E.obj 0)).right)
    (h : (PointedCGWH.loop.map (α.app 0)).right p = q) (n : ℕ) :
    (PointedCGWH.loop.map (α.app n)).right (loopDiagramPoint D p n) =
      loopDiagramPoint E q n :=
  (diagramPoint_map
    (Functor.whiskerRight (Functor.whiskerRight α PointedCGWH.loop)
      PointedCGWH.pointedToCGWH) p n).trans
        (congrArg (fun b => loopDiagramPoint E b n) h)

/-- The whole forward arbitrary-point comparison commutes with every full predecessor input map. -/
theorem loopBasedTypeIso_input_naturality {D E : ℕ ⥤ PointedCGWH.{u, v}} (α : D ⟶ E)
    (p : (PointedCGWH.loop.obj (D.obj 0)).right)
    (q : (PointedCGWH.loop.obj (E.obj 0)).right)
    (h : (PointedCGWH.loop.map (α.app 0)).right p = q) (k : ℕ) :
    Functor.whiskerRight (loopBasedMap α p q h) (PointedCGWH.piNFunctor k) ≫
        (loopBasedTypeIso E q k).hom =
      (loopBasedTypeIso D p k).hom ≫
        Functor.whiskerRight α (PointedCGWH.piNFunctor (k + 1)) := by
  apply NatTrans.ext
  funext n
  exact allPointComparison_hom_naturality 0 k (α.app n)
    (loopDiagramPoint D p n) (loopDiagramPoint E q n)
    (loopBasedMap_point_naturality α p q h n)

/-- Both original inverse comparisons commute with those same actual input maps and points. -/
theorem loopBasedTypeIso_input_inv_naturality {D E : ℕ ⥤ PointedCGWH.{u, v}} (α : D ⟶ E)
    (p : (PointedCGWH.loop.obj (D.obj 0)).right)
    (q : (PointedCGWH.loop.obj (E.obj 0)).right)
    (h : (PointedCGWH.loop.map (α.app 0)).right p = q) (k : ℕ) :
    Functor.whiskerRight α (PointedCGWH.piNFunctor (k + 1)) ≫
        (loopBasedTypeIso E q k).inv =
      (loopBasedTypeIso D p k).inv ≫
        Functor.whiskerRight (loopBasedMap α p q h) (PointedCGWH.piNFunctor k) :=
  (CommSq.vert_inv (g := loopBasedTypeIso D p k) (h := loopBasedTypeIso E q k)
    ⟨loopBasedTypeIso_input_naturality α p q h k⟩).w

/-- Composition of the actual repointed diagrams keeps both original carrier maps. -/
theorem basedDiagramMap_comp {D E G : ℕ ⥤ CGWH.{u, v}}
    (α : D ⟶ E) (β : E ⟶ G) (p : D.obj 0) (q : E.obj 0) (r : G.obj 0)
    (hα : α.app 0 p = q) (hβ : β.app 0 q = r) :
    basedDiagramMap α p q hα ≫ basedDiagramMap β q r hβ =
      basedDiagramMap (α ≫ β) p r ((congrArg (β.app 0) hα).trans hβ) := by
  apply NatTrans.ext
  funext n
  apply PointedCGWH.pointedToCGWH.map_injective
  rfl

/-- At the actual image point the full map is the original diagram repointing. -/
theorem basedDiagramMap_image {D E : ℕ ⥤ CGWH.{u, v}}
    (α : D ⟶ E) (p : D.obj 0) :
    basedDiagramMap α p (α.app 0 p) rfl = diagramAtMap α p := by
  apply NatTrans.ext
  funext n
  apply PointedCGWH.pointedToCGWH.map_injective
  rfl

/-- An original whole carrier square retains its exact image-point repointed square. -/
theorem basedDiagramIso_map_square {D E D' E' : ℕ ⥤ CGWH.{u, v}}
    (e : D ≅ E) (e' : D' ≅ E') (α : D ⟶ D') (β : E ⟶ E')
    (sq : α ≫ e'.hom = e.hom ≫ β) (p : D.obj 0) :
    diagramAtMap α p ≫ (basedDiagramIso e' (α.app 0 p)).hom =
      (basedDiagramIso e p).hom ≫
        basedDiagramMap β (e.hom.app 0 p) (e'.hom.app 0 (α.app 0 p))
          ((ConcreteCategory.congr_hom (NatTrans.congr_app sq 0) p).symm) := by
  apply NatTrans.ext
  funext n
  apply PointedCGWH.pointedToCGWH.map_injective
  change α.app n ≫ e'.hom.app n = e.hom.app n ≫ β.app n
  exact NatTrans.congr_app sq n

/-- The original whole raw-to-loop isomorphism gives the all-point Type comparison. -/
def loopIsoTypeComparison {D : ℕ ⥤ CGWH.{u, v}} {E : ℕ ⥤ PointedCGWH.{u, v}}
    (e : D ≅ (E ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH)
    (p : D.obj 0) (k : ℕ) :
    diagramAt D p ⋙ PointedCGWH.piNFunctor k ≅
      E ⋙ PointedCGWH.piNFunctor (k + 1) :=
  Functor.isoWhiskerRight (basedDiagramIso e p) (PointedCGWH.piNFunctor k) ≪≫
    loopBasedTypeIso E (e.hom.app 0 p) k

/-- All actual input maps commute with that entire all-point raw-loop comparison. -/
theorem loopIsoTypeComparison_input_naturality
    {D D' : ℕ ⥤ CGWH.{u, v}} {E E' : ℕ ⥤ PointedCGWH.{u, v}}
    (e : D ≅ (E ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH)
    (e' : D' ≅ (E' ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH)
    (α : D ⟶ D') (β : E ⟶ E')
    (sq : α ≫ e'.hom = e.hom ≫
      Functor.whiskerRight (Functor.whiskerRight β PointedCGWH.loop)
        PointedCGWH.pointedToCGWH)
    (p : D.obj 0) (q : D'.obj 0) (h : α.app 0 p = q) (k : ℕ) :
    Functor.whiskerRight (basedDiagramMap α p q h) (PointedCGWH.piNFunctor k) ≫
        (loopIsoTypeComparison e' q k).hom =
      (loopIsoTypeComparison e p k).hom ≫
        Functor.whiskerRight β (PointedCGWH.piNFunctor (k + 1)) := by
  subst q
  rw [basedDiagramMap_image]
  let βL := Functor.whiskerRight (Functor.whiskerRight β PointedCGWH.loop)
    PointedCGWH.pointedToCGWH
  let pL := e.hom.app 0 p
  let qL := e'.hom.app 0 (α.app 0 p)
  have hL : (PointedCGWH.loop.map (β.app 0)).right pL = qL :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app sq 0) p).symm
  have hs : diagramAtMap α p ≫ (basedDiagramIso e' (α.app 0 p)).hom =
      (basedDiagramIso e p).hom ≫ loopBasedMap β pL qL hL := by
    apply NatTrans.ext
    funext n
    apply PointedCGWH.pointedToCGWH.map_injective
    change α.app n ≫ e'.hom.app n = e.hom.app n ≫ βL.app n
    exact NatTrans.congr_app sq n
  have hn := loopBasedTypeIso_input_naturality β pL qL hL k
  apply NatTrans.ext
  funext n
  have hπ :
      (PointedCGWH.piNFunctor k).map ((diagramAtMap α p).app n) ≫
          (PointedCGWH.piNFunctor k).map
            ((basedDiagramIso e' (α.app 0 p)).hom.app n) =
        (PointedCGWH.piNFunctor k).map ((basedDiagramIso e p).hom.app n) ≫
          (PointedCGWH.piNFunctor k).map ((loopBasedMap β pL qL hL).app n) := by
    simpa only [NatTrans.comp_app, CategoryTheory.Functor.map_comp] using
      (PointedCGWH.piNFunctor k).congr_map (NatTrans.congr_app hs n)
  change
    (PointedCGWH.piNFunctor k).map ((diagramAtMap α p).app n) ≫
      ((PointedCGWH.piNFunctor k).map
        ((basedDiagramIso e' (α.app 0 p)).hom.app n) ≫
          (loopBasedTypeIso E' qL k).hom.app n) =
      ((PointedCGWH.piNFunctor k).map ((basedDiagramIso e p).hom.app n) ≫
        (loopBasedTypeIso E pL k).hom.app n) ≫
          (PointedCGWH.piNFunctor (k + 1)).map (β.app n)
  have hn' := NatTrans.congr_app hn n
  change (PointedCGWH.piNFunctor k).map ((loopBasedMap β pL qL hL).app n) ≫
      (loopBasedTypeIso E' qL k).hom.app n =
      (loopBasedTypeIso E pL k).hom.app n ≫
        (PointedCGWH.piNFunctor (k + 1)).map (β.app n) at hn'
  rw [← Category.assoc, hπ, Category.assoc, hn', ← Category.assoc]

end ActualPoints

end PointedCGWH.Spectra.OriginalLoopTailAllPointComparison
