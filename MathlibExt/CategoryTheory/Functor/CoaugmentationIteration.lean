/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Functor.Iteration
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Iterating a natural coaugmentation on its original input

For an endofunctor `F` and a natural map `η : 𝟭 C ⟶ F`, the transition in the
sequence considered here is `Fⁿ.map (η.app X)`. The target is reassociated by
the equality of the complete original iterates. No equation between
`F.map (η.app X)` and `η.app (F.obj X)` is required.

The construction retains every stage and every arrow of the natural-number
diagram, its functoriality in the original input, and transport through an
isomorphism of endofunctors. All transport maps are the canonical maps of the
same given functors.
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory

namespace CategoryTheory.Functor.Iteration

variable {C : Type u} [Category.{v} C]

/-- Powers of the same endofunctor associate as complete functors. -/
theorem iterate_add (F : C ⥤ C) (n m : ℕ) :
    iterate F (n + m) = iterate F n ⋙ iterate F m := by
  induction m with
  | zero => rfl
  | succ m hm =>
    exact congrArg (fun G : C ⥤ C => G ⋙ F) hm

/-- Prefixing a power by its original endofunctor gives the same successor power. -/
theorem iterate_succ_prefix (F : C ⥤ C) (n : ℕ) :
    iterate F (n + 1) = F ⋙ iterate F n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    exact congrArg (fun G : C ⥤ C => G ⋙ F) hn

/-- The equality of complete powers supplies both canonical association maps. -/
def iterateAddIso (F : C ⥤ C) (n m : ℕ) :
    iterate F (n + m) ≅ iterate F n ⋙ iterate F m :=
  eqToIso (iterate_add F n m)

/-- The exact prefix association of the same endofunctor, in both directions. -/
def iteratePrefixIso (F : C ⥤ C) (n : ℕ) :
    iterate F (n + 1) ≅ F ⋙ iterate F n :=
  eqToIso (iterate_succ_prefix F n)

/-- The forward association is the object transport of the complete functor equality. -/
theorem iterateAddIso_hom_app (F : C ⥤ C) (n m : ℕ) (X : C) :
    (iterateAddIso F n m).hom.app X =
      eqToHom (Functor.congr_obj (iterate_add F n m) X) :=
  eqToHom_app (iterate_add F n m) X

/-- The inverse association retains the inverse of that same object transport. -/
theorem iterateAddIso_inv_app (F : C ⥤ C) (n m : ℕ) (X : C) :
    (iterateAddIso F n m).inv.app X =
      eqToHom (Functor.congr_obj (iterate_add F n m).symm X) :=
  eqToHom_app (iterate_add F n m).symm X

/-- The forward prefix map keeps the original complete object equality. -/
theorem iteratePrefixIso_hom_app (F : C ⥤ C) (n : ℕ) (X : C) :
    (iteratePrefixIso F n).hom.app X =
      eqToHom (Functor.congr_obj (iterate_succ_prefix F n) X) :=
  eqToHom_app (iterate_succ_prefix F n) X

/-- The inverse prefix map keeps the inverse complete object equality. -/
theorem iteratePrefixIso_inv_app (F : C ⥤ C) (n : ℕ) (X : C) :
    (iteratePrefixIso F n).inv.app X =
      eqToHom (Functor.congr_obj (iterate_succ_prefix F n).symm X) :=
  eqToHom_app (iterate_succ_prefix F n).symm X

/-- Reassociation commutes with every original input arrow. -/
theorem iteratePrefixIso_hom_naturality (F : C ⥤ C) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    (iterate F (n + 1)).map f ≫ (iteratePrefixIso F n).hom.app Y =
      (iteratePrefixIso F n).hom.app X ≫ (iterate F n).map (F.map f) :=
  (iteratePrefixIso F n).hom.naturality f

/-- The inverse reassociation commutes with those same whole input arrows. -/
theorem iteratePrefixIso_inv_naturality (F : C ⥤ C) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    (iterate F n).map (F.map f) ≫ (iteratePrefixIso F n).inv.app Y =
      (iteratePrefixIso F n).inv.app X ≫ (iterate F (n + 1)).map f :=
  (iteratePrefixIso F n).inv.naturality f

/-- Iterating the coaugmentation of the original input gives the actual transition. -/
def inputTransition {F : C ⥤ C} (η : 𝟭 C ⟶ F) (n : ℕ) :
    iterate F n ⟶ iterate F (n + 1) where
  app X := (iterate F n).map (η.app X) ≫ (iteratePrefixIso F n).inv.app X
  naturality {X Y} f :=
    (Functor.whiskerRight η (iterate F n) ≫ (iteratePrefixIso F n).inv).naturality f

/-- Every transition is the original iterated arrow followed by canonical reassociation. -/
theorem inputTransition_app {F : C ⥤ C} (η : 𝟭 C ⟶ F) (n : ℕ) (X : C) :
    (inputTransition η n).app X =
      (iterate F n).map (η.app X) ≫
        eqToHom (Functor.congr_obj (iterate_succ_prefix F n).symm X) := by
  change (iterate F n).map (η.app X) ≫ (iteratePrefixIso F n).inv.app X = _
  rw [iteratePrefixIso_inv_app]

/-- No original input morphism is lost in the coaugmentation transition. -/
theorem inputTransition_naturality {F : C ⥤ C} (η : 𝟭 C ⟶ F) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    (iterate F n).map f ≫ (inputTransition η n).app Y =
      (inputTransition η n).app X ≫ (iterate F (n + 1)).map f :=
  (inputTransition η n).naturality f

/-- Stage zero has precisely the original natural coaugmentation. -/
theorem inputTransition_zero {F : C ⥤ C} (η : 𝟭 C ⟶ F) :
    inputTransition η 0 = η := by
  apply NatTrans.ext
  funext X
  change η.app X ≫ 𝟙 _ = η.app X
  exact Category.comp_id _

private theorem prefix_inv_succ (F : C ⥤ C) (n : ℕ) (X : C) :
    (iteratePrefixIso F (n + 1)).inv.app X =
      F.map ((iteratePrefixIso F n).inv.app X) := by
  rw [iteratePrefixIso_inv_app, iteratePrefixIso_inv_app, eqToHom_map]
  rfl

/-- Applying the original endofunctor produces the next original-input transition. -/
theorem inputTransition_succ_app {F : C ⥤ C} (η : 𝟭 C ⟶ F) (n : ℕ) (X : C) :
    (inputTransition η (n + 1)).app X = F.map ((inputTransition η n).app X) := by
  exact (congrArg (fun r => F.map ((iterate F n).map (η.app X)) ≫ r)
    (prefix_inv_succ F n X)).trans
      (F.map_comp ((iterate F n).map (η.app X))
        ((iteratePrefixIso F n).inv.app X)).symm

/-- The entire successor transition is the functor image of the preceding transition. -/
theorem inputTransition_succ {F : C ⥤ C} (η : 𝟭 C ⟶ F) (n : ℕ) :
    inputTransition η (n + 1) = Functor.whiskerRight (inputTransition η n) F := by
  apply NatTrans.ext
  funext X
  exact inputTransition_succ_app η n X

/-- The full natural-number diagram uses every actual original-input transition. -/
def inputDiagram {F : C ⥤ C} (η : 𝟭 C ⟶ F) (X : C) : ℕ ⥤ C :=
  Functor.ofSequence (fun n => (inputTransition η n).app X)

/-- Every stage is the original complete endofunctor power. -/
theorem inputDiagram_obj {F : C ⥤ C} (η : 𝟭 C ⟶ F) (X : C) (n : ℕ) :
    (inputDiagram η X).obj n = (iterate F n).obj X := rfl

/-- Every adjacent arrow is the original coaugmentation iterated on its original input. -/
theorem inputDiagram_map_succ {F : C ⥤ C} (η : 𝟭 C ⟶ F) (X : C) (n : ℕ) :
    (inputDiagram η X).map (homOfLE (Nat.le_add_right n 1)) =
      (inputTransition η n).app X :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- Every original input arrow gives a natural transformation of the complete diagrams. -/
def inputDiagramMap {F : C ⥤ C} (η : 𝟭 C ⟶ F) {X Y : C} (f : X ⟶ Y) :
    inputDiagram η X ⟶ inputDiagram η Y :=
  NatTrans.ofSequence (fun n => (iterate F n).map f) (fun n => by
    rw [inputDiagram_map_succ, inputDiagram_map_succ]
    exact (inputTransition_naturality η n f).symm)

/-- The diagram construction preserves all input identities and compositions. -/
def inputDiagramFunctor {F : C ⥤ C} (η : 𝟭 C ⟶ F) : C ⥤ (ℕ ⥤ C) where
  obj := inputDiagram η
  map := inputDiagramMap η
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (iterate F n).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (iterate F n).map_comp f g

/-- The action on an original input arrow is its actual iterate at each stage. -/
theorem inputDiagramFunctor_map_app {F : C ⥤ C} (η : 𝟭 C ⟶ F)
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((inputDiagramFunctor η).map f).app n = (iterate F n).map f := rfl

/-- The diagonal naturality equation applies to every natural-number arrow. -/
theorem inputDiagramMap_naturality {F : C ⥤ C} (η : 𝟭 C ⟶ F)
    {X Y : C} (f : X ⟶ Y) {n m : ℕ} (a : n ⟶ m) :
    (inputDiagram η X).map a ≫ (iterate F m).map f =
      (iterate F n).map f ≫ (inputDiagram η Y).map a :=
  (inputDiagramMap η f).naturality a

/-- An isomorphism of original endofunctors gives the complete iterated comparison. -/
def iterateIso {F G : C ⥤ C} (e : F ≅ G) :
    ∀ n : ℕ, iterate F n ≅ iterate G n :=
  Nat.rec (Iso.refl (𝟭 C)) (fun n previous =>
    Functor.isoWhiskerRight previous F ≪≫
      Functor.isoWhiskerLeft (iterate G n) e)

/-- The forward successor comparison retains the original functor image and original iso. -/
theorem iterateIso_succ_hom_app {F G : C ⥤ C} (e : F ≅ G) (n : ℕ) (X : C) :
    (iterateIso e (n + 1)).hom.app X =
      F.map ((iterateIso e n).hom.app X) ≫ e.hom.app ((iterate G n).obj X) := rfl

/-- The inverse successor comparison retains the same inverse maps in their original order. -/
theorem iterateIso_succ_inv_app {F G : C ⥤ C} (e : F ≅ G) (n : ℕ) (X : C) :
    (iterateIso e (n + 1)).inv.app X =
      e.inv.app ((iterate G n).obj X) ≫ F.map ((iterateIso e n).inv.app X) := rfl

/-- The full forward iterated comparison is natural in every original input arrow. -/
theorem iterateIso_hom_naturality {F G : C ⥤ C} (e : F ≅ G) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    (iterate F n).map f ≫ (iterateIso e n).hom.app Y =
      (iterateIso e n).hom.app X ≫ (iterate G n).map f :=
  (iterateIso e n).hom.naturality f

/-- The full inverse iterated comparison is natural on those same arrows. -/
theorem iterateIso_inv_naturality {F G : C ⥤ C} (e : F ≅ G) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    (iterate G n).map f ≫ (iterateIso e n).inv.app Y =
      (iterateIso e n).inv.app X ≫ (iterate F n).map f :=
  (iterateIso e n).inv.naturality f

set_option backward.isDefEq.respectTransparency false in
/-- The original-input transitions commute with the full iterated comparison. -/
theorem inputTransition_iterateIso {F G : C ⥤ C} (e : F ≅ G)
    (η : 𝟭 C ⟶ F) (n : ℕ) (X : C) :
    (inputTransition η n).app X ≫ (iterateIso e (n + 1)).hom.app X =
      (iterateIso e n).hom.app X ≫ (inputTransition (η ≫ e.hom) n).app X := by
  induction n with
  | zero =>
    rw [inputTransition_zero, inputTransition_zero]
    change η.app X ≫ (F.map (𝟙 X) ≫ e.hom.app X) =
      𝟙 X ≫ (η.app X ≫ e.hom.app X)
    rw [F.map_id, Category.id_comp, Category.id_comp]
  | succ n hn =>
    have ht := inputTransition_succ_app η n X
    have hu := inputTransition_succ_app (η ≫ e.hom) n X
    have he := iterateIso_succ_hom_app e (n + 1) X
    have he' := iterateIso_succ_hom_app e n X
    have hNat := e.hom.naturality ((inputTransition (η ≫ e.hom) n).app X)
    calc
      (inputTransition η (n + 1)).app X ≫ (iterateIso e (n + 1 + 1)).hom.app X =
          F.map ((inputTransition η n).app X) ≫
            (F.map ((iterateIso e (n + 1)).hom.app X) ≫
              e.hom.app ((iterate G (n + 1)).obj X)) :=
        congrArg₂ (fun a b => a ≫ b) ht he
      _ = F.map ((inputTransition η n).app X ≫
            (iterateIso e (n + 1)).hom.app X) ≫
              e.hom.app ((iterate G (n + 1)).obj X) :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun a => a ≫ e.hom.app ((iterate G (n + 1)).obj X))
            (F.map_comp _ _).symm)
      _ = F.map ((iterateIso e n).hom.app X ≫
            (inputTransition (η ≫ e.hom) n).app X) ≫
              e.hom.app ((iterate G (n + 1)).obj X) :=
        congrArg (fun a => F.map a ≫ e.hom.app ((iterate G (n + 1)).obj X)) hn
      _ = F.map ((iterateIso e n).hom.app X) ≫
            (F.map ((inputTransition (η ≫ e.hom) n).app X) ≫
              e.hom.app ((iterate G (n + 1)).obj X)) :=
        (congrArg (fun a => a ≫ e.hom.app ((iterate G (n + 1)).obj X))
          (F.map_comp _ _)).trans (Category.assoc _ _ _)
      _ = F.map ((iterateIso e n).hom.app X) ≫
            (e.hom.app ((iterate G n).obj X) ≫
              G.map ((inputTransition (η ≫ e.hom) n).app X)) :=
        congrArg (fun a => F.map ((iterateIso e n).hom.app X) ≫ a) hNat
      _ = (iterateIso e (n + 1)).hom.app X ≫
            (inputTransition (η ≫ e.hom) (n + 1)).app X :=
        (Category.assoc _ _ _).symm.trans
          (congrArg₂ (fun a b => a ≫ b) he'.symm hu.symm)

/-- The complete inverse comparison commutes with the same original-input transitions. -/
theorem inputTransition_iterateIso_inv {F G : C ⥤ C} (e : F ≅ G)
    (η : 𝟭 C ⟶ F) (n : ℕ) (X : C) :
    (inputTransition (η ≫ e.hom) n).app X ≫ (iterateIso e (n + 1)).inv.app X =
      (iterateIso e n).inv.app X ≫ (inputTransition η n).app X := by
  apply (cancel_epi ((iterateIso e n).hom.app X)).mp
  have h := congrArg (fun t => t ≫ (iterateIso e (n + 1)).inv.app X)
    (inputTransition_iterateIso e η n X)
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Iso.hom_inv_id_app_assoc] using h.symm

/-- Both comparison maps form an isomorphism of the whole original-input diagrams. -/
def inputDiagramIso {F G : C ⥤ C} (e : F ≅ G) (η : 𝟭 C ⟶ F) (X : C) :
    inputDiagram η X ≅ inputDiagram (η ≫ e.hom) X where
  hom := NatTrans.ofSequence (fun n => (iterateIso e n).hom.app X) (fun n => by
    rw [inputDiagram_map_succ, inputDiagram_map_succ]
    exact inputTransition_iterateIso e η n X)
  inv := NatTrans.ofSequence (fun n => (iterateIso e n).inv.app X) (fun n => by
    rw [inputDiagram_map_succ, inputDiagram_map_succ]
    exact inputTransition_iterateIso_inv e η n X)
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    exact (iterateIso e n).hom_inv_id_app X
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    exact (iterateIso e n).inv_hom_id_app X

/-- Every diagram component is precisely the original complete iterated forward map. -/
theorem inputDiagramIso_hom_app {F G : C ⥤ C} (e : F ≅ G)
    (η : 𝟭 C ⟶ F) (X : C) (n : ℕ) :
    (inputDiagramIso e η X).hom.app n = (iterateIso e n).hom.app X := rfl

/-- Every inverse component keeps the same original complete inverse map. -/
theorem inputDiagramIso_inv_app {F G : C ⥤ C} (e : F ≅ G)
    (η : 𝟭 C ⟶ F) (X : C) (n : ℕ) :
    (inputDiagramIso e η X).inv.app n = (iterateIso e n).inv.app X := rfl

/-- The isomorphism of complete diagrams is natural in every original input object. -/
def inputDiagramNatIso {F G : C ⥤ C} (e : F ≅ G) (η : 𝟭 C ⟶ F) :
    inputDiagramFunctor η ≅ inputDiagramFunctor (η ≫ e.hom) :=
  NatIso.ofComponents (inputDiagramIso e η) (fun {X Y} f => by
    apply NatTrans.ext
    funext n
    exact iterateIso_hom_naturality e n f)

section CurrentStage

variable {F : C ⥤ C} (η : 𝟭 C ⟶ F)

/-- The current-stage transition is the original coaugmentation at that stage. -/
def currentTransition (n : ℕ) : iterate F n ⟶ iterate F (n + 1) where
  app X := η.app ((iterate F n).obj X)
  naturality {_X _Y} f := η.naturality ((iterate F n).map f)

/-- The complete diagram uses the coaugmentation on each actual current stage. -/
def currentDiagram (X : C) : ℕ ⥤ C :=
  Functor.ofSequence (fun n => (currentTransition η n).app X)

/-- Every current-stage object remains the original endofunctor power. -/
theorem currentDiagram_obj (X : C) (n : ℕ) :
    (currentDiagram η X).obj n = (iterate F n).obj X := rfl

/-- Every adjacent map retains the actual current-stage coaugmentation. -/
theorem currentDiagram_map_succ (X : C) (n : ℕ) :
    (currentDiagram η X).map (homOfLE (Nat.le_succ n)) =
      η.app ((iterate F n).obj X) :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- Each original input map is retained at every current stage. -/
def currentDiagramMap {X Y : C} (f : X ⟶ Y) :
    currentDiagram η X ⟶ currentDiagram η Y :=
  NatTrans.ofSequence (fun n => (iterate F n).map f) (fun n => by
    rw [currentDiagram_map_succ, currentDiagram_map_succ]
    exact (η.naturality ((iterate F n).map f)).symm)

/-- The current-stage construction preserves the original identities and composites. -/
def currentDiagramFunctor : C ⥤ (ℕ ⥤ C) where
  obj := currentDiagram η
  map := currentDiagramMap η
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (iterate F n).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (iterate F n).map_comp f g

/-- Every component is the original iterated input map. -/
theorem currentDiagramMap_app {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (currentDiagramMap η f).app n = (iterate F n).map f := rfl

/-- Nonadjacent maps retain the original whole naturality square. -/
theorem currentDiagramMap_naturality {X Y : C} (f : X ⟶ Y)
    {n m : ℕ} (q : n ⟶ m) :
    (currentDiagram η X).map q ≫ (iterate F m).map f =
      (iterate F n).map f ≫ (currentDiagram η Y).map q :=
  (currentDiagramMap η f).naturality q

end CurrentStage

end CategoryTheory.Functor.Iteration
