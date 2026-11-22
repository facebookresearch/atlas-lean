/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Functor.CoaugmentationIteration
import Mathlib.CategoryTheory.CommSq

/-!
# Evaluating the original-input coaugmentation sequence

An actual one-step comparison `R ⋙ E m ≅ E (m + 1) ⋙ L` determines every
source-ordered comparison `Rⁿ ⋙ E m ≅ E (m + n) ⋙ Lⁿ`. Its naturality at
the original arrow `η.app X` proves the transition square for `Rⁿ(η_X)`.

The target transition is constructed from that same coaugmentation,
one-step comparison and canonical reassociation. The square is a theorem;
it is not a supplied condition on a comparison or on the coaugmentation.
Both directions form an isomorphism of the complete natural-number
diagrams, natural in every original input arrow.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Functor.Iteration

namespace CategoryTheory.Functor.CoaugmentationEvaluation

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (R : C ⥤ C) (L : D ⥤ D) (E : ℕ → C ⥤ D)
  (e : ∀ m : ℕ, R ⋙ E m ≅ E (m + 1) ⋙ L)

/-- The same output functor power is canonically reassociated at every pair of indices. -/
def evaluationTail (n m : ℕ) :
    (E (m + n + 1) ⋙ L) ⋙ iterate L n ≅ E (m + (n + 1)) ⋙ iterate L (n + 1) :=
  Functor.associator (E (m + n + 1)) L (iterate L n) ≪≫
    Functor.isoWhiskerLeft (E (m + n + 1)) (iteratePrefixIso L n).symm ≪≫
    Functor.isoWhiskerRight
      (eqToIso (congrArg E (Nat.add_assoc m n 1))) (iterate L (n + 1))

/-- Every source-ordered comparison is built from the supplied whole one-step isomorphisms. -/
def comparison : ∀ n m : ℕ,
    iterate R n ⋙ E m ≅ E (m + n) ⋙ iterate L n
  | 0, m => (E m).leftUnitor ≪≫ (E m).rightUnitor.symm
  | n + 1, m =>
    Functor.isoWhiskerRight (iteratePrefixIso R n) (E m) ≪≫
      Functor.associator R (iterate R n) (E m) ≪≫
      Functor.isoWhiskerLeft R (comparison n m) ≪≫
      (Functor.associator R (E (m + n)) (iterate L n)).symm ≪≫
      Functor.isoWhiskerRight (e (m + n)) (iterate L n) ≪≫
      evaluationTail L E n m

/-- The original forward recursion retains the one-step maps and their source order. -/
theorem comparison_succ_hom_app (n m : ℕ) (X : C) :
    (comparison R L E e (n + 1) m).hom.app X =
      (E m).map ((iteratePrefixIso R n).hom.app X) ≫
        (comparison R L E e n m).hom.app (R.obj X) ≫
          (iterate L n).map ((e (m + n)).hom.app X) ≫
            (evaluationTail L E n m).hom.app X := by
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]

/-- The inverse recursion preserves the original inverse maps in the reverse composite order. -/
theorem comparison_succ_inv_app (n m : ℕ) (X : C) :
    (comparison R L E e (n + 1) m).inv.app X =
      (evaluationTail L E n m).inv.app X ≫
        (iterate L n).map ((e (m + n)).inv.app X) ≫
          (comparison R L E e n m).inv.app (R.obj X) ≫
            (E m).map ((iteratePrefixIso R n).inv.app X) := by
  simp only [comparison, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]

/-- The complete forward comparison is natural on every original input arrow. -/
theorem comparison_hom_naturality (n m : ℕ) {X Y : C} (f : X ⟶ Y) :
    (E m).map ((iterate R n).map f) ≫ (comparison R L E e n m).hom.app Y =
      (comparison R L E e n m).hom.app X ≫ (iterate L n).map ((E (m + n)).map f) :=
  (comparison R L E e n m).hom.naturality f

/-- The inverse comparison is natural on the same original whole input arrows. -/
theorem comparison_inv_naturality (n m : ℕ) {X Y : C} (f : X ⟶ Y) :
    (iterate L n).map ((E (m + n)).map f) ≫ (comparison R L E e n m).inv.app Y =
      (comparison R L E e n m).inv.app X ≫ (E m).map ((iterate R n).map f) :=
  (comparison R L E e n m).inv.naturality f

variable {R} (η : 𝟭 C ⟶ R)

/-- The compared one-step coaugmentation is the actual evaluation of its original input map. -/
def coordinate (m : ℕ) : E m ⟶ E (m + 1) ⋙ L :=
  (E m).leftUnitor.inv ≫ Functor.whiskerRight η (E m) ≫ (e m).hom

/-- The whole coordinate consists of the original evaluated coaugmentation and one-step map. -/
theorem coordinate_app (m : ℕ) (X : C) :
    (coordinate L E e η m).app X = (E m).map (η.app X) ≫ (e m).hom.app X := by
  simp only [coordinate, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Category.id_comp]

/-- Every original input arrow is natural for the actual compared one-step coaugmentation. -/
theorem coordinate_naturality (m : ℕ) {X Y : C} (f : X ⟶ Y) :
    (E m).map f ≫ (coordinate L E e η m).app Y =
      (coordinate L E e η m).app X ≫ L.map ((E (m + 1)).map f) :=
  (coordinate L E e η m).naturality f

/-- The target transition uses the original compared coordinate and the same canonical power. -/
def diagonalTransition (n m : ℕ) :
    E (m + n) ⋙ iterate L n ⟶ E (m + (n + 1)) ⋙ iterate L (n + 1) :=
  Functor.whiskerRight (coordinate L E e η (m + n)) (iterate L n) ≫
    (evaluationTail L E n m).hom

/-- Every target transition retains the actual output-functor image of the compared coordinate. -/
theorem diagonalTransition_app (n m : ℕ) (X : C) :
    (diagonalTransition L E e η n m).app X =
      (iterate L n).map ((coordinate L E e η (m + n)).app X) ≫
        (evaluationTail L E n m).hom.app X := rfl

/-- The entire actual original-input transition square follows from comparison naturality. -/
theorem inputTransition_square (n m : ℕ) (X : C) :
    (E m).map ((inputTransition η n).app X) ≫
        (comparison R L E e (n + 1) m).hom.app X =
      (comparison R L E e n m).hom.app X ≫
        (diagonalTransition L E e η n m).app X := by
  rw [comparison_succ_hom_app]
  change (E m).map ((iterate R n).map (η.app X) ≫ (iteratePrefixIso R n).inv.app X) ≫
      ((E m).map ((iteratePrefixIso R n).hom.app X) ≫
        (comparison R L E e n m).hom.app (R.obj X) ≫
          (iterate L n).map ((e (m + n)).hom.app X) ≫
            (evaluationTail L E n m).hom.app X) = _
  rw [(E m).map_comp]
  have hc : (E m).map ((iteratePrefixIso R n).inv.app X) ≫
      (E m).map ((iteratePrefixIso R n).hom.app X) = 𝟙 _ := by
    rw [← (E m).map_comp, Iso.inv_hom_id_app, (E m).map_id]
  simp only [Category.assoc]
  rw [← Category.assoc ((E m).map ((iteratePrefixIso R n).inv.app X))
    ((E m).map ((iteratePrefixIso R n).hom.app X)), hc, Category.id_comp]
  rw [← Category.assoc, ← Category.assoc, comparison_hom_naturality R L E e n m (η.app X)]
  rw [diagonalTransition_app, coordinate_app, (iterate L n).map_comp]
  simp only [Category.assoc]
  rfl

/-- The inverse transition square follows for those same original source and target maps. -/
theorem inputTransition_square_inv (n m : ℕ) (X : C) :
    (diagonalTransition L E e η n m).app X ≫
        (comparison R L E e (n + 1) m).inv.app X =
      (comparison R L E e n m).inv.app X ≫ (E m).map ((inputTransition η n).app X) :=
  (CommSq.vert_inv (g := (comparison R L E e n m).app X)
    (h := (comparison R L E e (n + 1) m).app X)
    ⟨inputTransition_square L E e η n m X⟩).w

variable (P : ℕ → ℕ → C ⥤ D)
  (b : ∀ n m : ℕ, E (m + n) ⋙ iterate L n ≅ P n m)

/-- A whole output identification retains the original recursive comparison in both directions. -/
def comparisonWithOutput (n m : ℕ) : iterate R n ⋙ E m ≅ P n m :=
  comparison R L E e n m ≪≫ b n m

/-- The compared transition uses exactly both maps of the given whole output identifications. -/
def transitionWithOutput (n m : ℕ) : P n m ⟶ P (n + 1) m :=
  (b n m).inv ≫ diagonalTransition L E e η n m ≫ (b (n + 1) m).hom

/-- The output transport square follows from the proved original-input transition square. -/
theorem inputTransition_output_square (n m : ℕ) (X : C) :
    (E m).map ((inputTransition η n).app X) ≫
        (comparisonWithOutput L E e P b (n + 1) m).hom.app X =
      (comparisonWithOutput L E e P b n m).hom.app X ≫
        (transitionWithOutput L E e η P b n m).app X := by
  have h := inputTransition_square L E e η n m X
  simp only [comparisonWithOutput, transitionWithOutput, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, h, Category.assoc]

/-- Both inverse output maps retain the same original input transition, with no extra square. -/
theorem inputTransition_output_square_inv (n m : ℕ) (X : C) :
    (transitionWithOutput L E e η P b n m).app X ≫
        (comparisonWithOutput L E e P b (n + 1) m).inv.app X =
      (comparisonWithOutput L E e P b n m).inv.app X ≫
        (E m).map ((inputTransition η n).app X) :=
  (CommSq.vert_inv (g := (comparisonWithOutput L E e P b n m).app X)
    (h := (comparisonWithOutput L E e P b (n + 1) m).app X)
    ⟨inputTransition_output_square L E e η P b n m X⟩).w

section MappedOutput

variable {A : Type u₃} [Category.{v₃} A] (Q : D ⥤ A)
  (T : ℕ → ℕ → C ⥤ A) (c : ∀ n m : ℕ, P n m ⋙ Q ≅ T n m)

/-- Mapping a source comparison retains the given full output comparison maps. -/
def comparisonWithMappedOutput (n m : ℕ) :
    (iterate R n ⋙ E m) ⋙ Q ≅ T n m :=
  Functor.isoWhiskerRight (comparisonWithOutput L E e P b n m) Q ≪≫ c n m

/-- The mapped output transition is the image of the same actual source-coordinate transition. -/
def transitionWithMappedOutput (n m : ℕ) : T n m ⟶ T (n + 1) m :=
  (c n m).inv ≫ Functor.whiskerRight (transitionWithOutput L E e η P b n m) Q ≫
    (c (n + 1) m).hom

/-- The original-input square remains proved after every whole output-functor comparison. -/
theorem inputTransition_mapped_output_square (n m : ℕ) (X : C) :
    Q.map ((E m).map ((inputTransition η n).app X)) ≫
        (comparisonWithMappedOutput L E e P b Q T c (n + 1) m).hom.app X =
      (comparisonWithMappedOutput L E e P b Q T c n m).hom.app X ≫
        (transitionWithMappedOutput L E e η P b Q T c n m).app X := by
  have h := congrArg Q.map (inputTransition_output_square L E e η P b n m X)
  simp only [Functor.map_comp] at h
  simp only [comparisonWithMappedOutput, transitionWithMappedOutput, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (c (n + 1) m).hom.app X) h).trans (Category.assoc _ _ _))

/-- Both inverse mapped comparison functions retain that same original-input square. -/
theorem inputTransition_mapped_output_square_inv (n m : ℕ) (X : C) :
    (transitionWithMappedOutput L E e η P b Q T c n m).app X ≫
        (comparisonWithMappedOutput L E e P b Q T c (n + 1) m).inv.app X =
      (comparisonWithMappedOutput L E e P b Q T c n m).inv.app X ≫
        Q.map ((E m).map ((inputTransition η n).app X)) :=
  (CommSq.vert_inv (g := (comparisonWithMappedOutput L E e P b Q T c n m).app X)
    (h := (comparisonWithMappedOutput L E e P b Q T c (n + 1) m).app X)
    ⟨inputTransition_mapped_output_square L E e η P b Q T c n m X⟩).w

/-- The full output diagram retains every actual mapped original-input transition. -/
def mappedOutputDiagram (m : ℕ) (X : C) : ℕ ⥤ A :=
  Functor.ofSequence (fun n => (transitionWithMappedOutput L E e η P b Q T c n m).app X)

/-- Every adjacent output arrow is the original complete mapped transition. -/
theorem mappedOutputDiagram_map_succ (m : ℕ) (X : C) (n : ℕ) :
    (mappedOutputDiagram L E e η P b Q T c m X).map (homOfLE (Nat.le_succ n)) =
      (transitionWithMappedOutput L E e η P b Q T c n m).app X :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- Both comparison directions identify the entire mapped original-input diagrams. -/
def diagramIsoWithMappedOutput (m : ℕ) (X : C) :
    inputDiagram η X ⋙ E m ⋙ Q ≅ mappedOutputDiagram L E e η P b Q T c m X where
  hom := NatTrans.ofSequence
    (fun n => (comparisonWithMappedOutput L E e P b Q T c n m).hom.app X) (fun n => by
      change Q.map ((E m).map ((inputDiagram η X).map (homOfLE (Nat.le_succ n)))) ≫
        (comparisonWithMappedOutput L E e P b Q T c (n + 1) m).hom.app X = _
      exact (congrArg (fun q => Q.map ((E m).map q) ≫
        (comparisonWithMappedOutput L E e P b Q T c (n + 1) m).hom.app X)
          (inputDiagram_map_succ η X n)).trans
            ((inputTransition_mapped_output_square L E e η P b Q T c n m X).trans
              (congrArg (fun q =>
                (comparisonWithMappedOutput L E e P b Q T c n m).hom.app X ≫ q)
                  (mappedOutputDiagram_map_succ L E e η P b Q T c m X n).symm)))
  inv := NatTrans.ofSequence
    (fun n => (comparisonWithMappedOutput L E e P b Q T c n m).inv.app X) (fun n => by
      exact (congrArg (fun q => q ≫
        (comparisonWithMappedOutput L E e P b Q T c (n + 1) m).inv.app X)
          (mappedOutputDiagram_map_succ L E e η P b Q T c m X n)).trans
            ((inputTransition_mapped_output_square_inv L E e η P b Q T c n m X).trans
              (congrArg (fun q =>
                (comparisonWithMappedOutput L E e P b Q T c n m).inv.app X ≫
                  Q.map ((E m).map q)) (inputDiagram_map_succ η X n).symm)))
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    exact (comparisonWithMappedOutput L E e P b Q T c n m).hom_inv_id_app X
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    exact (comparisonWithMappedOutput L E e P b Q T c n m).inv_hom_id_app X

/-- Every forward mapped diagram component is the same full original output comparison. -/
theorem diagramIsoWithMappedOutput_hom_app (m : ℕ) (X : C) (n : ℕ) :
    (diagramIsoWithMappedOutput L E e η P b Q T c m X).hom.app n =
      (comparisonWithMappedOutput L E e P b Q T c n m).hom.app X := rfl

/-- Every inverse mapped component retains the same original inverse output comparison. -/
theorem diagramIsoWithMappedOutput_inv_app (m : ℕ) (X : C) (n : ℕ) :
    (diagramIsoWithMappedOutput L E e η P b Q T c m X).inv.app n =
      (comparisonWithMappedOutput L E e P b Q T c n m).inv.app X := rfl

end MappedOutput

/-- The complete target diagram uses every actual compared original-input coordinate. -/
def diagonalDiagram (m : ℕ) (X : C) : ℕ ⥤ D :=
  Functor.ofSequence (fun n => (diagonalTransition L E e η n m).app X)

/-- Every target stage retains the supplied evaluated input and the actual output power. -/
theorem diagonalDiagram_obj (m : ℕ) (X : C) (n : ℕ) :
    (diagonalDiagram L E e η m X).obj n = (iterate L n).obj ((E (m + n)).obj X) := rfl

/-- Each adjacent target arrow is its actual compared original-input transition. -/
theorem diagonalDiagram_map_succ (m : ℕ) (X : C) (n : ℕ) :
    (diagonalDiagram L E e η m X).map (homOfLE (Nat.le_succ n)) =
      (diagonalTransition L E e η n m).app X :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- Every original input map gives the actual full diagonal diagram map. -/
def diagonalDiagramMap (m : ℕ) {X Y : C} (f : X ⟶ Y) :
    diagonalDiagram L E e η m X ⟶ diagonalDiagram L E e η m Y :=
  NatTrans.ofSequence (fun n => (iterate L n).map ((E (m + n)).map f)) (fun n => by
    rw [diagonalDiagram_map_succ, diagonalDiagram_map_succ]
    exact ((diagonalTransition L E e η n m).naturality f).symm)

/-- The complete compared diagram preserves all original input identities and composites. -/
def diagonalDiagramFunctor (m : ℕ) : C ⥤ (ℕ ⥤ D) where
  obj := diagonalDiagram L E e η m
  map := diagonalDiagramMap L E e η m
  map_id X := by
    apply NatTrans.ext
    funext n
    exact ((E (m + n) ⋙ iterate L n).map_id X)
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact ((E (m + n) ⋙ iterate L n).map_comp f g)

/-- Both comparison maps form an isomorphism of the whole original-input diagrams. -/
def diagramIso (m : ℕ) (X : C) :
    inputDiagram η X ⋙ E m ≅ diagonalDiagram L E e η m X where
  hom := NatTrans.ofSequence (fun n => (comparison R L E e n m).hom.app X) (fun n => by
    change (E m).map ((inputDiagram η X).map (homOfLE (Nat.le_succ n))) ≫
        (comparison R L E e (n + 1) m).hom.app X = _
    rw [inputDiagram_map_succ, diagonalDiagram_map_succ]
    exact inputTransition_square L E e η n m X)
  inv := NatTrans.ofSequence (fun n => (comparison R L E e n m).inv.app X) (fun n => by
    rw [diagonalDiagram_map_succ]
    change _ = (comparison R L E e n m).inv.app X ≫
      (E m).map ((inputDiagram η X).map (homOfLE (Nat.le_succ n)))
    rw [inputDiagram_map_succ]
    exact inputTransition_square_inv L E e η n m X)
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    exact (comparison R L E e n m).hom_inv_id_app X
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    exact (comparison R L E e n m).inv_hom_id_app X

/-- Every forward diagram component is precisely the original recursive comparison. -/
theorem diagramIso_hom_app (m : ℕ) (X : C) (n : ℕ) :
    (diagramIso L E e η m X).hom.app n = (comparison R L E e n m).hom.app X := rfl

/-- Every inverse diagram component retains that same original recursive inverse. -/
theorem diagramIso_inv_app (m : ℕ) (X : C) (n : ℕ) :
    (diagramIso L E e η m X).inv.app n = (comparison R L E e n m).inv.app X := rfl

/-- The forward comparison retains every nonadjacent original natural-number map. -/
theorem diagramIso_hom_naturality (m : ℕ) (X : C) {i j : ℕ} (f : i ⟶ j) :
    (E m).map ((inputDiagram η X).map f) ≫ (comparison R L E e j m).hom.app X =
      (comparison R L E e i m).hom.app X ≫ (diagonalDiagram L E e η m X).map f :=
  (diagramIso L E e η m X).hom.naturality f

/-- The inverse comparison retains those same complete natural-number maps. -/
theorem diagramIso_inv_naturality (m : ℕ) (X : C) {i j : ℕ} (f : i ⟶ j) :
    (diagonalDiagram L E e η m X).map f ≫ (comparison R L E e j m).inv.app X =
      (comparison R L E e i m).inv.app X ≫ (E m).map ((inputDiagram η X).map f) :=
  (diagramIso L E e η m X).inv.naturality f

/-- The entire evaluated diagram comparison is natural in every original input arrow. -/
def diagramNatIso (m : ℕ) :
    inputDiagramFunctor η ⋙ (whiskeringRight ℕ C D).obj (E m) ≅
      diagonalDiagramFunctor L E e η m :=
  NatIso.ofComponents (diagramIso L E e η m) (fun {X Y} f => by
    apply NatTrans.ext
    funext n
    exact comparison_hom_naturality R L E e n m f)

end CategoryTheory.Functor.CoaugmentationEvaluation
