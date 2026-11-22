/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.FiniteCube
public import MathlibExt.CategoryTheory.Monoidal.MonoidWordPushoutUniversalProperty
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Associative word attachments

The old coefficient in an associative word is its original monoid object.
Right actions at the final old factor make every contraction of an old
letter an actual map, with the original monoid multiplication.
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.MonoidWordPushout

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A right action of the original monoid, retaining both action laws. -/
structure RightModule (A : Mon C) where
  /-- Its original carrier. -/
  X : C
  /-- The original right action. -/
  act : X ⊗ A.X ⟶ X
  /-- Acting by the original unit gives the right unitor. -/
  act_one : (X ◁ A.mon.one) ≫ act = (ρ_ X).hom
  /-- The original multiplication acts associatively. -/
  act_assoc : (X ◁ A.mon.mul) ≫ act =
    (α_ X A.X A.X).inv ≫ (act ▷ A.X) ≫ act

namespace RightModule

variable {A : Mon C}

/-- A map preserving the actual right action. -/
@[ext]
structure Hom (M N : RightModule A) where
  /-- Its original carrier map. -/
  hom : M.X ⟶ N.X
  /-- The full original action square. -/
  act_hom : M.act ≫ hom = (hom ▷ A.X) ≫ N.act

/-- The original identity action map. -/
def id (M : RightModule A) : Hom M M where
  hom := 𝟙 M.X
  act_hom := by simp

/-- Composition retains the full original action square. -/
def comp {M N P : RightModule A} (f : Hom M N) (g : Hom N P) : Hom M P where
  hom := f.hom ≫ g.hom
  act_hom := by
    rw [← Category.assoc, f.act_hom, Category.assoc, g.act_hom, ← Category.assoc,
      ← comp_whiskerRight]

instance : Category (RightModule A) where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

@[simp] theorem id_hom (M : RightModule A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := rfl

@[simp] theorem comp_hom {M N P : RightModule A} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The original regular right action, including the original unit and multiplication. -/
def regular (A : Mon C) : RightModule A where
  X := A.X
  act := A.mon.mul
  act_one := A.mon.mul_one
  act_assoc := MonObj.mul_assoc_flip A.X

/-- Free right action on the final old coefficient. -/
def freeAct (A : Mon C) (X : C) : (X ⊗ A.X) ⊗ A.X ⟶ X ⊗ A.X :=
  (α_ X A.X A.X).hom ≫ X ◁ A.mon.mul

/-- The final original old coefficient has its actual unital right action. -/
theorem freeAct_one (A : Mon C) (X : C) :
    ((X ⊗ A.X) ◁ A.mon.one) ≫ freeAct A X = (ρ_ (X ⊗ A.X)).hom := by
  dsimp [freeAct]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp, A.mon.mul_one]
  monoidal

/-- Multiplying adjacent original old coefficients gives an associative right action. -/
theorem freeAct_assoc (A : Mon C) (X : C) :
    ((X ⊗ A.X) ◁ A.mon.mul) ≫ freeAct A X =
      (α_ (X ⊗ A.X) A.X A.X).inv ≫ (freeAct A X ▷ A.X) ≫ freeAct A X := by
  dsimp [freeAct]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp, MonObj.mul_assoc_flip A.X]
  simp only [whiskerLeft_comp]
  rw [associator_naturality_middle_assoc]
  monoidal

/-- The free right action on an arbitrary original prefix. -/
abbrev free (A : Mon C) (X : C) : RightModule A where
  X := X ⊗ A.X
  act := freeAct A X
  act_one := freeAct_one A X
  act_assoc := freeAct_assoc A X

/-- The original free right action preserves every map of prefixes. -/
def freeMap {X Y : C} (f : X ⟶ Y) : free A X ⟶ free A Y where
  hom := f ▷ A.X
  act_hom := by
    dsimp [free, freeAct]
    simp only [Category.assoc]
    rw [whisker_exchange, ← associator_naturality_left_assoc]

@[simp] theorem freeMap_hom {X Y : C} (f : X ⟶ Y) :
    (freeMap (A := A) f).hom = f ▷ A.X := rfl

@[simp] theorem freeMap_id (X : C) : freeMap (A := A) (𝟙 X) = 𝟙 (free A X) := by
  apply Hom.ext
  exact id_whiskerRight _ _

@[simp] theorem freeMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    freeMap (A := A) (f ≫ g) = freeMap f ≫ freeMap g := by
  apply Hom.ext
  exact comp_whiskerRight f g A.X

/-- The actual free right action functor. -/
def freeFunctor (A : Mon C) : C ⥤ RightModule A where
  obj := free A
  map := freeMap
  map_id := freeMap_id
  map_comp := freeMap_comp

/-- Extend an original prefix map by the actual right action. -/
def lift (M : RightModule A) {X : C} (f : X ⟶ M.X) : free A X ⟶ M where
  hom := (f ▷ A.X) ≫ M.act
  act_hom := by
    dsimp [free, freeAct]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc, M.act_assoc]
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_inv_naturality_left_assoc]
    simp

/-- The extension retains its actual original action formula. -/
@[simp] theorem lift_hom (M : RightModule A) {X : C} (f : X ⟶ M.X) :
    (lift M f).hom = (f ▷ A.X) ≫ M.act := rfl

/-- Original free extensions commute with every original right action map. -/
theorem lift_naturality {M N : RightModule A} (g : M ⟶ N) {X : C} (f : X ⟶ M.X) :
    lift M f ≫ g = lift N (f ≫ g.hom) := by
  apply Hom.ext
  dsimp [lift]
  rw [Category.assoc, g.act_hom, ← Category.assoc, ← comp_whiskerRight]

/-- Free extension respects every original source map. -/
theorem freeMap_lift {X Y : C} (g : X ⟶ Y) (M : RightModule A) (f : Y ⟶ M.X) :
    freeMap g ≫ lift M f = lift M (g ≫ f) := by
  apply Hom.ext
  dsimp [freeMap, lift]
  rw [comp_whiskerRight, Category.assoc]

/-- Carrier maps retain the original transport of an equality of complete right actions. -/
theorem eqToHom_hom {M N : RightModule A} (h : M = N) :
    (eqToHom h : M ⟶ N).hom = eqToHom (congrArg RightModule.X h) := by
  cases h
  rfl

/-- Appending one actual new slot keeps an original old coefficient at its end. -/
abbrev snoc (M : RightModule A) (X : C) : RightModule A := free A (M.X ⊗ X)

/-- Append original maps without changing either original tensor factor. -/
def snocMap {M N : RightModule A} (f : M ⟶ N) {X Y : C} (g : X ⟶ Y) :
    snoc M X ⟶ snoc N Y := freeMap (f.hom ⊗ₘ g)

@[simp] theorem snocMap_hom {M N : RightModule A} (f : M ⟶ N) {X Y : C} (g : X ⟶ Y) :
    (snocMap f g).hom = (f.hom ⊗ₘ g) ▷ A.X := rfl

@[simp] theorem snocMap_id (M : RightModule A) (X : C) :
    snocMap (𝟙 M) (𝟙 X) = 𝟙 (snoc M X) := by
  apply Hom.ext
  simp only [snocMap_hom, id_hom, id_tensorHom_id, id_whiskerRight]

/-- Appending maps respects composition in both original variables. -/
theorem snocMap_comp {M N P : RightModule A} (f : M ⟶ N) (g : N ⟶ P)
    {X Y Z : C} (h : X ⟶ Y) (k : Y ⟶ Z) :
    snocMap (f ≫ g) (h ≫ k) = snocMap f h ≫ snocMap g k := by
  apply Hom.ext
  simp only [snocMap_hom, comp_hom]
  rw [← tensorHom_comp_tensorHom, comp_whiskerRight]

/-- Append an unchanged original letter to the composite of original prefix maps. -/
theorem snocMap_comp_id {M N P : RightModule A} (f : M ⟶ N) (g : N ⟶ P) (X : C) :
    snocMap (f ≫ g) (𝟙 X) = snocMap f (𝟙 X) ≫ snocMap g (𝟙 X) := by
  simpa only [Category.id_comp] using snocMap_comp f g (𝟙 X) (𝟙 X)

/-- Appending an identity letter retains the exact transport of the original prefix. -/
theorem snocMap_eqToHom {M N : RightModule A} (h : M = N) (X : C) :
    snocMap (eqToHom h) (𝟙 X) = eqToHom (congrArg (fun Q => snoc Q X) h) := by
  cases h
  exact snocMap_id M X

/-- Collapse one actual old letter through its original attaching value,
then multiply both adjacent original old coefficients. -/
def collapseLast (M : RightModule A) {X : C} (k : X ⟶ A.X) : snoc M X ⟶ M :=
  lift M ((M.X ◁ k) ≫ M.act)

/-- The actual two adjacent old multiplications, with all original tensor maps. -/
@[simp] theorem collapseLast_hom (M : RightModule A) {X : C} (k : X ⟶ A.X) :
    (collapseLast M k).hom = ((M.X ◁ k) ▷ A.X) ≫ (M.act ▷ A.X) ≫ M.act := by
  dsimp [collapseLast, lift]
  rw [comp_whiskerRight, Category.assoc]

/-- Collapsing an actual old letter commutes with every preceding original word map. -/
theorem collapseLast_naturality {M N : RightModule A} (g : M ⟶ N)
    {X : C} (k : X ⟶ A.X) :
    snocMap g (𝟙 X) ≫ collapseLast N k = collapseLast M k ≫ g := by
  have h : (g.hom ▷ X) ≫ (N.X ◁ k) ≫ N.act =
      ((M.X ◁ k) ≫ M.act) ≫ g.hom := by
    rw [← whisker_exchange_assoc, Category.assoc, ← g.act_hom, ← Category.assoc]
  have hs : snocMap g (𝟙 X) = freeMap (g.hom ▷ X) := by
    apply Hom.ext
    dsimp [snocMap, freeMap]
    rw [tensorHom_id]
  rw [hs]
  dsimp only [collapseLast]
  rw [freeMap_lift, h, ← lift_naturality]

/-- Restrict the original monoid's right multiplication along an actual monoid map. -/
abbrev restrict (M : Mon C) (a : A ⟶ M) : RightModule A where
  X := M.X
  act := (M.X ◁ a.hom) ≫ M.mon.mul
  act_one := by
    rw [← Category.assoc, ← whiskerLeft_comp, IsMonHom.one_hom, M.mon.mul_one]
  act_assoc := by
    rw [← Category.assoc, ← whiskerLeft_comp, IsMonHom.mul_hom]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [MonObj.mul_assoc_flip M.X]
    simp only [tensorHom_def, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc]
    rw [whisker_exchange_assoc]

/-- The actual old monoid map is a map of its original regular right action. -/
def ofMonHom (M : Mon C) (a : A ⟶ M) : regular A ⟶ restrict M a where
  hom := a.hom
  act_hom := by
    change A.mon.mul ≫ a.hom = (a.hom ▷ A.X) ≫ (M.X ◁ a.hom) ≫ M.mon.mul
    rw [IsMonHom.mul_hom, tensorHom_def, Category.assoc]

end RightModule

/-- A literal ordered word of old (`false`) and new (`true`) letter slots. -/
inductive Word where
  /-- The degree-zero word still has its original old coefficient. -/
  | nil : Word
  /-- Append one original letter slot in its original position. -/
  | snoc : Word → Bool → Word
  deriving DecidableEq

namespace Word

/-- The original number of letter slots. -/
def length : Word → ℕ
  | nil => 0
  | snoc w _ => w.length + 1

/-- The original number of retained new letter slots. -/
def kept : Word → ℕ
  | nil => 0
  | snoc w false => w.kept
  | snoc w true => w.kept + 1

/-- Remove precisely the old letter slots, in the original order. -/
def reduced : Word → Word
  | nil => nil
  | snoc w false => w.reduced
  | snoc w true => snoc w.reduced true

/-- The complete original word with exactly `n` new letter slots. -/
def allNew : ℕ → Word
  | 0 => nil
  | n + 1 => snoc (allNew n) true

/-- Reduction has exactly the original retained new letter slots. -/
theorem reduced_eq (w : Word) : w.reduced = allNew w.kept := by
  induction w with
  | nil => rfl
  | snoc w b ih => cases b <;> simp only [reduced, kept, allNew, ih]

@[simp] theorem length_allNew (n : ℕ) : (allNew n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allNew, length, ih]

@[simp] theorem kept_allNew (n : ℕ) : (allNew n).kept = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allNew, kept, ih]

@[simp] theorem reduced_allNew (n : ℕ) : (allNew n).reduced = allNew n := by
  rw [reduced_eq, kept_allNew]

end Word

/-- Literal alternating tensor words with the original regular coefficient at degree zero. -/
abbrev wordModule (A : Mon C) (K L : C) : Word → RightModule A
  | .nil => RightModule.regular A
  | .snoc w b => RightModule.snoc (wordModule A K L w) (if b then L else K)

/-- The actual original word carrier, including all of its old coefficient factors. -/
abbrev wordObj (A : Mon C) (K L : C) (w : Word) : C := (wordModule A K L w).X

/-- The actual original full word carrier of `n` new letters. -/
abbrev newWordObj (A : Mon C) (L : C) (n : ℕ) : C := wordObj A L L (Word.allNew n)

theorem wordObj_nil (A : Mon C) (K L : C) : wordObj A K L .nil = A.X := rfl

/-- Appending retains the original letter and the original final old coefficient. -/
theorem wordObj_snoc (A : Mon C) (K L : C) (w : Word) (b : Bool) :
    wordObj A K L (.snoc w b) = (wordObj A K L w ⊗ (if b then L else K)) ⊗ A.X := rfl

/-- The degree-zero full new-word carrier is precisely the original monoid carrier. -/
@[simp] theorem newWordObj_zero (A : Mon C) (L : C) : newWordObj A L 0 = A.X := rfl

/-- Every positive full new word appends one actual new letter and one actual old coefficient. -/
@[simp] theorem newWordObj_succ (A : Mon C) (L : C) (n : ℕ) :
    newWordObj A L (n + 1) = (newWordObj A L n ⊗ L) ⊗ A.X := rfl

/-- Collapse every actual old letter through its original attaching value,
multiplying adjacent original old coefficients in their original order. -/
def wordReduction (A : Mon C) {K L : C} (k : K ⟶ A.X) :
    (w : Word) → wordModule A K L w ⟶ wordModule A K L w.reduced
  | .nil => 𝟙 _
  | .snoc w false =>
    RightModule.snocMap (wordReduction A k w) (𝟙 K) ≫
      RightModule.collapseLast (wordModule A K L w.reduced) k
  | .snoc w true => RightModule.snocMap (wordReduction A k w) (𝟙 L)

/-- The degree-zero contraction is the original identity of the old monoid. -/
@[simp] theorem wordReduction_nil (A : Mon C) {K L : C} (k : K ⟶ A.X) :
    (wordReduction A (L := L) k .nil).hom = 𝟙 A.X := rfl

/-- An original new letter is retained, including its adjacent original coefficient. -/
@[simp] theorem wordReduction_new (A : Mon C) {K L : C} (k : K ⟶ A.X) (w : Word) :
    (wordReduction A (L := L) k (.snoc w true)).hom =
      ((wordReduction A k w).hom ▷ L) ▷ A.X := by
  change ((wordReduction A (L := L) k w).hom ⊗ₘ 𝟙 L) ▷ A.X = _
  rw [tensorHom_id]

/-- An original old letter is mapped through the original attaching value,
then the two adjacent original old multiplications are performed. -/
@[simp] theorem wordReduction_old (A : Mon C) {K L : C} (k : K ⟶ A.X) (w : Word) :
    (wordReduction A (L := L) k (.snoc w false)).hom =
      (((wordReduction A k w).hom ▷ K) ▷ A.X) ≫
        ((wordObj A K L w.reduced ◁ k) ▷ A.X) ≫
          ((wordModule A K L w.reduced).act ▷ A.X) ≫
            (wordModule A K L w.reduced).act := by
  change (RightModule.snocMap (wordReduction A (L := L) k w) (𝟙 K)).hom ≫
    (RightModule.collapseLast (wordModule A K L w.reduced) k).hom = _
  simp only [RightModule.snocMap_hom, tensorHom_id, RightModule.collapseLast_hom]

/-- Every full new word has precisely the identity reduction,
with its original carrier transport retained. -/
theorem wordReduction_allNew (A : Mon C) {K L : C} (k : K ⟶ A.X) (n : ℕ) :
    wordReduction A (L := L) k (Word.allNew n) =
      eqToHom (congrArg (wordModule A K L) (Word.reduced_allNew n).symm) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RightModule.snocMap (wordReduction A (L := L) k (Word.allNew n)) (𝟙 L) = _
    rw [ih, RightModule.snocMap_eqToHom]
    rfl

namespace Word

/-- The literal subset word in the original increasing order of its original finite positions. -/
def ofSubset : {n : ℕ} → FiniteCube.Index n → Word
  | 0, _ => .nil
  | n + 1, S => .snoc (ofSubset (FiniteCube.«prefix» S)) (decide (Fin.last n ∈ S))

/-- The full original subset word contains exactly its original selected positions. -/
theorem kept_ofSubset : ∀ {n : ℕ} (S : FiniteCube.Index n), (ofSubset S).kept = S.card
  | 0, S => by
    have hs : S = ∅ := Finset.eq_empty_of_isEmpty S
    rw [hs]
    rfl
  | n + 1, S => by
    rw [FiniteCube.card_eq_prefix]
    by_cases h : Fin.last n ∈ S
    · simp only [ofSubset, h, decide_true, kept, kept_ofSubset, ite_true]
    · simp only [ofSubset, h, decide_false, kept, kept_ofSubset, ite_false, Nat.add_zero]

/-- The original terminal subset is precisely the original complete new-letter word. -/
@[simp] theorem ofSubset_univ (n : ℕ) :
    ofSubset (Finset.univ : FiniteCube.Index n) = allNew n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ofSubset, FiniteCube.prefix_univ, Finset.mem_univ, decide_true, ih, allNew]

end Word

/-- Literal original alternating word vertices, with precisely `n+1` original monoid factors. -/
abbrev literalVertex (A : Mon C) (K L : C) {n : ℕ} (S : FiniteCube.Index n) : C :=
  FiniteCube.alternatingObj (fun _ : Fin (n + 1) => A.X)
    (FiniteCube.vertexFamily (fun _ : Fin n => K) (fun _ => L) S)

/-- The complete original associative word cube uses precisely the original arrow in every new face. -/
def wordCube (A : Mon C) {K L : C} (f : K ⟶ L) (n : ℕ) : FiniteCube.Index n ⥤ C :=
  FiniteCube.alternatingCube (fun _ : Fin (n + 1) => A.X) (fun _ : Fin n => f)

/-- Every original cube vertex has the literal original alternating carrier. -/
@[simp] theorem wordCube_obj (A : Mon C) {K L : C} (f : K ⟶ L) (n : ℕ) (S : FiniteCube.Index n) :
    (wordCube A f n).obj S = literalVertex A K L S := rfl

/-- All original cube faces retain the original arrow and all original identity coefficient maps. -/
@[simp] theorem wordCube_map (A : Mon C) {K L : C} (f : K ⟶ L) (n : ℕ)
    {S T : FiniteCube.Index n} (h : S ⟶ T) :
    (wordCube A f n).map h =
      FiniteCube.alternatingMap (fun _ : Fin (n + 1) => 𝟙 A.X)
        (FiniteCube.familyMap (fun _ : Fin n => f) (leOfHom h)) := rfl

/-- The literal zero-letter cube vertex is the original monoid carrier. -/
@[simp] theorem literalVertex_zero (A : Mon C) (K L : C) (S : FiniteCube.Index 0) :
    literalVertex A K L S = A.X := rfl

/-- The recursive word action carrier is exactly the literal original subset cube carrier. -/
theorem literalVertex_eq_word (A : Mon C) (K L : C) :
    ∀ {n : ℕ} (S : FiniteCube.Index n), literalVertex A K L S = wordObj A K L (Word.ofSubset S)
  | 0, _ => rfl
  | n + 1, S => by
    have hx : (fun i : Fin n =>
        FiniteCube.vertexFamily (fun _ : Fin (n + 1) => K) (fun _ => L) S i.castSucc) =
        FiniteCube.vertexFamily (fun _ : Fin n => K) (fun _ => L) (FiniteCube.«prefix» S) := by
      funext i
      simp only [FiniteCube.vertexFamily, FiniteCube.mem_prefix]
    change ((FiniteCube.alternatingObj (fun _ : Fin (n + 1) => A.X)
      (fun i : Fin n => FiniteCube.vertexFamily (fun _ : Fin (n + 1) => K) (fun _ => L) S i.castSucc) ⊗
        FiniteCube.vertexFamily (fun _ : Fin (n + 1) => K) (fun _ => L) S (Fin.last n)) ⊗ A.X) = _
    rw [hx]
    have ih := literalVertex_eq_word A K L (FiniteCube.«prefix» S)
    dsimp only [literalVertex] at ih
    rw [ih]
    by_cases h : Fin.last n ∈ S
    · simp only [Word.ofSubset, h, decide_true, FiniteCube.vertexFamily, ite_true]
      rfl
    · simp only [Word.ofSubset, h, decide_false, FiniteCube.vertexFamily, ite_false]
      rfl

/-- The complete new word is independent of the unused old-letter carrier, preserving all factors. -/
theorem wordObj_allNew (A : Mon C) (K L : C) (n : ℕ) :
    wordObj A K L (Word.allNew n) = newWordObj A L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (wordObj A K L (Word.allNew n) ⊗ L) ⊗ A.X = (newWordObj A L n ⊗ L) ⊗ A.X
    rw [ih]

/-- Reduction retains exactly the original selected new letters and their original adjacent coefficients. -/
theorem reducedVertex_eq (A : Mon C) (K L : C) {n : ℕ} (S : FiniteCube.Index n) :
    wordObj A K L (Word.ofSubset S).reduced = newWordObj A L S.card := by
  rw [Word.reduced_eq, Word.kept_ofSubset, wordObj_allNew]

/-- Collapse every original old letter of every original subset face through its actual attaching map,
then multiply adjacent original old coefficients before entering its actual earlier full word. -/
def vertexCollapse (A : Mon C) {K L : C} (k : K ⟶ A.X) {n : ℕ} (S : FiniteCube.Index n) :
    literalVertex A K L S ⟶ newWordObj A L S.card :=
  eqToHom (literalVertex_eq_word A K L S) ≫ (wordReduction A (L := L) k (Word.ofSubset S)).hom ≫
    eqToHom (reducedVertex_eq A K L S)

/-- An original face relation records the discarded old slots and each retained old or new slot. -/
inductive Mask where
  /-- The original degree-zero relation. -/
  | nil : Mask
  /-- An original old slot outside the selected target subset. -/
  | drop : Mask → Mask
  /-- An original target-selected slot, old (`false`) or new (`true`) at the source. -/
  | keep : Mask → Bool → Mask
  deriving DecidableEq

namespace Mask

/-- The complete original source subset word. -/
def sourceWord : Mask → Word
  | .nil => .nil
  | .drop m => .snoc m.sourceWord false
  | .keep m b => .snoc m.sourceWord b

/-- The complete original target subset word. -/
def fullWord : Mask → Word
  | .nil => .nil
  | .drop m => .snoc m.fullWord false
  | .keep m _ => .snoc m.fullWord true

/-- The actual retained source slots, in their original order. -/
def selectedWord : Mask → Word
  | .nil => .nil
  | .drop m => m.selectedWord
  | .keep m b => .snoc m.selectedWord b

/-- The original number of selected target slots. -/
def count : Mask → ℕ
  | .nil => 0
  | .drop m => m.count
  | .keep m _ => m.count + 1

/-- The retained source slots have precisely the target subset's original size. -/
theorem selected_length (m : Mask) : m.selectedWord.length = m.count := by
  induction m with
  | nil => rfl
  | drop m ih => exact ih
  | keep m b ih => exact congrArg (· + 1) ih

/-- Removing the discarded slots retains exactly the original new-letter slots. -/
theorem selected_reduced (m : Mask) : m.selectedWord.reduced = m.sourceWord.reduced := by
  induction m with
  | nil => rfl
  | drop m ih => exact ih
  | keep m b ih => cases b <;> simp only [selectedWord, sourceWord, Word.reduced, ih]

/-- The original selected target has precisely its original selected slot count. -/
theorem full_kept (m : Mask) : m.fullWord.kept = m.count := by
  induction m with
  | nil => rfl
  | drop m ih => exact ih
  | keep m b ih => exact congrArg (· + 1) ih

end Mask

/-- Collapse exactly the original old slots outside the selected target subset. -/
def partialCollapse (A : Mon C) {K L : C} (k : K ⟶ A.X) : (m : Mask) →
    wordModule A K L m.sourceWord ⟶ wordModule A K L m.selectedWord
  | .nil => 𝟙 _
  | .drop m => RightModule.snocMap (partialCollapse A k m) (𝟙 K) ≫
    RightModule.collapseLast (wordModule A K L m.selectedWord) k
  | .keep m false => RightModule.snocMap (partialCollapse A k m) (𝟙 K)
  | .keep m true => RightModule.snocMap (partialCollapse A k m) (𝟙 L)

/-- Reduction of retained slots, with the complete original source reduction as its actual target. -/
def selectedReduction (A : Mon C) {K L : C} (k : K ⟶ A.X) : (m : Mask) →
    wordModule A K L m.selectedWord ⟶ wordModule A K L m.sourceWord.reduced
  | .nil => 𝟙 _
  | .drop m => selectedReduction A k m
  | .keep m false => RightModule.snocMap (selectedReduction A k m) (𝟙 K) ≫
    RightModule.collapseLast (wordModule A K L m.sourceWord.reduced) k
  | .keep m true => RightModule.snocMap (selectedReduction A k m) (𝟙 L)

/-- Collapsing the unselected old slots and then all retained old slots is the full original collapse. -/
theorem partialCollapse_reduction (A : Mon C) {K L : C} (k : K ⟶ A.X) : ∀ (m : Mask),
    partialCollapse A (L := L) k m ≫ selectedReduction A k m = wordReduction A k m.sourceWord
  | .nil => Category.id_comp _
  | .drop m => by
    change (RightModule.snocMap (partialCollapse A (L := L) k m) (𝟙 K) ≫
      RightModule.collapseLast (wordModule A K L m.selectedWord) k) ≫ selectedReduction A k m =
        RightModule.snocMap (wordReduction A k m.sourceWord) (𝟙 K) ≫
          RightModule.collapseLast (wordModule A K L m.sourceWord.reduced) k
    rw [Category.assoc, ← RightModule.collapseLast_naturality, ← Category.assoc,
      ← RightModule.snocMap_comp, Category.id_comp, partialCollapse_reduction A k m]
  | .keep m false => by
    change RightModule.snocMap (partialCollapse A (L := L) k m) (𝟙 K) ≫
      (RightModule.snocMap (selectedReduction A k m) (𝟙 K) ≫
        RightModule.collapseLast (wordModule A K L m.sourceWord.reduced) k) =
      RightModule.snocMap (wordReduction A k m.sourceWord) (𝟙 K) ≫
        RightModule.collapseLast (wordModule A K L m.sourceWord.reduced) k
    rw [← Category.assoc, ← RightModule.snocMap_comp, Category.id_comp, partialCollapse_reduction A k m]
  | .keep m true => by
    change RightModule.snocMap (partialCollapse A (L := L) k m) (𝟙 L) ≫
      RightModule.snocMap (selectedReduction A k m) (𝟙 L) =
        RightModule.snocMap (wordReduction A k m.sourceWord) (𝟙 L)
    rw [← RightModule.snocMap_comp, Category.id_comp, partialCollapse_reduction A k m]

/-- The original face map changes exactly the retained old slots by the original arrow. -/
def faceMap (A : Mon C) {K L : C} (f : K ⟶ L) : (m : Mask) →
    wordModule A K L m.sourceWord ⟶ wordModule A K L m.fullWord
  | .nil => 𝟙 _
  | .drop m => RightModule.snocMap (faceMap A f m) (𝟙 K)
  | .keep m false => RightModule.snocMap (faceMap A f m) f
  | .keep m true => RightModule.snocMap (faceMap A f m) (𝟙 L)

/-- The same original face map on the retained actual source slots. -/
def selectedFaceMap (A : Mon C) {K L : C} (f : K ⟶ L) : (m : Mask) →
    wordModule A K L m.selectedWord ⟶ wordModule A K L (Word.allNew m.count)
  | .nil => 𝟙 _
  | .drop m => selectedFaceMap A f m
  | .keep m false => RightModule.snocMap (selectedFaceMap A f m) f
  | .keep m true => RightModule.snocMap (selectedFaceMap A f m) (𝟙 L)

/-- Collapse precisely the original target's remaining old slots. -/
def fullCollapse (A : Mon C) {K L : C} (k : K ⟶ A.X) : (m : Mask) →
    wordModule A K L m.fullWord ⟶ wordModule A K L (Word.allNew m.count)
  | .nil => 𝟙 _
  | .drop m => RightModule.snocMap (fullCollapse A k m) (𝟙 K) ≫
    RightModule.collapseLast (wordModule A K L (Word.allNew m.count)) k
  | .keep m false => RightModule.snocMap (fullCollapse A k m) (𝟙 L)
  | .keep m true => RightModule.snocMap (fullCollapse A k m) (𝟙 L)

/-- Removing the same original unselected old slots commutes with the entire original face map. -/
theorem partialCollapse_face (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : ∀ (m : Mask),
    partialCollapse A (L := L) k m ≫ selectedFaceMap A f m = faceMap A f m ≫ fullCollapse A k m
  | .nil => rfl
  | .drop m => by
    change (RightModule.snocMap (partialCollapse A (L := L) k m) (𝟙 K) ≫
      RightModule.collapseLast (wordModule A K L m.selectedWord) k) ≫ selectedFaceMap A f m =
      RightModule.snocMap (faceMap A f m) (𝟙 K) ≫
        (RightModule.snocMap (fullCollapse A k m) (𝟙 K) ≫
          RightModule.collapseLast (wordModule A K L (Word.allNew m.count)) k)
    rw [Category.assoc, ← RightModule.collapseLast_naturality, ← Category.assoc,
      ← RightModule.snocMap_comp, Category.id_comp, partialCollapse_face A k f m]
    simpa only [Category.id_comp, Category.assoc] using
      congrArg (fun z => z ≫ RightModule.collapseLast (wordModule A K L (Word.allNew m.count)) k)
        (RightModule.snocMap_comp (faceMap A f m) (fullCollapse A k m) (𝟙 K) (𝟙 K))
  | .keep m false => by
    change RightModule.snocMap (partialCollapse A (L := L) k m) (𝟙 K) ≫
      RightModule.snocMap (selectedFaceMap A f m) f =
        RightModule.snocMap (faceMap A f m) f ≫ RightModule.snocMap (fullCollapse A k m) (𝟙 L)
    rw [← RightModule.snocMap_comp, ← RightModule.snocMap_comp, Category.id_comp, Category.comp_id,
      partialCollapse_face A k f m]
  | .keep m true => by
    change RightModule.snocMap (partialCollapse A (L := L) k m) (𝟙 L) ≫
      RightModule.snocMap (selectedFaceMap A f m) (𝟙 L) =
        RightModule.snocMap (faceMap A f m) (𝟙 L) ≫ RightModule.snocMap (fullCollapse A k m) (𝟙 L)
    rw [← RightModule.snocMap_comp, ← RightModule.snocMap_comp, Category.id_comp,
      partialCollapse_face A k f m]

namespace Mask

/-- The target face reduces precisely to its actual original full new word. -/
theorem full_reduced (m : Mask) : m.fullWord.reduced = Word.allNew m.count := by
  rw [Word.reduced_eq, full_kept]

end Mask

/-- The retained-slot reduction is the actual word reduction with its original target transport. -/
theorem selectedReduction_eq (A : Mon C) {K L : C} (k : K ⟶ A.X) : ∀ (m : Mask),
    selectedReduction A (L := L) k m = wordReduction A k m.selectedWord ≫
      eqToHom (congrArg (wordModule A K L) m.selected_reduced)
  | .nil => (Category.comp_id _).symm
  | .drop m => selectedReduction_eq A k m
  | .keep m false => by
    change RightModule.snocMap (selectedReduction A (L := L) k m) (𝟙 K) ≫
        RightModule.collapseLast (wordModule A K L m.sourceWord.reduced) k =
      (RightModule.snocMap (wordReduction A k m.selectedWord) (𝟙 K) ≫
        RightModule.collapseLast (wordModule A K L m.selectedWord.reduced) k) ≫
          eqToHom (congrArg (wordModule A K L) (Mask.selected_reduced (.keep m false)))
    rw [selectedReduction_eq A k m, RightModule.snocMap_comp_id, Category.assoc,
      RightModule.collapseLast_naturality, ← Category.assoc]
    rfl
  | .keep m true => by
    change RightModule.snocMap (selectedReduction A (L := L) k m) (𝟙 L) =
      RightModule.snocMap (wordReduction A k m.selectedWord) (𝟙 L) ≫
        eqToHom (congrArg (wordModule A K L) (Mask.selected_reduced (.keep m true)))
    rw [selectedReduction_eq A k m, RightModule.snocMap_comp_id, RightModule.snocMap_eqToHom]
    rfl

/-- The target-slot collapse is the actual complete word reduction with its original target transport. -/
theorem fullCollapse_eq (A : Mon C) {K L : C} (k : K ⟶ A.X) : ∀ (m : Mask),
    fullCollapse A (L := L) k m = wordReduction A k m.fullWord ≫
      eqToHom (congrArg (wordModule A K L) m.full_reduced)
  | .nil => (Category.comp_id _).symm
  | .drop m => by
    change RightModule.snocMap (fullCollapse A (L := L) k m) (𝟙 K) ≫
        RightModule.collapseLast (wordModule A K L (Word.allNew m.count)) k =
      (RightModule.snocMap (wordReduction A k m.fullWord) (𝟙 K) ≫
        RightModule.collapseLast (wordModule A K L m.fullWord.reduced) k) ≫
          eqToHom (congrArg (wordModule A K L) (Mask.full_reduced (.drop m)))
    rw [fullCollapse_eq A k m, RightModule.snocMap_comp_id, Category.assoc,
      RightModule.collapseLast_naturality, ← Category.assoc]
    rfl
  | .keep m false => by
    change RightModule.snocMap (fullCollapse A (L := L) k m) (𝟙 L) =
      RightModule.snocMap (wordReduction A k m.fullWord) (𝟙 L) ≫
        eqToHom (congrArg (wordModule A K L) (Mask.full_reduced (.keep m false)))
    rw [fullCollapse_eq A k m, RightModule.snocMap_comp_id, RightModule.snocMap_eqToHom]
    rfl
  | .keep m true => by
    change RightModule.snocMap (fullCollapse A (L := L) k m) (𝟙 L) =
      RightModule.snocMap (wordReduction A k m.fullWord) (𝟙 L) ≫
        eqToHom (congrArg (wordModule A K L) (Mask.full_reduced (.keep m true)))
    rw [fullCollapse_eq A k m, RightModule.snocMap_comp_id, RightModule.snocMap_eqToHom]
    rfl

namespace Word

/-- The original new-letter count is bounded by the original total slot count. -/
theorem kept_le_length (w : Word) : w.kept ≤ w.length := by
  induction w with
  | nil => exact Nat.le_refl 0
  | snoc w b ih =>
    cases b with
    | false => exact ih.trans (Nat.le_succ _)
    | true => exact Nat.add_le_add_right ih 1

/-- The subset word retains every original slot, independently of which slots are selected. -/
theorem length_ofSubset : ∀ {n : ℕ} (S : FiniteCube.Index n), (ofSubset S).length = n
  | 0, _ => rfl
  | _n + 1, S => congrArg (· + 1) (length_ofSubset (FiniteCube.«prefix» S))

end Word

/-- The original face to the full new word changes every remaining original old letter by `f`. -/
def wordToNew (A : Mon C) {K L : C} (f : K ⟶ L) : (w : Word) →
    wordModule A K L w ⟶ wordModule A K L (Word.allNew w.length)
  | .nil => 𝟙 _
  | .snoc w false => RightModule.snocMap (wordToNew A f w) f
  | .snoc w true => RightModule.snocMap (wordToNew A f w) (𝟙 L)

/-- The original full-face map on actual carriers, with its original target transport. -/
def wordToNewHom (A : Mon C) {K L : C} (f : K ⟶ L) (w : Word) :
    wordObj A K L w ⟶ newWordObj A L w.length :=
  (wordToNew A f w).hom ≫ eqToHom (wordObj_allNew A K L w.length)

/-- The original reduced word has precisely the original new count and all its original coefficients. -/
theorem reducedWord_eq (A : Mon C) (K L : C) (w : Word) :
    wordObj A K L w.reduced = newWordObj A L w.kept :=
  (congrArg (wordObj A K L) w.reduced_eq).trans (wordObj_allNew A K L w.kept)

/-- The actual complete collapse enters the original full word of its original retained new count. -/
def wordReductionToNew (A : Mon C) {K L : C} (k : K ⟶ A.X) (w : Word) :
    wordObj A K L w ⟶ newWordObj A L w.kept :=
  (wordReduction A (L := L) k w).hom ≫ eqToHom (reducedWord_eq A K L w)

/-- An actual proper original word face occurring at or before an original stage. -/
structure CellFace (N : ℕ) where
  /-- Its complete original ordered old/new slot word. -/
  word : Word
  /-- Its original word stage bound. -/
  bound : word.length ≤ N
  /-- At least one original old letter remains on this actual punctured face. -/
  proper : word.kept < word.length

/-- There is no proper original zero-letter face. -/
instance zeroFaceIsEmpty : IsEmpty (CellFace 0) where
  false c := Nat.not_lt_zero _ (c.proper.trans_le c.bound)

namespace CellFace

/-- The same actual face occurs at every larger original stage. -/
def enlarge {N M : ℕ} (h : N ≤ M) (c : CellFace N) : CellFace M :=
  ⟨c.word, c.bound.trans h, c.proper⟩

end CellFace

section Stages

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair
local instance : HasColimitsOfShape ℕ C := HasColimitsOfShape.of_essentiallySmall C ℕ

/-- The actual finite coproduct of every original full word through the given original stage. -/
abbrev stageWords (A : Mon C) (L : C) (N : ℕ) : C :=
  ∐ fun i : Fin (N + 1) => newWordObj A L i.val

/-- The original full-word inclusion at the given original stage. -/
def stageWordι (A : Mon C) (L : C) (N j : ℕ) (h : j ≤ N) :
    newWordObj A L j ⟶ stageWords A L N :=
  Sigma.ι (fun i : Fin (N + 1) => newWordObj A L i.val) ⟨j, Nat.lt_succ_of_le h⟩

/-- The actual coproduct of all original proper word faces at the original stage. -/
abbrev stageFaces (A : Mon C) (K L : C) (N : ℕ) : C :=
  ∐ fun c : CellFace N => wordObj A K L c.word

/-- Every actual old-letter contraction enters its actual earlier full word. -/
def stageRelationLeft (A : Mon C) (L : C) {K : C} (k : K ⟶ A.X) (N : ℕ) :
    stageFaces A K L N ⟶ stageWords A L N :=
  Sigma.desc (fun c : CellFace N => wordReductionToNew A k c.word ≫
    stageWordι A L N c.word.kept (c.word.kept_le_length.trans c.bound))

/-- Every original proper face enters its original terminal word by the original arrow. -/
def stageRelationRight (A : Mon C) {K L : C} (f : K ⟶ L) (N : ℕ) :
    stageFaces A K L N ⟶ stageWords A L N :=
  Sigma.desc (fun c : CellFace N => wordToNewHom A f c.word ≫ stageWordι A L N c.word.length c.bound)

/-- The actual word-stage carrier imposes precisely the original proper word-face equations. -/
abbrev stage (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ) : C :=
  coequalizer (stageRelationLeft A L k N) (stageRelationRight A f N)

/-- The actual original full-word leg into its original word-stage carrier. -/
def stageWordLeg (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N j : ℕ) (h : j ≤ N) :
    newWordObj A L j ⟶ stage A k f N :=
  stageWordι A L N j h ≫ coequalizer.π (stageRelationLeft A L k N) (stageRelationRight A f N)

/-- Every actual original proper face satisfies its original contraction/full-face equation at that stage. -/
theorem stage_cell (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ) (c : CellFace N) :
    wordReductionToNew A k c.word ≫
        stageWordLeg A k f N c.word.kept (c.word.kept_le_length.trans c.bound) =
      wordToNewHom A f c.word ≫ stageWordLeg A k f N c.word.length c.bound := by
  have h := coequalizer.condition (stageRelationLeft A L k N) (stageRelationRight A f N)
  have h' := congrArg (fun t => Sigma.ι (fun d : CellFace N => wordObj A K L d.word) c ≫ t) h
  simpa only [stage, stageRelationLeft, stageRelationRight, stageWordLeg, Category.assoc,
    Sigma.ι_comp_desc_assoc] using h'

/-- The original zero stage has no nontrivial relation. -/
theorem stage_zero_relations (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    stageRelationLeft A L k 0 = stageRelationRight A f 0 := by
  apply Sigma.hom_ext
  intro c
  exact isEmptyElim c

/-- The original old monoid carrier is exactly the constructed zero-stage carrier up to its original colimit iso. -/
def stageZeroIso (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : stage A k f 0 ≅ A.X := by
  let q := coequalizer.π (stageRelationLeft A L k 0) (stageRelationRight A f 0)
  haveI : IsIso q := coequalizer.π_of_eq (stage_zero_relations A k f)
  exact (asIso q).symm ≪≫ coproductUniqueIso (fun i : Fin 1 => newWordObj A L i.val)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original zero-word inclusion is the inverse of the original zero-stage comparison. -/
theorem stageZeroIso_inv (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    (stageZeroIso A k f).inv = stageWordLeg A k f 0 0 (Nat.le_refl 0) := by
  dsimp only [stageZeroIso]
  rw [Iso.trans_inv, Iso.symm_inv, asIso_hom, coproductUniqueIso_inv]
  rfl

/-- Every actual original full-word leg jointly determines a map from its original stage. -/
theorem stage_hom_ext (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    {X : C} {g h : stage A k f N ⟶ X}
    (H : ∀ j (hj : j ≤ N), stageWordLeg A k f N j hj ≫ g = stageWordLeg A k f N j hj ≫ h) : g = h := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro i
  have hh := H i.val (Nat.le_of_lt_succ i.isLt)
  simpa only [stageWordLeg, stageWordι, Category.assoc] using hh

/-- The actual original stage-word coproduct maps to every larger actual stage. -/
def toLargerWords (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) {N M : ℕ} (h : N ≤ M) :
    stageWords A L N ⟶ stage A k f M :=
  Sigma.desc (fun i : Fin (N + 1) => stageWordLeg A k f M i.val ((Nat.le_of_lt_succ i.isLt).trans h))

/-- Every original full-word inclusion retains its same original word at the larger stage. -/
@[reassoc (attr := simp)] theorem stageWordι_toLargerWords (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) {N M : ℕ} (h : N ≤ M) (j : ℕ) (hj : j ≤ N) :
    stageWordι A L N j hj ≫ toLargerWords A k f h = stageWordLeg A k f M j (hj.trans h) :=
  Sigma.ι_comp_desc _ _

/-- The same original proper-face relations hold on every actual later stage. -/
theorem toLargerWords_relations (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L)
    {N M : ℕ} (h : N ≤ M) :
    stageRelationLeft A L k N ≫ toLargerWords A k f h =
      stageRelationRight A f N ≫ toLargerWords A k f h := by
  apply Sigma.hom_ext
  intro c
  simp only [stageRelationLeft, stageRelationRight, Sigma.ι_comp_desc_assoc, Category.assoc,
    stageWordι_toLargerWords]
  exact stage_cell A k f M (c.enlarge h)

/-- The actual transition between the two given original word stages. -/
def stageMap (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) {N M : ℕ} (h : N ≤ M) :
    stage A k f N ⟶ stage A k f M :=
  coequalizer.desc (toLargerWords A k f h) (toLargerWords_relations A k f h)

/-- Every original full-word leg is retained by each original word-stage transition. -/
@[reassoc (attr := simp)] theorem stageWordLeg_map (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) {N M : ℕ} (h : N ≤ M) (j : ℕ) (hj : j ≤ N) :
    stageWordLeg A k f N j hj ≫ stageMap A k f h = stageWordLeg A k f M j (hj.trans h) := by
  dsimp only [stageWordLeg, stageMap]
  rw [Category.assoc, coequalizer.π_desc, stageWordι_toLargerWords]
  rfl

/-- The actual word-stage transition at identity order is the original identity. -/
@[simp] theorem stageMap_id (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ) :
    stageMap A k f (Nat.le_refl N) = 𝟙 (stage A k f N) := by
  apply stage_hom_ext A k f N
  intro j hj
  rw [stageWordLeg_map, Category.comp_id]

/-- Every two original stage transitions compose to their original combined transition. -/
theorem stageMap_comp (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L)
    {N M P : ℕ} (h : N ≤ M) (h' : M ≤ P) :
    stageMap A k f h ≫ stageMap A k f h' = stageMap A k f (h.trans h') := by
  apply stage_hom_ext A k f N
  intro j hj
  rw [← Category.assoc, stageWordLeg_map, stageWordLeg_map, stageWordLeg_map]

/-- The constructed actual original countable word-stage diagram. -/
def stageDiagram (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : ℕ ⥤ C where
  obj N := stage A k f N
  map h := stageMap A k f (leOfHom h)
  map_id N := stageMap_id A k f N
  map_comp h h' := (stageMap_comp A k f (leOfHom h) (leOfHom h')).symm

/-- The actual countable underlying colimit of the constructed original word stages. -/
abbrev stageEndpoint (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : C :=
  colimit (stageDiagram A k f)

/-- The original leg of each original word stage into its actual countable endpoint. -/
def stageι (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ) :
    stage A k f N ⟶ stageEndpoint A k f := colimit.ι (stageDiagram A k f) N

/-- Every actual original transition retains its original endpoint leg. -/
@[reassoc (attr := simp)] theorem stageι_naturality (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) {N M : ℕ} (h : N ≤ M) :
    stageMap A k f h ≫ stageι A k f M = stageι A k f N :=
  colimit.w (stageDiagram A k f) (homOfLE h)

/-- The same original old monoid carrier enters the actual countable word-stage endpoint. -/
def rootMap (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : A.X ⟶ stageEndpoint A k f :=
  stageWordLeg A k f 0 0 (Nat.le_refl 0) ≫ stageι A k f 0

end Stages

/-- Evaluate the entire original alternating word through its original old monoid map,
original old-letter values, original new-letter values, and original target multiplication. -/
def evaluateWord (A M : Mon C) (b : A ⟶ M) {K L : C} (x : K ⟶ M.X) (g : L ⟶ M.X) :
    (w : Word) → wordModule A K L w ⟶ RightModule.restrict M b
  | .nil => RightModule.ofMonHom M b
  | .snoc w false => RightModule.lift (RightModule.restrict M b)
    (((evaluateWord A M b x g w).hom ⊗ₘ x) ≫ M.mon.mul)
  | .snoc w true => RightModule.lift (RightModule.restrict M b)
    (((evaluateWord A M b x g w).hom ⊗ₘ g) ≫ M.mon.mul)

/-- Evaluating a retained original letter commutes with an original prefix map. -/
theorem evaluate_snoc_precompose (A M : Mon C) (b : A ⟶ M) {P Q : RightModule A}
    (h : P ⟶ Q) {X : C} (e : Q.X ⟶ M.X) (g : X ⟶ M.X) :
    RightModule.snocMap h (𝟙 X) ≫
        RightModule.lift (RightModule.restrict M b) ((e ⊗ₘ g) ≫ M.mon.mul) =
      RightModule.lift (RightModule.restrict M b) (((h.hom ≫ e) ⊗ₘ g) ≫ M.mon.mul) := by
  dsimp only [RightModule.snocMap]
  rw [RightModule.freeMap_lift]
  congr 1
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

/-- Evaluating the original old-letter contraction uses exactly its original value under the old monoid map. -/
theorem evaluate_collapseLast (A M : Mon C) (b : A ⟶ M) {P : RightModule A}
    (e : P ⟶ RightModule.restrict M b) {K : C} (k : K ⟶ A.X) :
    RightModule.snocMap e (𝟙 K) ≫ RightModule.collapseLast (RightModule.restrict M b) k =
      RightModule.lift (RightModule.restrict M b) ((e.hom ⊗ₘ (k ≫ b.hom)) ≫ M.mon.mul) := by
  dsimp only [RightModule.snocMap, RightModule.collapseLast]
  rw [RightModule.freeMap_lift]
  congr 1
  simp only [RightModule.restrict, tensorHom_def, whiskerLeft_comp, whiskerLeft_id,
    Category.id_comp, Category.assoc]

/-- Every original old-letter contraction preserves the full original word evaluation. -/
theorem wordReduction_evaluate (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (g : L ⟶ M.X) : ∀ (w : Word),
    wordReduction A (L := L) k w ≫ evaluateWord A M b (k ≫ b.hom) g w.reduced =
      evaluateWord A M b (k ≫ b.hom) g w
  | .nil => Category.id_comp _
  | .snoc w false => by
    change (RightModule.snocMap (wordReduction A (L := L) k w) (𝟙 K) ≫
      RightModule.collapseLast (wordModule A K L w.reduced) k) ≫
        evaluateWord A M b (k ≫ b.hom) g w.reduced = _
    rw [Category.assoc, ← RightModule.collapseLast_naturality, ← Category.assoc,
      ← RightModule.snocMap_comp, Category.id_comp, wordReduction_evaluate A M b k g w,
      evaluate_collapseLast]
    rfl
  | .snoc w true => by
    change RightModule.snocMap (wordReduction A (L := L) k w) (𝟙 L) ≫
        RightModule.lift (RightModule.restrict M b)
          (((evaluateWord A M b (k ≫ b.hom) g w.reduced).hom ⊗ₘ g) ≫ M.mon.mul) = _
    rw [evaluate_snoc_precompose]
    have h := congrArg RightModule.Hom.hom (wordReduction_evaluate A M b k g w)
    change (wordReduction A (L := L) k w).hom ≫ (evaluateWord A M b (k ≫ b.hom) g w.reduced).hom =
      (evaluateWord A M b (k ≫ b.hom) g w).hom at h
    rw [h]
    rfl

/-- Evaluation of a full original word face uses exactly the original letter values after `f`. -/
theorem wordToNew_evaluate (A M : Mon C) (b : A ⟶ M) {K L : C}
    (f : K ⟶ L) (g : L ⟶ M.X) : ∀ (w : Word),
    wordToNew A f w ≫ evaluateWord A M b (f ≫ g) g (Word.allNew w.length) =
      evaluateWord A M b (f ≫ g) g w
  | .nil => Category.id_comp _
  | .snoc w false => by
    change RightModule.snocMap (wordToNew A f w) f ≫
        RightModule.lift (RightModule.restrict M b)
          (((evaluateWord A M b (f ≫ g) g (Word.allNew w.length)).hom ⊗ₘ g) ≫ M.mon.mul) = _
    dsimp only [RightModule.snocMap]
    rw [RightModule.freeMap_lift]
    have h := congrArg RightModule.Hom.hom (wordToNew_evaluate A M b f g w)
    change (wordToNew A f w).hom ≫ (evaluateWord A M b (f ≫ g) g (Word.allNew w.length)).hom =
      (evaluateWord A M b (f ≫ g) g w).hom at h
    rw [← Category.assoc, tensorHom_comp_tensorHom, h]
    rfl
  | .snoc w true => by
    change RightModule.snocMap (wordToNew A f w) (𝟙 L) ≫
        RightModule.lift (RightModule.restrict M b)
          (((evaluateWord A M b (f ≫ g) g (Word.allNew w.length)).hom ⊗ₘ g) ≫ M.mon.mul) = _
    rw [evaluate_snoc_precompose]
    have h := congrArg RightModule.Hom.hom (wordToNew_evaluate A M b f g w)
    change (wordToNew A f w).hom ≫ (evaluateWord A M b (f ≫ g) g (Word.allNew w.length)).hom =
      (evaluateWord A M b (f ≫ g) g w).hom at h
    rw [h]
    rfl

/-- Evaluation respects the original equality transport of a complete word carrier. -/
theorem evaluateWord_transport (A M : Mon C) (b : A ⟶ M) {K L : C}
    (x : K ⟶ M.X) (g : L ⟶ M.X) {p q : Word} (h : p = q) :
    eqToHom (congrArg (wordObj A K L) h) ≫ (evaluateWord A M b x g q).hom =
      (evaluateWord A M b x g p).hom := by
  cases h
  exact Category.id_comp _

/-- The actual original full-word evaluation, with the original carrier comparison retained. -/
def targetWord (A M : Mon C) (b : A ⟶ M) {K L : C} (x : K ⟶ M.X) (g : L ⟶ M.X) (n : ℕ) :
    newWordObj A L n ⟶ M.X :=
  eqToHom (wordObj_allNew A K L n).symm ≫ (evaluateWord A M b x g (Word.allNew n)).hom

/-- The original complete old-letter collapse preserves the original full target word evaluation. -/
theorem wordReductionToNew_targetWord (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (g : L ⟶ M.X) (p : Word) :
    wordReductionToNew A k p ≫ targetWord A M b (k ≫ b.hom) g p.kept =
      (evaluateWord A M b (k ≫ b.hom) g p).hom := by
  dsimp only [wordReductionToNew, targetWord]
  simp only [Category.assoc, eqToHom_trans_assoc]
  change (wordReduction A (L := L) k p).hom ≫
    (eqToHom (congrArg (wordObj A K L) p.reduced_eq) ≫
      (evaluateWord A M b (k ≫ b.hom) g (Word.allNew p.kept)).hom) = _
  rw [evaluateWord_transport A M b (k ≫ b.hom) g p.reduced_eq]
  exact congrArg RightModule.Hom.hom (wordReduction_evaluate A M b k g p)

/-- The original full-face map preserves the original full target word evaluation. -/
theorem wordToNewHom_targetWord (A M : Mon C) (b : A ⟶ M) {K L : C}
    (f : K ⟶ L) (g : L ⟶ M.X) (p : Word) :
    wordToNewHom A f p ≫ targetWord A M b (f ≫ g) g p.length =
      (evaluateWord A M b (f ≫ g) g p).hom := by
  dsimp only [wordToNewHom, targetWord]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact congrArg RightModule.Hom.hom (wordToNew_evaluate A M b f g p)

/-- Every original proper-face equation holds for every original compatible monoid target. -/
theorem targetWord_relation (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) (p : Word) :
    wordReductionToNew A k p ≫ targetWord A M b (k ≫ b.hom) g p.kept =
      wordToNewHom A f p ≫ targetWord A M b (k ≫ b.hom) g p.length := by
  rw [wordReductionToNew_targetWord, h, wordToNewHom_targetWord]

section StageEvaluation

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair
local instance : HasColimitsOfShape ℕ C := HasColimitsOfShape.of_essentiallySmall C ℕ

/-- The entire original finite word family evaluates by its actual original monoid maps. -/
def evaluateStageWords (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (g : L ⟶ M.X) (N : ℕ) : stageWords A L N ⟶ M.X :=
  Sigma.desc (fun i : Fin (N + 1) => targetWord A M b (k ≫ b.hom) g i.val)

/-- The entire original target retains each original finite word family leg. -/
@[reassoc (attr := simp)] theorem stageWordι_evaluate (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (g : L ⟶ M.X) (N j : ℕ) (h : j ≤ N) :
    stageWordι A L N j h ≫ evaluateStageWords A M b k g N = targetWord A M b (k ≫ b.hom) g j :=
  Sigma.ι_comp_desc _ _

/-- Every original defining relation of the original stage is preserved by compatible monoid evaluation. -/
theorem evaluateStageWords_relations (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) (N : ℕ) :
    stageRelationLeft A L k N ≫ evaluateStageWords A M b k g N =
      stageRelationRight A f N ≫ evaluateStageWords A M b k g N := by
  apply Sigma.hom_ext
  intro c
  simp only [stageRelationLeft, stageRelationRight, Sigma.ι_comp_desc_assoc, Category.assoc,
    stageWordι_evaluate]
  exact targetWord_relation A M b k f g h c.word

/-- The actual original word stage evaluates through its actual coequalizer universal property. -/
def stageEvaluation (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) (N : ℕ) :
    stage A k f N ⟶ M.X :=
  coequalizer.desc (evaluateStageWords A M b k g N) (evaluateStageWords_relations A M b k f g h N)

/-- The original stage evaluation retains each original full word. -/
@[reassoc (attr := simp)] theorem stageWordLeg_evaluate (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) (N j : ℕ) (hj : j ≤ N) :
    stageWordLeg A k f N j hj ≫ stageEvaluation A M b k f g h N = targetWord A M b (k ≫ b.hom) g j := by
  dsimp only [stageWordLeg, stageEvaluation]
  rw [Category.assoc, coequalizer.π_desc, stageWordι_evaluate]

/-- The actual word-stage evaluations retain every original word-stage transition. -/
@[reassoc (attr := simp)] theorem stageEvaluation_naturality (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) {N N' : ℕ} (hN : N ≤ N') :
    stageMap A k f hN ≫ stageEvaluation A M b k f g h N' = stageEvaluation A M b k f g h N := by
  apply stage_hom_ext A k f N
  intro j hj
  rw [← Category.assoc, stageWordLeg_map, stageWordLeg_evaluate, stageWordLeg_evaluate]

/-- Every entire original compatible monoid target gives the actual original countable cocone. -/
def endpointEvaluationCocone (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) :
    Cocone (stageDiagram A k f) where
  pt := M.X
  ι :=
    { app N := stageEvaluation A M b k f g h N
      naturality N N' hN := by
        change stageMap A k f (leOfHom hN) ≫ stageEvaluation A M b k f g h N' =
          stageEvaluation A M b k f g h N ≫ 𝟙 M.X
        rw [Category.comp_id]
        exact stageEvaluation_naturality A M b k f g h (leOfHom hN) }

/-- The actual original countable word-stage endpoint evaluates through its original colimit property. -/
def endpointEvaluation (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) :
    stageEndpoint A k f ⟶ M.X :=
  colimit.desc (stageDiagram A k f) (endpointEvaluationCocone A M b k f g h)

/-- Every original stage leg retains the original entire stage evaluation at the countable endpoint. -/
@[reassoc (attr := simp)] theorem stageι_endpointEvaluation (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) (N : ℕ) :
    stageι A k f N ≫ endpointEvaluation A M b k f g h = stageEvaluation A M b k f g h N :=
  colimit.ι_desc (endpointEvaluationCocone A M b k f g h) N

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The entire original old monoid map is retained at the original countable endpoint. -/
@[reassoc (attr := simp)] theorem rootMap_endpointEvaluation (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) :
    rootMap A k f ≫ endpointEvaluation A M b k f g h = b.hom := by
  dsimp only [rootMap]
  rw [Category.assoc, stageι_endpointEvaluation, stageWordLeg_evaluate]
  change (𝟙 A.X) ≫ b.hom = b.hom
  exact Category.id_comp _

variable [SymmetricCategory C] [MonoidalClosed C]

local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))

/-- The actual original stage endpoint maps to the actual original monoid pushout,
using its constructed original old and new legs and their proved original compatibility. -/
def endpointToPushout (A : Mon C) {K L : C} (f : K ⟶ L) (a : TensorWord.tensorWordMon K ⟶ A) :
    stageEndpoint A (attachingValue A a) f ⟶ (freeAttachment A f a).X :=
  endpointEvaluation A (freeAttachment A f a) (oldι A f a) (attachingValue A a) f (newLetterι A f a)
    (Presentation.attachment_relation A (attachingValue A a) f)

/-- The original old leg is retained by the constructed endpoint-to-original-pushout map. -/
@[reassoc (attr := simp)] theorem rootMap_endpointToPushout (A : Mon C) {K L : C}
    (f : K ⟶ L) (a : TensorWord.tensorWordMon K ⟶ A) :
    rootMap A (attachingValue A a) f ≫ endpointToPushout A f a = (oldι A f a).hom :=
  rootMap_endpointEvaluation A (freeAttachment A f a) (oldι A f a) (attachingValue A a) f _ _

end StageEvaluation

namespace Word

/-- Recover the original selected finite positions of an entire original ordered word. -/
def toSubset : (p : Word) → FiniteCube.Index p.length
  | .nil => ∅
  | .snoc p false => FiniteCube.lower p.toSubset
  | .snoc p true => FiniteCube.upper p.toSubset

/-- Recovering the selected finite positions retains the complete original ordered word. -/
@[simp] theorem ofSubset_toSubset (p : Word) : ofSubset p.toSubset = p := by
  induction p with
  | nil => rfl
  | snoc p b ih =>
    cases b with
    | false =>
      change ofSubset (n := p.length + 1) (FiniteCube.lower p.toSubset) = .snoc p false
      simp only [ofSubset, FiniteCube.prefix_lower, FiniteCube.notMem_last_lower, decide_false, ih]
    | true =>
      change ofSubset (n := p.length + 1) (FiniteCube.upper p.toSubset) = .snoc p true
      simp only [ofSubset, FiniteCube.prefix_upper, FiniteCube.mem_last_upper, decide_true, ih]

/-- The original selected finite-position count is exactly the original new-letter count. -/
@[simp] theorem card_toSubset (p : Word) : p.toSubset.card = p.kept := by
  rw [← kept_ofSubset p.toSubset, ofSubset_toSubset]

/-- Every original proper word face gives its same actual proper finite subset. -/
def punctured (p : Word) (h : p.kept < p.length) : FiniteCube.Punctured p.length :=
  ⟨p.toSubset, fun he => by
    have hc := congrArg Finset.card he
    simp only [card_toSubset, Finset.card_univ, Fintype.card_fin] at hc
    exact (Nat.ne_of_lt h) hc⟩

end Word

namespace Mask

/-- The entire original subset inclusion in its original ordered finite positions. -/
def ofSubsets : {n : ℕ} → (S T : FiniteCube.Index n) → Mask
  | 0, _, _ => .nil
  | n + 1, S, T =>
    if Fin.last n ∈ T then
      .keep (ofSubsets (FiniteCube.«prefix» S) (FiniteCube.«prefix» T)) (decide (Fin.last n ∈ S))
    else
      .drop (ofSubsets (FiniteCube.«prefix» S) (FiniteCube.«prefix» T))

/-- The selected target keeps every original target position. -/
theorem full_ofSubsets : ∀ {n : ℕ} (S T : FiniteCube.Index n), (ofSubsets S T).fullWord = Word.ofSubset T
  | 0, _, _ => rfl
  | n + 1, S, T => by
    by_cases h : Fin.last n ∈ T
    · simp only [ofSubsets, h, ite_true, fullWord, Word.ofSubset, decide_true, full_ofSubsets]
    · simp only [ofSubsets, h, ite_false, fullWord, Word.ofSubset, decide_false, full_ofSubsets]

/-- A valid actual face inclusion retains the complete original source position data. -/
theorem source_ofSubsets : ∀ {n : ℕ} (S T : FiniteCube.Index n) (_h : S ⊆ T),
    (ofSubsets S T).sourceWord = Word.ofSubset S
  | 0, _, _, _ => rfl
  | n + 1, S, T, h => by
    have hp := source_ofSubsets (FiniteCube.«prefix» S) (FiniteCube.«prefix» T) (FiniteCube.prefix_mono h)
    by_cases ht : Fin.last n ∈ T
    · simp only [ofSubsets, ht, ite_true, sourceWord, Word.ofSubset, hp]
    · have hs : Fin.last n ∉ S := fun hs => ht (h hs)
      simp only [ofSubsets, ht, ite_false, sourceWord, Word.ofSubset, hp, hs, decide_false]

/-- The original target count is the cardinality of its complete original finite subset. -/
theorem count_ofSubsets {n : ℕ} (S T : FiniteCube.Index n) : (ofSubsets S T).count = T.card := by
  rw [← full_kept, full_ofSubsets, Word.kept_ofSubset]

end Mask

/-- The same original finite word vertex is the original ordered word recovered from its positions. -/
theorem literalVertex_toSubset (A : Mon C) (K L : C) (p : Word) :
    literalVertex A K L p.toSubset = wordObj A K L p := by
  rw [literalVertex_eq_word, Word.ofSubset_toSubset]

/-- Prefixing an original literal word-face map retains every original nonfinal coordinate. -/
theorem wordFace_prefix_heq (A : Mon C) {K L : C} (f : K ⟶ L) {n : ℕ}
    {S T : FiniteCube.Index (n + 1)} (h : S ⊆ T) :
    HEq (FiniteCube.alternatingMap (fun _ : Fin (n + 1) => 𝟙 A.X)
      (fun i : Fin n => FiniteCube.familyMap (fun _ : Fin (n + 1) => f) h i.castSucc))
      ((wordCube A f n).map (homOfLE (FiniteCube.prefix_mono h))) := by
  exact FiniteCube.alternatingMap_heq (fun _ => rfl) (fun _ => rfl)
    (fun i => congrFun (FiniteCube.vertexFamily_prefix S) i)
    (fun i => congrFun (FiniteCube.vertexFamily_prefix T) i)
    (fun _ => 𝟙 A.X) (fun _ => 𝟙 A.X) _ _ (fun _ => HEq.rfl)
    (fun i => FiniteCube.familyMap_prefix (fun _ : Fin (n + 1) => f) h i)

/-- Every literal original subset face is exactly its original masked word map,
with the original source and target carriers retained as heterogeneous equality. -/
theorem wordFace_heq (A : Mon C) {K L : C} (f : K ⟶ L) :
    ∀ {n : ℕ} (S T : FiniteCube.Index n) (h : S ⊆ T),
    HEq ((wordCube A f n).map (homOfLE h)) (faceMap A f (Mask.ofSubsets S T)).hom
  | 0, _, _, _ => by
    change HEq (𝟙 A.X) (𝟙 A.X)
    rfl
  | n + 1, S, T, h => by
    let p : Mask := Mask.ofSubsets (FiniteCube.«prefix» S) (FiniteCube.«prefix» T)
    let a := FiniteCube.alternatingMap (fun _ : Fin (n + 1) => 𝟙 A.X)
      (fun i : Fin n => FiniteCube.familyMap (fun _ : Fin (n + 1) => f) h i.castSucc)
    let z := FiniteCube.familyMap (fun _ : Fin (n + 1) => f) h (Fin.last n)
    have hp : HEq a (faceMap A f p).hom :=
      (wordFace_prefix_heq A f h).trans
        (wordFace_heq A f (FiniteCube.«prefix» S) (FiniteCube.«prefix» T) (FiniteCube.prefix_mono h))
    have hs :
        FiniteCube.alternatingObj (fun _ : Fin (n + 1) => A.X)
          (fun i : Fin n => FiniteCube.vertexFamily (fun _ : Fin (n + 1) => K) (fun _ => L) S i.castSucc) =
        wordObj A K L p.sourceWord := by
      rw [FiniteCube.vertexFamily_prefix]
      exact (literalVertex_eq_word A K L (FiniteCube.«prefix» S)).trans
        (congrArg (wordObj A K L) (Mask.source_ofSubsets _ _ (FiniteCube.prefix_mono h)).symm)
    have ht :
        FiniteCube.alternatingObj (fun _ : Fin (n + 1) => A.X)
          (fun i : Fin n => FiniteCube.vertexFamily (fun _ : Fin (n + 1) => K) (fun _ => L) T i.castSucc) =
        wordObj A K L p.fullWord := by
      rw [FiniteCube.vertexFamily_prefix]
      exact (literalVertex_eq_word A K L (FiniteCube.«prefix» T)).trans
        (congrArg (wordObj A K L) (Mask.full_ofSubsets (FiniteCube.«prefix» S) (FiniteCube.«prefix» T)).symm)
    have finish {X Y : C} (g : X ⟶ Y)
        (hX : FiniteCube.vertexFamily (fun _ : Fin (n + 1) => K) (fun _ => L) S (Fin.last n) = X)
        (hY : FiniteCube.vertexFamily (fun _ : Fin (n + 1) => K) (fun _ => L) T (Fin.last n) = Y)
        (hg : HEq z g) : HEq ((a ⊗ₘ z) ⊗ₘ 𝟙 A.X) (((faceMap A f p).hom ⊗ₘ g) ▷ A.X) := by
      have hfirst := OrderedTensor.tensorHom_heq hs ht hX hY a z (faceMap A f p).hom g hp hg
      have hlast := OrderedTensor.tensorHom_heq
        (congrArg₂ (fun P Q : C => P ⊗ Q) hs hX) (congrArg₂ (fun P Q : C => P ⊗ Q) ht hY)
        rfl rfl (a ⊗ₘ z) (𝟙 A.X) ((faceMap A f p).hom ⊗ₘ g) (𝟙 A.X) hfirst HEq.rfl
      exact hlast.trans (heq_of_eq (tensorHom_id _ A.X))
    by_cases hT : Fin.last n ∈ T
    · by_cases hS : Fin.last n ∈ S
      · have hx := finish (𝟙 L)
          (by simp only [FiniteCube.vertexFamily, hS, ite_true])
          (by simp only [FiniteCube.vertexFamily, hT, ite_true])
          (FiniteCube.familyMap_selected (fun _ : Fin (n + 1) => f) h (Fin.last n) hS)
        have hm : Mask.ofSubsets S T = .keep p true := by
          simp only [Mask.ofSubsets, hT, hS, ite_true, decide_true]
          rfl
        rw [hm]
        change HEq ((a ⊗ₘ z) ⊗ₘ 𝟙 A.X) (((faceMap A f p).hom ⊗ₘ 𝟙 L) ▷ A.X)
        exact hx
      · have hx := finish f
          (by simp only [FiniteCube.vertexFamily, hS, ite_false])
          (by simp only [FiniteCube.vertexFamily, hT, ite_true])
          (FiniteCube.familyMap_added (fun _ : Fin (n + 1) => f) h (Fin.last n) hS hT)
        have hm : Mask.ofSubsets S T = .keep p false := by
          simp only [Mask.ofSubsets, hT, hS, ite_true, decide_false]
          rfl
        rw [hm]
        change HEq ((a ⊗ₘ z) ⊗ₘ 𝟙 A.X) (((faceMap A f p).hom ⊗ₘ f) ▷ A.X)
        exact hx
    · have hS : Fin.last n ∉ S := fun hi => hT (h hi)
      have hx := finish (𝟙 K)
        (by simp only [FiniteCube.vertexFamily, hS, ite_false])
        (by simp only [FiniteCube.vertexFamily, hT, ite_false])
        (FiniteCube.familyMap_unselected (fun _ : Fin (n + 1) => f) h (Fin.last n) hT)
      have hm : Mask.ofSubsets S T = .drop p := by
        simp only [Mask.ofSubsets, hT, ite_false]
        rfl
      rw [hm]
      change HEq ((a ⊗ₘ z) ⊗ₘ 𝟙 A.X) (((faceMap A f p).hom ⊗ₘ 𝟙 K) ▷ A.X)
      exact hx

namespace Mask

/-- The retained source has exactly the original source's complete new-letter count. -/
theorem selected_kept (m : Mask) : m.selectedWord.kept = m.sourceWord.kept := by
  induction m with
  | nil => rfl
  | drop m ih => exact ih
  | keep m b ih => cases b <;> simp only [selectedWord, sourceWord, Word.kept, ih]

end Mask

/-- The retained face map is exactly the original full-face map of the retained source word. -/
theorem selectedFaceMap_eq (A : Mon C) {K L : C} (f : K ⟶ L) : ∀ (m : Mask),
    selectedFaceMap A f m = wordToNew A f m.selectedWord ≫
      eqToHom (congrArg (wordModule A K L) (congrArg Word.allNew m.selected_length))
  | .nil => (Category.comp_id _).symm
  | .drop m => selectedFaceMap_eq A f m
  | .keep m false => by
    change RightModule.snocMap (selectedFaceMap A f m) f =
      RightModule.snocMap (wordToNew A f m.selectedWord) f ≫
        eqToHom (congrArg (wordModule A K L) (congrArg Word.allNew (Mask.selected_length (.keep m false))))
    rw [selectedFaceMap_eq A f m]
    change RightModule.snocMap (wordToNew A f m.selectedWord ≫
      eqToHom (congrArg (wordModule A K L) (congrArg Word.allNew m.selected_length))) f =
        RightModule.snocMap (wordToNew A f m.selectedWord) f ≫
          eqToHom (congrArg (fun P => RightModule.snoc P L)
            (congrArg (wordModule A K L) (congrArg Word.allNew m.selected_length)))
    simpa only [Category.comp_id, RightModule.snocMap_eqToHom] using
      RightModule.snocMap_comp (wordToNew A f m.selectedWord)
        (eqToHom (congrArg (wordModule A K L) (congrArg Word.allNew m.selected_length))) f (𝟙 L)
  | .keep m true => by
    change RightModule.snocMap (selectedFaceMap A f m) (𝟙 L) =
      RightModule.snocMap (wordToNew A f m.selectedWord) (𝟙 L) ≫
        eqToHom (congrArg (wordModule A K L) (congrArg Word.allNew (Mask.selected_length (.keep m true))))
    rw [selectedFaceMap_eq A f m, RightModule.snocMap_comp_id, RightModule.snocMap_eqToHom]
    rfl

/-- The original source cube carrier retains its complete original masked source word. -/
theorem maskSourceVertex_eq (A : Mon C) (K L : C) {n : ℕ} (S T : FiniteCube.Index n) (h : S ⊆ T) :
    literalVertex A K L S = wordObj A K L (Mask.ofSubsets S T).sourceWord :=
  (literalVertex_eq_word A K L S).trans (congrArg (wordObj A K L) (Mask.source_ofSubsets S T h).symm)

/-- The original target cube carrier retains its complete original masked target word. -/
theorem maskTargetVertex_eq (A : Mon C) (K L : C) {n : ℕ} (S T : FiniteCube.Index n) :
    literalVertex A K L T = wordObj A K L (Mask.ofSubsets S T).fullWord :=
  (literalVertex_eq_word A K L T).trans (congrArg (wordObj A K L) (Mask.full_ofSubsets S T).symm)

/-- Every original subset face has its complete original word map and both original carrier transports. -/
theorem wordFace_eq (A : Mon C) {K L : C} (f : K ⟶ L) {n : ℕ}
    (S T : FiniteCube.Index n) (h : S ⊆ T) :
    (wordCube A f n).map (homOfLE h) =
      eqToHom (maskSourceVertex_eq A K L S T h) ≫ (faceMap A f (Mask.ofSubsets S T)).hom ≫
        eqToHom (maskTargetVertex_eq A K L S T).symm :=
  (conj_eqToHom_iff_heq _ _ (maskSourceVertex_eq A K L S T h) (maskTargetVertex_eq A K L S T)).mpr
    (wordFace_heq A f S T h)

/-- Partial original old-letter contraction followed by complete contraction is the original complete map. -/
theorem partialCollapse_toNew (A : Mon C) {K L : C} (k : K ⟶ A.X) (m : Mask) :
    (partialCollapse A (L := L) k m).hom ≫ wordReductionToNew A k m.selectedWord ≫
        eqToHom (congrArg (newWordObj A L) m.selected_kept) =
      wordReductionToNew A k m.sourceWord := by
  have hh := congrArg RightModule.Hom.hom (partialCollapse_reduction A (L := L) k m)
  change (partialCollapse A (L := L) k m).hom ≫ (selectedReduction A k m).hom =
    (wordReduction A k m.sourceWord).hom at hh
  have hs := congrArg RightModule.Hom.hom (selectedReduction_eq A (L := L) k m)
  simp only [RightModule.comp_hom, RightModule.eqToHom_hom] at hs
  rw [hs] at hh
  have h' := congrArg (fun t => t ≫ eqToHom (reducedWord_eq A K L m.sourceWord)) hh
  simpa only [wordReductionToNew, Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using h'

/-- The complete target collapse retains its exact original full-word carrier comparison. -/
theorem fullCollapse_toNew (A : Mon C) {K L : C} (k : K ⟶ A.X) (m : Mask) :
    (fullCollapse A (L := L) k m).hom ≫ eqToHom (wordObj_allNew A K L m.count) =
      wordReductionToNew A k m.fullWord ≫ eqToHom (congrArg (newWordObj A L) m.full_kept) := by
  have h := congrArg RightModule.Hom.hom (fullCollapse_eq A (L := L) k m)
  simp only [RightModule.comp_hom, RightModule.eqToHom_hom] at h
  have h' := congrArg (fun t => t ≫ eqToHom (wordObj_allNew A K L m.count)) h
  simpa only [wordReductionToNew, Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using h'

/-- The retained full-face map retains its exact original full-word carrier comparison. -/
theorem selectedFaceMap_toNew (A : Mon C) {K L : C} (f : K ⟶ L) (m : Mask) :
    (selectedFaceMap A f m).hom ≫ eqToHom (wordObj_allNew A K L m.count) =
      wordToNewHom A f m.selectedWord ≫ eqToHom (congrArg (newWordObj A L) m.selected_length) := by
  have h := congrArg RightModule.Hom.hom (selectedFaceMap_eq A f m)
  simp only [RightModule.comp_hom, RightModule.eqToHom_hom] at h
  have h' := congrArg (fun t => t ≫ eqToHom (wordObj_allNew A K L m.count)) h
  simpa only [wordToNewHom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using h'

section StageFaceNormalization

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair

/-- The same original stage-word inclusion retains the equality transport of its original word count. -/
theorem stageWordLeg_transport (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L)
    (N : ℕ) {j j' : ℕ} (e : j = j') (h : j ≤ N) :
    eqToHom (congrArg (newWordObj A L) e) ≫ stageWordLeg A k f N j' (e ▸ h) =
      stageWordLeg A k f N j h := by
  cases e
  exact Category.id_comp _

/-- Every partial original old-letter collapse retains its actual earlier stage-word leg. -/
theorem partialCollapse_stage (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    (m : Mask) (h : m.sourceWord.kept ≤ N) :
    (partialCollapse A (L := L) k m).hom ≫ wordReductionToNew A k m.selectedWord ≫
        stageWordLeg A k f N m.selectedWord.kept (m.selected_kept.symm ▸ h) =
      wordReductionToNew A k m.sourceWord ≫ stageWordLeg A k f N m.sourceWord.kept h := by
  have hs := congrArg (fun t => t ≫ stageWordLeg A k f N m.sourceWord.kept h)
    (partialCollapse_toNew A (L := L) k m)
  have ht := stageWordLeg_transport A k f N m.selected_kept (m.selected_kept.symm ▸ h)
  change eqToHom (congrArg (newWordObj A L) m.selected_kept) ≫
    stageWordLeg A k f N m.sourceWord.kept h =
      stageWordLeg A k f N m.selectedWord.kept (m.selected_kept.symm ▸ h) at ht
  simp only [Category.assoc] at hs
  rw [ht] at hs
  exact hs

/-- Every actual target collapse retains its original later stage-word leg. -/
theorem fullCollapse_stage (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    (m : Mask) (h : m.count ≤ N) :
    (fullCollapse A (L := L) k m).hom ≫ eqToHom (wordObj_allNew A K L m.count) ≫
        stageWordLeg A k f N m.count h =
      wordReductionToNew A k m.fullWord ≫ stageWordLeg A k f N m.fullWord.kept (m.full_kept.symm ▸ h) := by
  have hs := congrArg (fun t => t ≫ stageWordLeg A k f N m.count h) (fullCollapse_toNew A (L := L) k m)
  have ht := stageWordLeg_transport A k f N m.full_kept (m.full_kept.symm ▸ h)
  change eqToHom (congrArg (newWordObj A L) m.full_kept) ≫ stageWordLeg A k f N m.count h =
    stageWordLeg A k f N m.fullWord.kept (m.full_kept.symm ▸ h) at ht
  simp only [Category.assoc] at hs
  rw [ht] at hs
  exact hs

/-- The retained full-face map retains its original later stage-word leg. -/
theorem selectedFaceMap_stage (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    (m : Mask) (h : m.count ≤ N) :
    (selectedFaceMap A f m).hom ≫ eqToHom (wordObj_allNew A K L m.count) ≫
        stageWordLeg A k f N m.count h =
      wordToNewHom A f m.selectedWord ≫ stageWordLeg A k f N m.selectedWord.length (m.selected_length.symm ▸ h) := by
  have hs := congrArg (fun t => t ≫ stageWordLeg A k f N m.count h) (selectedFaceMap_toNew A f m)
  have ht := stageWordLeg_transport A k f N m.selected_length (m.selected_length.symm ▸ h)
  change eqToHom (congrArg (newWordObj A L) m.selected_length) ≫ stageWordLeg A k f N m.count h =
    stageWordLeg A k f N m.selectedWord.length (m.selected_length.symm ▸ h) at ht
  simp only [Category.assoc] at hs
  rw [ht] at hs
  exact hs

/-- The two complete original contraction diagrams agree at the same actual word stage. -/
theorem stage_mask (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    (m : Mask) (h : m.count ≤ N) (hp : m.selectedWord.kept < m.selectedWord.length) :
    wordReductionToNew A k m.sourceWord ≫
        stageWordLeg A k f N m.sourceWord.kept
          (m.selected_kept ▸ m.selectedWord.kept_le_length.trans (m.selected_length.symm ▸ h)) =
      (faceMap A f m).hom ≫ wordReductionToNew A k m.fullWord ≫
        stageWordLeg A k f N m.fullWord.kept (m.full_kept.symm ▸ h) := by
  let c : CellFace N := ⟨m.selectedWord, m.selected_length.symm ▸ h, hp⟩
  have hc := stage_cell A k f N c
  have hm := congrArg RightModule.Hom.hom (partialCollapse_face A (L := L) k f m)
  change (partialCollapse A (L := L) k m).hom ≫ (selectedFaceMap A f m).hom =
    (faceMap A f m).hom ≫ (fullCollapse A k m).hom at hm
  have hn := congrArg (fun t => t ≫ eqToHom (wordObj_allNew A K L m.count) ≫
    stageWordLeg A k f N m.count h) hm
  simp only [Category.assoc, selectedFaceMap_stage, fullCollapse_stage] at hn
  rw [← hn, ← hc]
  exact (partialCollapse_stage A k f N m _).symm

end StageFaceNormalization

section LiteralFaceValues

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair

/-- The entire original word enters its actual earlier full-word stage. -/
def wordValue (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    (p : Word) (h : p.kept ≤ N) : wordObj A K L p ⟶ stage A k f N :=
  wordReductionToNew A k p ≫ stageWordLeg A k f N p.kept h

/-- The original word-stage value retains the original equality transport of a full word. -/
theorem wordValue_transport (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    {p q : Word} (e : p = q) (h : p.kept ≤ N) :
    eqToHom (congrArg (wordObj A K L) e) ≫ wordValue A k f N q (congrArg Word.kept e ▸ h) =
      wordValue A k f N p h := by
  cases e
  exact Category.id_comp _

/-- The same original literal subset vertex enters its actual earlier full-word stage. -/
def vertexValue (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    {n : ℕ} (S : FiniteCube.Index n) (h : S.card ≤ N) : literalVertex A K L S ⟶ stage A k f N :=
  vertexCollapse A k S ≫ stageWordLeg A k f N S.card h

/-- The literal face value is the original word value with its original complete vertex comparison. -/
theorem vertexValue_eq_word (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    {n : ℕ} (S : FiniteCube.Index n) (h : S.card ≤ N) :
    vertexValue A k f N S h = eqToHom (literalVertex_eq_word A K L S) ≫
      wordValue A k f N (Word.ofSubset S) ((Word.kept_ofSubset S).symm ▸ h) := by
  let p : Word := Word.ofSubset S
  let e : p.kept = S.card := Word.kept_ofSubset S
  have he : eqToHom (reducedVertex_eq A K L S) =
      eqToHom (reducedWord_eq A K L p) ≫ eqToHom (congrArg (newWordObj A L) e) := by
    rw [eqToHom_trans]
  have ht := stageWordLeg_transport A k f N e (e.symm ▸ h)
  change eqToHom (congrArg (newWordObj A L) e) ≫ stageWordLeg A k f N S.card h =
    stageWordLeg A k f N p.kept (e.symm ▸ h) at ht
  simp only [vertexValue, vertexCollapse, wordValue, wordReductionToNew, Category.assoc]
  rw [he, Category.assoc, ht]

/-- The literal original source face retains its complete original masked word-stage value. -/
theorem vertexValue_eq_maskSource (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    {n : ℕ} (S T : FiniteCube.Index n) (h : S ⊆ T) (hS : S.card ≤ N) :
    vertexValue A k f N S hS = eqToHom (maskSourceVertex_eq A K L S T h) ≫
      wordValue A k f N (Mask.ofSubsets S T).sourceWord
        ((congrArg Word.kept (Mask.source_ofSubsets S T h)).trans (Word.kept_ofSubset S) |>.symm ▸ hS) := by
  let e : (Mask.ofSubsets S T).sourceWord = Word.ofSubset S := Mask.source_ofSubsets S T h
  have he : eqToHom (maskSourceVertex_eq A K L S T h) =
      eqToHom (literalVertex_eq_word A K L S) ≫ eqToHom (congrArg (wordObj A K L) e.symm) := by
    rw [eqToHom_trans]
  rw [vertexValue_eq_word, he, Category.assoc]
  have ht := wordValue_transport A k f N e.symm ((Word.kept_ofSubset S).symm ▸ hS)
  exact congrArg (fun t => eqToHom (literalVertex_eq_word A K L S) ≫ t) ht.symm

/-- The literal original target face retains its complete original masked word-stage value. -/
theorem vertexValue_eq_maskTarget (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    {n : ℕ} (S T : FiniteCube.Index n) (hT : T.card ≤ N) :
    vertexValue A k f N T hT = eqToHom (maskTargetVertex_eq A K L S T) ≫
      wordValue A k f N (Mask.ofSubsets S T).fullWord
        ((congrArg Word.kept (Mask.full_ofSubsets S T)).trans (Word.kept_ofSubset T) |>.symm ▸ hT) := by
  let e : (Mask.ofSubsets S T).fullWord = Word.ofSubset T := Mask.full_ofSubsets S T
  have he : eqToHom (maskTargetVertex_eq A K L S T) =
      eqToHom (literalVertex_eq_word A K L T) ≫ eqToHom (congrArg (wordObj A K L) e.symm) := by
    rw [eqToHom_trans]
  rw [vertexValue_eq_word, he, Category.assoc]
  have ht := wordValue_transport A k f N e.symm ((Word.kept_ofSubset T).symm ▸ hT)
  exact congrArg (fun t => eqToHom (literalVertex_eq_word A K L T) ≫ t) ht.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original literal subset face commutes with complete contraction into the actual earlier stage. -/
theorem vertexValue_face (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    {n : ℕ} (S T : FiniteCube.Index n) (h : S ⊆ T) (hT : T.card ≤ N) :
    (wordCube A f n).map (homOfLE h) ≫ vertexValue A k f N T hT =
      vertexValue A k f N S ((Finset.card_le_card h).trans hT) := by
  by_cases he : S = T
  · subst T
    have hm : (homOfLE h : S ⟶ S) = 𝟙 S := Subsingleton.elim _ _
    rw [hm, Functor.map_id, Category.id_comp]
  · let m : Mask := Mask.ofSubsets S T
    have hcount : m.count ≤ N := Mask.count_ofSubsets S T ▸ hT
    have hsource : m.sourceWord.kept = S.card :=
      (congrArg Word.kept (Mask.source_ofSubsets S T h)).trans (Word.kept_ofSubset S)
    have hproper : m.selectedWord.kept < m.selectedWord.length := by
      rw [m.selected_kept, m.selected_length, hsource, Mask.count_ofSubsets S T]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h, he⟩)
    rw [wordFace_eq, vertexValue_eq_maskTarget A k f N S T,
      vertexValue_eq_maskSource A k f N S T h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have hs := stage_mask A k f N m hcount hproper
    exact congrArg (fun t => eqToHom (maskSourceVertex_eq A K L S T h) ≫ t) hs.symm

end LiteralFaceValues

section ActualAttachingMaps

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair
local instance (n : ℕ) : HasColimitsOfShape (FiniteCube.Punctured n) C :=
  HasColimitsOfShape.of_essentiallySmall C (FiniteCube.Punctured n)

/-- Every literal original face enters its own actual earlier stage before the original later transition. -/
theorem vertexValue_ownStage (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L)
    (N : ℕ) {n : ℕ} (S : FiniteCube.Index n) (h : S.card ≤ N) :
    vertexValue A k f N S h =
      (vertexCollapse A k S ≫ stageWordLeg A k f S.card S.card (Nat.le_refl _)) ≫ stageMap A k f h := by
  rw [Category.assoc, stageWordLeg_map]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual punctured original word cube has its constructed cocone to the actual predecessor stage. -/
def attachingCocone (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    Cocone (FiniteCube.punctured (wordCube A f (n + 1))) where
  pt := stage A k f n
  ι :=
    { app S := vertexValue A k f n S.1 (Nat.le_of_lt_succ (FiniteCube.card_lt S))
      naturality S T h := by
        change (wordCube A f (n + 1)).map (homOfLE (leOfHom h)) ≫
          vertexValue A k f n T.1 (Nat.le_of_lt_succ (FiniteCube.card_lt T)) =
            vertexValue A k f n S.1 (Nat.le_of_lt_succ (FiniteCube.card_lt S)) ≫ 𝟙 (stage A k f n)
        rw [Category.comp_id]
        exact vertexValue_face A k f n S.1 T.1 (leOfHom h) _ }

/-- The actual attaching source is the colimit of every original proper subset face. -/
abbrev attachingSource (A : Mon C) {K L : C} (f : K ⟶ L) (n : ℕ) : C :=
  FiniteCube.boundary (wordCube A f n)

/-- The actual original attaching map is constructed from all original old-letter contractions. -/
def attachingMap (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    attachingSource A f (n + 1) ⟶ stage A k f n :=
  FiniteCube.boundaryDesc (wordCube A f (n + 1)) (attachingCocone A k f n)

/-- Every original proper face of the actual attaching map is its exact original contraction and earlier stage leg. -/
@[reassoc (attr := simp)] theorem attachingFace (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) (S : FiniteCube.Punctured (n + 1)) :
    FiniteCube.boundaryι (wordCube A f (n + 1)) S ≫ attachingMap A k f n =
      vertexValue A k f n S.1 (Nat.le_of_lt_succ (FiniteCube.card_lt S)) :=
  FiniteCube.boundaryι_desc (wordCube A f (n + 1)) (attachingCocone A k f n) S

end ActualAttachingMaps

namespace Mask

/-- Keep every original word position when mapping to its original full face. -/
def allKeep : Word → Mask
  | .nil => .nil
  | .snoc p b => .keep (allKeep p) b

/-- Keeping every original position retains the entire original source word. -/
@[simp] theorem allKeep_source (p : Word) : (allKeep p).sourceWord = p := by
  induction p with
  | nil => rfl
  | snoc p b ih => simp only [allKeep, sourceWord, ih]

/-- The complete target keeps every original position as an original new letter. -/
@[simp] theorem allKeep_full (p : Word) : (allKeep p).fullWord = Word.allNew p.length := by
  induction p with
  | nil => rfl
  | snoc p b ih => simp only [allKeep, fullWord, Word.length, Word.allNew, ih]

/-- The original full subset keeps every original finite input position. -/
@[simp] theorem ofSubsets_univ : ∀ {n : ℕ} (S : FiniteCube.Index n),
    ofSubsets S Finset.univ = allKeep (Word.ofSubset S)
  | 0, _ => rfl
  | n + 1, S => by
    simp only [ofSubsets, Finset.mem_univ, ite_true, FiniteCube.prefix_univ, Word.ofSubset,
      allKeep, ofSubsets_univ]

end Mask

namespace RightModule

variable {A : Mon C}

/-- Appending the same original letter map retains original source, target and prefix-map transports. -/
theorem snocMap_hom_heq {P Q P' Q' : RightModule A} (hP : P = P') (hQ : Q = Q')
    (f : P ⟶ Q) (g : P' ⟶ Q') (hf : HEq f.hom g.hom) {X Y : C} (h : X ⟶ Y) :
    HEq (snocMap f h).hom (snocMap g h).hom := by
  cases hP
  cases hQ
  have hg : f = g := Hom.ext (eq_of_heq hf)
  subst g
  rfl

end RightModule

/-- The entire retained original mask has precisely the original full-face word map. -/
theorem faceMap_allKeep_heq (A : Mon C) {K L : C} (f : K ⟶ L) (p : Word) :
    HEq (faceMap A f (Mask.allKeep p)).hom (wordToNew A f p).hom := by
  induction p with
  | nil => rfl
  | snoc p b ih =>
    cases b with
    | false =>
      change HEq (RightModule.snocMap (faceMap A f (Mask.allKeep p)) f).hom
        (RightModule.snocMap (wordToNew A f p) f).hom
      exact RightModule.snocMap_hom_heq
        (congrArg (wordModule A K L) (Mask.allKeep_source p))
        (congrArg (wordModule A K L) (Mask.allKeep_full p)) _ _ ih f
    | true =>
      change HEq (RightModule.snocMap (faceMap A f (Mask.allKeep p)) (𝟙 L)).hom
        (RightModule.snocMap (wordToNew A f p) (𝟙 L)).hom
      exact RightModule.snocMap_hom_heq
        (congrArg (wordModule A K L) (Mask.allKeep_source p))
        (congrArg (wordModule A K L) (Mask.allKeep_full p)) _ _ ih (𝟙 L)

/-- The original literal full-face cube map is exactly the original full-face word map. -/
theorem wordFullFace_heq (A : Mon C) {K L : C} (f : K ⟶ L) {n : ℕ} (S : FiniteCube.Index n) :
    HEq ((wordCube A f n).map (homOfLE (Finset.subset_univ S)))
      (wordToNew A f (Word.ofSubset S)).hom := by
  have h := wordFace_heq A f S Finset.univ (Finset.subset_univ S)
  rw [Mask.ofSubsets_univ] at h
  exact h.trans (faceMap_allKeep_heq A f (Word.ofSubset S))

/-- The literal original terminal vertex is its actual complete new word. -/
theorem terminalVertex_eq (A : Mon C) (K L : C) (n : ℕ) :
    literalVertex A K L (Finset.univ : FiniteCube.Index n) = newWordObj A L n :=
  (literalVertex_eq_word A K L Finset.univ).trans
    ((congrArg (wordObj A K L) (Word.ofSubset_univ n)).trans (wordObj_allNew A K L n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original full-face cube arrow retains its entire original word map and exact terminal comparison. -/
theorem wordFullFace_eq (A : Mon C) {K L : C} (f : K ⟶ L) {n : ℕ} (S : FiniteCube.Index n) :
    (wordCube A f n).map (homOfLE (Finset.subset_univ S)) ≫ eqToHom (terminalVertex_eq A K L n) =
      eqToHom (literalVertex_eq_word A K L S) ≫ wordToNewHom A f (Word.ofSubset S) ≫
        eqToHom (congrArg (newWordObj A L) (Word.length_ofSubset S)) := by
  let p : Word := Word.ofSubset S
  let e : p.length = n := Word.length_ofSubset S
  let et : literalVertex A K L (Finset.univ : FiniteCube.Index n) =
      wordObj A K L (Word.allNew p.length) :=
    (terminalVertex_eq A K L n).trans
      ((congrArg (newWordObj A L) e.symm).trans (wordObj_allNew A K L p.length).symm)
  have h := (conj_eqToHom_iff_heq _ _ (literalVertex_eq_word A K L S) et).mpr (wordFullFace_heq A f S)
  have hc : eqToHom et.symm ≫ eqToHom (terminalVertex_eq A K L n) =
      eqToHom (wordObj_allNew A K L p.length) ≫ eqToHom (congrArg (newWordObj A L) e) := by
    rw [eqToHom_trans, eqToHom_trans]
  rw [h]
  simp only [Category.assoc]
  rw [hc]
  simp only [wordToNewHom, Category.assoc]

section SuccessorSquares

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair
local instance (n : ℕ) : HasColimitsOfShape (FiniteCube.Punctured n) C :=
  HasColimitsOfShape.of_essentiallySmall C (FiniteCube.Punctured n)

/-- The literal complete original new word enters its actual original word stage. -/
def topStageLeg (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    (wordCube A f n).obj Finset.univ ⟶ stage A k f n :=
  eqToHom (terminalVertex_eq A K L n) ≫ stageWordLeg A k f n n (Nat.le_refl n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every literal original proper cube face satisfies its actual word-stage defining relation. -/
theorem cubeFace_stage (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (S : FiniteCube.Punctured n) :
    (wordCube A f n).map (homOfLE (Finset.subset_univ S.1)) ≫ topStageLeg A k f n =
      vertexValue A k f n S.1 (Nat.le_of_lt (FiniteCube.card_lt S)) := by
  let p : Word := Word.ofSubset S.1
  let e : p.length = n := Word.length_ofSubset S.1
  let c : CellFace n :=
    { word := p
      bound := Nat.le_of_eq e
      proper := by
        change (Word.ofSubset S.1).kept < (Word.ofSubset S.1).length
        rw [Word.kept_ofSubset, Word.length_ofSubset]
        exact FiniteCube.card_lt S }
  have hc := stage_cell A k f n c
  have ht := stageWordLeg_transport A k f n e c.bound
  change eqToHom (congrArg (newWordObj A L) e) ≫ stageWordLeg A k f n n (Nat.le_refl n) =
    stageWordLeg A k f n p.length c.bound at ht
  dsimp only [topStageLeg]
  rw [← Category.assoc, wordFullFace_eq]
  simp only [Category.assoc]
  rw [ht, vertexValue_eq_word]
  exact congrArg (fun t => eqToHom (literalVertex_eq_word A K L S.1) ≫ t) hc.symm

/-- The literal original vertex value retains each original later-stage transition. -/
@[reassoc (attr := simp)] theorem vertexValue_map (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) {N M : ℕ} (h : N ≤ M) {n : ℕ}
    (S : FiniteCube.Index n) (hS : S.card ≤ N) :
    vertexValue A k f N S hS ≫ stageMap A k f h = vertexValue A k f M S (hS.trans h) := by
  dsimp only [vertexValue]
  rw [Category.assoc, stageWordLeg_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The entire actual punctured original word cube forms the original successor square. -/
theorem successorSquare (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    attachingMap A k f n ≫ stageMap A k f (Nat.le_succ n) =
      FiniteCube.boundaryToTop (wordCube A f (n + 1)) ≫ topStageLeg A k f (n + 1) := by
  apply FiniteCube.boundary_hom_ext (wordCube A f (n + 1))
  intro S
  rw [attachingFace_assoc, vertexValue_map, FiniteCube.boundaryι_boundaryToTop_assoc, cubeFace_stage]

/-- The actual original successor cocone retains the complete original attaching cube and predecessor. -/
def successorCocone (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1))) :=
  PushoutCocone.mk (stageMap A k f (Nat.le_succ n)) (topStageLeg A k f (n + 1)) (successorSquare A k f n)

end SuccessorSquares

namespace Word

/-- Retain the original selected finite positions while transporting their exact original dimension. -/
def toSubsetAt (p : Word) {m : ℕ} (e : p.length = m) : FiniteCube.Index m := e ▸ p.toSubset

/-- The transported original finite positions retain the original complete word. -/
@[simp] theorem ofSubset_toSubsetAt (p : Word) {m : ℕ} (e : p.length = m) :
    ofSubset (p.toSubsetAt e) = p := by
  cases e
  exact ofSubset_toSubset p

/-- The transported original finite-position count retains the actual original new-letter count. -/
@[simp] theorem card_toSubsetAt (p : Word) {m : ℕ} (e : p.length = m) :
    (p.toSubsetAt e).card = p.kept := by
  cases e
  exact card_toSubset p

/-- Every proper original word gives its same actual proper face at the original dimension. -/
def puncturedAt (p : Word) {m : ℕ} (e : p.length = m) (h : p.kept < p.length) : FiniteCube.Punctured m :=
  ⟨p.toSubsetAt e, by
    cases e
    exact (p.punctured h).2⟩

end Word

/-- The transported original finite vertex has the complete original word carrier. -/
theorem literalVertex_toSubsetAt (A : Mon C) (K L : C) (p : Word) {m : ℕ} (e : p.length = m) :
    literalVertex A K L (p.toSubsetAt e) = wordObj A K L p := by
  cases e
  exact literalVertex_toSubset A K L p

/-- The original full-face word map retains the original equality transports of both carriers. -/
theorem wordToNewHom_transport (A : Mon C) {K L : C} (f : K ⟶ L) {p q : Word} (e : p = q) :
    eqToHom (congrArg (wordObj A K L) e) ≫ wordToNewHom A f q =
      wordToNewHom A f p ≫ eqToHom (congrArg (newWordObj A L) (congrArg Word.length e)) := by
  cases e
  rw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The entire transported original cube face is its original full-word face with both original comparisons. -/
theorem wordFullFace_at (A : Mon C) {K L : C} (f : K ⟶ L) (p : Word) {m : ℕ} (e : p.length = m) :
    eqToHom (literalVertex_toSubsetAt A K L p e).symm ≫
        (wordCube A f m).map (homOfLE (Finset.subset_univ (p.toSubsetAt e))) =
      wordToNewHom A f p ≫ eqToHom (congrArg (newWordObj A L) e) ≫
        eqToHom (terminalVertex_eq A K L m).symm := by
  let S := p.toSubsetAt e
  let ep : Word.ofSubset S = p := Word.ofSubset_toSubsetAt p e
  have hfront : eqToHom (literalVertex_toSubsetAt A K L p e).symm ≫
      eqToHom (literalVertex_eq_word A K L S) = eqToHom (congrArg (wordObj A K L) ep.symm) := by
    rw [eqToHom_trans]
  have hh := wordFullFace_eq A f S
  have hleft : eqToHom (literalVertex_toSubsetAt A K L p e).symm ≫
      (wordCube A f m).map (homOfLE (Finset.subset_univ S)) ≫ eqToHom (terminalVertex_eq A K L m) =
      wordToNewHom A f p ≫ eqToHom (congrArg (newWordObj A L) e) := by
    rw [hh, ← Category.assoc, hfront]
    have hew := congrArg (fun t => t ≫ eqToHom (congrArg (newWordObj A L) (Word.length_ofSubset S)))
      (wordToNewHom_transport A f ep.symm)
    simp only [Category.assoc, eqToHom_trans] at hew
    exact hew
  apply (cancel_mono (eqToHom (terminalVertex_eq A K L m))).mp
  simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp] using hleft


section SuccessorDescenders

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair
local instance (n : ℕ) : HasColimitsOfShape (FiniteCube.Punctured n) C :=
  HasColimitsOfShape.of_essentiallySmall C (FiniteCube.Punctured n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original word value at its transported finite vertex retains the original entire stage map. -/
theorem vertexWordValue_at (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (N : ℕ)
    (p : Word) {m : ℕ} (e : p.length = m) (h : p.kept ≤ N) :
    eqToHom (literalVertex_toSubsetAt A K L p e).symm ≫
        vertexValue A k f N (p.toSubsetAt e) ((p.card_toSubsetAt e).symm ▸ h) =
      wordValue A k f N p h := by
  let S := p.toSubsetAt e
  let ep : Word.ofSubset S = p := Word.ofSubset_toSubsetAt p e
  have hfront : eqToHom (literalVertex_toSubsetAt A K L p e).symm ≫
      eqToHom (literalVertex_eq_word A K L S) = eqToHom (congrArg (wordObj A K L) ep.symm) := by
    rw [eqToHom_trans]
  rw [vertexValue_eq_word, ← Category.assoc, hfront]
  exact wordValue_transport A k f N ep.symm h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The entire original target cocone retains each original proper-face compatibility square. -/
theorem successorTarget_face (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1))))
    (S : FiniteCube.Punctured (n + 1)) :
    vertexValue A k f n S.1 (Nat.le_of_lt_succ (FiniteCube.card_lt S)) ≫ s.inl =
      (wordCube A f (n + 1)).map (homOfLE (Finset.subset_univ S.1)) ≫ s.inr := by
  have h := congrArg (fun t => FiniteCube.boundaryι (wordCube A f (n + 1)) S ≫ t) s.condition
  simpa only [attachingFace_assoc, FiniteCube.boundaryι_boundaryToTop_assoc] using h

/-- The entire original successor target extends to its actual original finite word family. -/
def successorWordsDesc (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))) :
    stageWords A L (n + 1) ⟶ s.pt :=
  Sigma.desc (fun i : Fin (n + 2) =>
    Fin.lastCases (motive := fun j => newWordObj A L j.val ⟶ s.pt)
      (eqToHom (terminalVertex_eq A K L (n + 1)).symm ≫ s.inr)
      (fun j : Fin (n + 1) => stageWordLeg A k f n j.val (Nat.le_of_lt_succ j.isLt) ≫ s.inl) i)

/-- Every original earlier word retains its original target map in the successor extension. -/
@[reassoc (attr := simp)] theorem successorWordsDesc_old (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1))))
    (j : ℕ) (h : j ≤ n) :
    stageWordι A L (n + 1) j (h.trans (Nat.le_succ n)) ≫ successorWordsDesc A k f n s =
      stageWordLeg A k f n j h ≫ s.inl := by
  change Sigma.ι (fun i : Fin (n + 2) => newWordObj A L i.val) (⟨j, Nat.lt_succ_of_le h⟩ : Fin (n + 1)).castSucc ≫
    successorWordsDesc A k f n s = _
  dsimp only [successorWordsDesc]
  rw [Sigma.ι_comp_desc, Fin.lastCases_castSucc]

/-- The entire original new terminal word retains the original target full-word map. -/
@[reassoc (attr := simp)] theorem successorWordsDesc_new (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))) :
    stageWordι A L (n + 1) (n + 1) (Nat.le_refl _) ≫ successorWordsDesc A k f n s =
      eqToHom (terminalVertex_eq A K L (n + 1)).symm ≫ s.inr := by
  change Sigma.ι (fun i : Fin (n + 2) => newWordObj A L i.val) (Fin.last (n + 1)) ≫
    successorWordsDesc A k f n s = _
  dsimp only [successorWordsDesc]
  rw [Sigma.ι_comp_desc, Fin.lastCases_last]

/-- The same original last-word extension retains the original equality transport of its word count. -/
theorem successorWordsDesc_last (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1))))
    (j : ℕ) (e : j = n + 1) (h : j ≤ n + 1) :
    stageWordι A L (n + 1) j h ≫ successorWordsDesc A k f n s =
      eqToHom (congrArg (newWordObj A L) e) ≫ eqToHom (terminalVertex_eq A K L (n + 1)).symm ≫ s.inr := by
  subst j
  rw [successorWordsDesc_new, eqToHom_refl, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original proper word at the new stage has precisely the relation imposed by the actual attaching cube. -/
theorem successorTarget_newRelation (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1))))
    (p : Word) (e : p.length = n + 1) (hp : p.kept < p.length) :
    wordReductionToNew A k p ≫ stageWordLeg A k f n p.kept (Nat.le_of_lt_succ (hp.trans_le (Nat.le_of_eq e))) ≫ s.inl =
      wordToNewHom A f p ≫ eqToHom (congrArg (newWordObj A L) e) ≫
        eqToHom (terminalVertex_eq A K L (n + 1)).symm ≫ s.inr := by
  let S : FiniteCube.Punctured (n + 1) := p.puncturedAt e hp
  have hg := successorTarget_face A k f n s S
  have hge := congrArg (fun t => eqToHom (literalVertex_toSubsetAt A K L p e).symm ≫ t) hg
  have hv := congrArg (fun t => t ≫ s.inl)
    (vertexWordValue_at A k f n p e (Nat.le_of_lt_succ (hp.trans_le (Nat.le_of_eq e))))
  have hf := congrArg (fun t => t ≫ s.inr) (wordFullFace_at A f p e)
  simp only [Category.assoc] at hv hf hge
  simpa only [wordValue, Category.assoc] using hv.symm.trans (hge.trans hf)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original defining word relation is retained by the entire original successor target extension. -/
theorem successorWordsDesc_relations (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))) :
    stageRelationLeft A L k (n + 1) ≫ successorWordsDesc A k f n s =
      stageRelationRight A f (n + 1) ≫ successorWordsDesc A k f n s := by
  apply Sigma.hom_ext
  intro c
  have hk : c.word.kept ≤ n := Nat.le_of_lt_succ (c.proper.trans_le c.bound)
  simp only [stageRelationLeft, stageRelationRight, Sigma.ι_comp_desc_assoc, Category.assoc]
  rw [successorWordsDesc_old A k f n s c.word.kept hk]
  by_cases hc : c.word.length ≤ n
  · rw [successorWordsDesc_old A k f n s c.word.length hc]
    have h := congrArg (fun t => t ≫ s.inl) (stage_cell A k f n ⟨c.word, hc, c.proper⟩)
    simpa only [Category.assoc] using h
  · have he : c.word.length = n + 1 := Nat.le_antisymm c.bound (Nat.succ_le_of_lt (Nat.lt_of_not_ge hc))
    rw [successorWordsDesc_last A k f n s c.word.length he]
    exact successorTarget_newRelation A k f n s c.word he c.proper

/-- The actual entire original successor target has its constructed stage descender. -/
def successorDesc (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))) :
    stage A k f (n + 1) ⟶ s.pt :=
  coequalizer.desc (successorWordsDesc A k f n s) (successorWordsDesc_relations A k f n s)

/-- The actual successor descender retains the full original finite-word extension. -/
@[reassoc (attr := simp)] theorem successorDesc_word (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1))))
    (j : ℕ) (hj : j ≤ n + 1) :
    stageWordLeg A k f (n + 1) j hj ≫ successorDesc A k f n s =
      stageWordι A L (n + 1) j hj ≫ successorWordsDesc A k f n s := by
  dsimp only [stageWordLeg, successorDesc]
  rw [Category.assoc, coequalizer.π_desc]

/-- Every original predecessor word is retained by the actual successor descender. -/
@[reassoc] theorem successorDesc_word_old (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1))))
    (j : ℕ) (hj : j ≤ n) :
    stageWordLeg A k f (n + 1) j (hj.trans (Nat.le_succ n)) ≫ successorDesc A k f n s =
      stageWordLeg A k f n j hj ≫ s.inl := by
  rw [successorDesc_word, successorWordsDesc_old]

/-- The original terminal new word is retained by the actual successor descender. -/
@[reassoc (attr := simp)] theorem successorDesc_word_new (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))) :
    stageWordLeg A k f (n + 1) (n + 1) (Nat.le_refl _) ≫ successorDesc A k f n s =
      eqToHom (terminalVertex_eq A K L (n + 1)).symm ≫ s.inr := by
  rw [successorDesc_word, successorWordsDesc_new]

/-- The actual successor descender retains the entire original predecessor target map. -/
@[reassoc (attr := simp)] theorem successorDesc_old (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))) :
    stageMap A k f (Nat.le_succ n) ≫ successorDesc A k f n s = s.inl := by
  apply stage_hom_ext A k f n
  intro j hj
  rw [← Category.assoc, stageWordLeg_map, successorDesc_word_old]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual successor descender retains the entire original terminal new-word target map. -/
@[reassoc (attr := simp)] theorem successorDesc_new (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))) :
    topStageLeg A k f (n + 1) ≫ successorDesc A k f n s = s.inr := by
  dsimp only [topStageLeg]
  rw [Category.assoc, successorDesc_word_new, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original target factorization through the actual successor is uniquely its original descender. -/
theorem successorDesc_unique (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ)
    (s : PushoutCocone (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1))))
    (p : stage A k f (n + 1) ⟶ s.pt)
    (ho : stageMap A k f (Nat.le_succ n) ≫ p = s.inl)
    (hn : topStageLeg A k f (n + 1) ≫ p = s.inr) : p = successorDesc A k f n s := by
  apply stage_hom_ext A k f (n + 1)
  intro j hj
  by_cases h : j ≤ n
  · have hh := congrArg (fun t => stageWordLeg A k f n j h ≫ t) ho
    rw [← Category.assoc, stageWordLeg_map] at hh
    rw [successorDesc_word_old A k f n s j h]
    exact hh
  · have he : j = n + 1 := Nat.le_antisymm hj (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))
    subst j
    have hh := congrArg (fun t => eqToHom (terminalVertex_eq A K L (n + 1)).symm ≫ t) hn
    simp only [topStageLeg, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hh
    rw [successorDesc_word_new]
    exact hh

/-- Every actual original word-stage successor is the pushout of its entire actual original attaching cube. -/
def successorCoconeIsColimit (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    IsColimit (successorCocone A k f n) :=
  PushoutCocone.IsColimit.mk (successorSquare A k f n) (successorDesc A k f n)
    (successorDesc_old A k f n) (successorDesc_new A k f n) (successorDesc_unique A k f n)

/-- The complete original attaching source, predecessor and terminal word form an actual successor pushout. -/
theorem successorIsPushout (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    IsPushout (attachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))
      (stageMap A k f (Nat.le_succ n)) (topStageLeg A k f (n + 1)) :=
  IsPushout.of_isColimit (successorCoconeIsColimit A k f n)

end SuccessorDescenders

section OriginalStages

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair
local instance (n : ℕ) : HasColimitsOfShape (FiniteCube.Punctured n) C :=
  HasColimitsOfShape.of_essentiallySmall C (FiniteCube.Punctured n)
local instance : HasColimitsOfShape ℕ C := HasColimitsOfShape.of_essentiallySmall C ℕ

/-- The actual original word stages have the literal original monoid carrier at stage zero. -/
abbrev originalStage (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : ℕ → C
  | 0 => A.X
  | n + 1 => stage A k f (n + 1)

/-- The original zero-stage comparison and the unchanged positive-stage comparisons. -/
def stageComparison (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    (n : ℕ) → originalStage A k f n ≅ stage A k f n
  | 0 => (stageZeroIso A k f).symm
  | _ + 1 => Iso.refl _

/-- The actual original countable word-stage diagram, with its original source carrier unchanged. -/
def originalStageDiagram (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : ℕ ⥤ C where
  obj := originalStage A k f
  map {n m} h := (stageComparison A k f n).hom ≫ stageMap A k f (leOfHom h) ≫
    (stageComparison A k f m).inv
  map_id n := by
    rw [stageMap_id, Category.id_comp, Iso.hom_inv_id]
  map_comp {n m p} h h' := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun t => (stageComparison A k f n).hom ≫ t ≫ (stageComparison A k f p).inv)
        (stageMap_comp A k f (leOfHom h) (leOfHom h')).symm

/-- The entire original countable diagram has its actual pointwise original comparison. -/
def originalStageIso (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    originalStageDiagram A k f ≅ stageDiagram A k f :=
  NatIso.ofComponents (stageComparison A k f) (by
    intro n m h
    change ((stageComparison A k f n).hom ≫ stageMap A k f (leOfHom h) ≫
      (stageComparison A k f m).inv) ≫ (stageComparison A k f m).hom =
        (stageComparison A k f n).hom ≫ stageMap A k f (leOfHom h)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The original countable endpoint cocone retains every original stage map and the actual original source. -/
def originalStagesCocone (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    Cocone (originalStageDiagram A k f) :=
  (Cocone.precompose (originalStageIso A k f).hom).obj (colimit.cocone (stageDiagram A k f))

/-- The constructed endpoint is the actual colimit of the entire original word-stage diagram. -/
def originalStagesIsColimit (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    IsColimit (originalStagesCocone A k f) :=
  (IsColimit.precomposeHomEquiv (originalStageIso A k f) (colimit.cocone (stageDiagram A k f))).symm
    (colimit.isColimit (stageDiagram A k f))

/-- The actual original predecessor attaching map retains every actual original cube face. -/
def originalAttachingMap (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    attachingSource A f (n + 1) ⟶ originalStage A k f n :=
  attachingMap A k f n ≫ (stageComparison A k f n).inv

/-- The actual complete terminal word leg retains its original successor-stage comparison. -/
def originalTopStageLeg (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    (wordCube A f (n + 1)).obj Finset.univ ⟶ originalStage A k f (n + 1) :=
  topStageLeg A k f (n + 1) ≫ (stageComparison A k f (n + 1)).inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original stage successor is the actual original cube pushout, including the literal stage-zero source. -/
theorem originalSuccessorIsPushout (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    IsPushout (originalAttachingMap A k f n) (FiniteCube.boundaryToTop (wordCube A f (n + 1)))
      ((originalStageDiagram A k f).map (homOfLE (Nat.le_succ n))) (originalTopStageLeg A k f n) := by
  apply (successorIsPushout A k f n).of_iso' (Iso.refl _) (stageComparison A k f n)
    (Iso.refl _) (stageComparison A k f (n + 1))
  · simp only [Iso.refl_hom, originalAttachingMap, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · change (stageComparison A k f n).hom ≫ stageMap A k f (Nat.le_succ n) =
      ((stageComparison A k f n).hom ≫ stageMap A k f (Nat.le_succ n) ≫
        (stageComparison A k f (n + 1)).inv) ≫ (stageComparison A k f (n + 1)).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [originalTopStageLeg, Iso.refl_hom, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

/-- The original source leg of the original countable diagram is the original old-carrier endpoint map. -/
@[simp] theorem originalStages_rootMap (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    (originalStagesCocone A k f).ι.app 0 = rootMap A k f := by
  change (stageZeroIso A k f).inv ≫ stageι A k f 0 = _
  rw [stageZeroIso_inv]
  rfl

end OriginalStages

section EndpointWordLegs

universe w

variable [HasColimitsOfSize.{w, w} C]

local instance (N : ℕ) : HasColimitsOfShape (Discrete (Fin (N + 1))) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Fin (N + 1)))
local instance (N : ℕ) : HasColimitsOfShape (Discrete (CellFace N)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (CellFace N))
local instance : HasColimitsOfShape WalkingParallelPair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingParallelPair
local instance : HasColimitsOfShape ℕ C := HasColimitsOfShape.of_essentiallySmall C ℕ

/-- The entire original full word enters its actual original countable endpoint. -/
def endpointWordLeg (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) (n : ℕ) :
    newWordObj A L n ⟶ stageEndpoint A k f :=
  stageWordLeg A k f n n (Nat.le_refl n) ≫ stageι A k f n

/-- Every original later-stage inclusion retains the same original endpoint full-word leg. -/
@[reassoc (attr := simp)] theorem endpointWordLeg_atStage (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (N j : ℕ) (h : j ≤ N) :
    stageWordLeg A k f N j h ≫ stageι A k f N = endpointWordLeg A k f j := by
  dsimp only [endpointWordLeg]
  rw [← stageι_naturality A k f h, ← Category.assoc, stageWordLeg_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original countable endpoint is jointly generated by every actual original full word. -/
theorem endpoint_hom_ext (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L)
    {X : C} {g h : stageEndpoint A k f ⟶ X}
    (H : ∀ n, endpointWordLeg A k f n ≫ g = endpointWordLeg A k f n ≫ h) : g = h := by
  apply colimit.hom_ext
  intro N
  apply stage_hom_ext A k f N
  intro j hj
  change stageWordLeg A k f N j hj ≫ stageι A k f N ≫ g =
    stageWordLeg A k f N j hj ≫ stageι A k f N ≫ h
  rw [← Category.assoc, endpointWordLeg_atStage, ← Category.assoc, endpointWordLeg_atStage]
  exact H j

/-- Every original proper word face retains its entire original contraction/full-face equation at the endpoint. -/
theorem endpoint_word_relation (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L)
    (p : Word) (hp : p.kept < p.length) :
    wordReductionToNew A k p ≫ endpointWordLeg A k f p.kept =
      wordToNewHom A f p ≫ endpointWordLeg A k f p.length := by
  have h := congrArg (fun t => t ≫ stageι A k f p.length)
    (stage_cell A k f p.length ⟨p, Nat.le_refl _, hp⟩)
  simpa only [Category.assoc, endpointWordLeg_atStage] using h

/-- The actual degree-zero endpoint word leg is precisely the original monoid-carrier map. -/
@[simp] theorem endpointWordLeg_zero (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    endpointWordLeg A k f 0 = rootMap A k f := rfl

/-- The entire original compatible target retains each original full word at the countable endpoint. -/
@[reassoc (attr := simp)] theorem endpointWordLeg_evaluation (A M : Mon C) (b : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ b.hom = f ≫ g) (n : ℕ) :
    endpointWordLeg A k f n ≫ endpointEvaluation A M b k f g h = targetWord A M b (k ≫ b.hom) g n := by
  dsimp only [endpointWordLeg]
  rw [Category.assoc, stageι_endpointEvaluation, stageWordLeg_evaluate]

end EndpointWordLegs

end CategoryTheory.MonoidalCategory.MonoidWordPushout
