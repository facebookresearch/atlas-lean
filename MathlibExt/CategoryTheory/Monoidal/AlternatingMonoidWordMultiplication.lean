/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.MonoidWordPushoutFiltration

/-!
# Multiplication of original alternating monoid words

Concatenating two alternating words multiplies the two adjacent original
old coefficients. Every original letter and all other coefficient factors
are retained in their original order, including the degree-zero word.

`concatMixedHom` retains the original final right action. `concatMixed`
and `wordConcat` have actual original monoid units and associative
multiplication laws, including every ordered-word and summed-degree
transport. The original K-letter reductions, K-to-L full face maps,
and evaluations into arbitrary original target monoids commute with
these maps. The carrier wrappers use the actual original full-word
normalizations. Subsequent endpoint modules use these results to
descend multiplication through the original stage relations.
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.MonoidWordPushout

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory MonObj

namespace Word

/-- Append the complete second original word to the complete first original word. -/
@[implicit_reducible]
def append (p : Word) : Word → Word
  | .nil => p
  | .snoc q b => .snoc (append p q) b

@[simp] theorem append_nil (p : Word) : p.append .nil = p := rfl

@[simp] theorem append_snoc (p q : Word) (b : Bool) :
    p.append (.snoc q b) = .snoc (p.append q) b := rfl

/-- The original degree-zero word is the left identity for ordered append. -/
@[simp] theorem nil_append (q : Word) : Word.nil.append q = q := by
  induction q with
  | nil => rfl
  | snoc q b ih => simp only [append_snoc, ih]

/-- Ordered append retains the sum of the original letter counts. -/
@[simp] theorem length_append (p q : Word) : (p.append q).length = p.length + q.length := by
  induction q with
  | nil => simp only [append_nil, length, Nat.add_zero]
  | snoc q b ih => simp only [append_snoc, length, ih, Nat.add_assoc]

/-- Ordered append retains the sum of the original new-letter counts. -/
@[simp] theorem kept_append (p q : Word) : (p.append q).kept = p.kept + q.kept := by
  induction q with
  | nil => simp only [append_nil, kept, Nat.add_zero]
  | snoc q b ih => cases b <;> simp only [append_snoc, kept, ih, Nat.add_assoc]

/-- Ordered word append is associative with every original letter retained. -/
theorem append_assoc (p q r : Word) : (p.append q).append r = p.append (q.append r) := by
  induction r with
  | nil => rfl
  | snoc r b ih => simp only [append_snoc, ih]

/-- Removing the original old slots commutes with ordered append. -/
@[simp] theorem reduced_append (p q : Word) : (p.append q).reduced = p.reduced.append q.reduced := by
  induction q with
  | nil => rfl
  | snoc q b ih => cases b <;> simp only [append_snoc, reduced, ih]

/-- Appending the two original full new words gives the original full word at their summed degree. -/
theorem allNew_append (n m : ℕ) : (allNew n).append (allNew m) = allNew (n + m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [allNew, append_snoc, ih]
    rfl

/-- The original full word of an append has precisely the two original full input words. -/
theorem fullFaceAppendEq (p q : Word) : allNew (p.append q).length = (allNew p.length).append (allNew q.length) :=
  (congrArg allNew (length_append p q)).trans (allNew_append p.length q.length).symm

end Word

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightModule

variable {A : Mon C}

/-- Tensor a right action with an arbitrary original coefficient on its left. -/
abbrev leftTensor (X : C) (M : RightModule A) : RightModule A where
  X := X ⊗ M.X
  act := (α_ X M.X A.X).hom ≫ X ◁ M.act
  act_one := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, M.act_one]
    monoidal
  act_assoc := by
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, M.act_assoc]
    simp only [whiskerLeft_comp]
    rw [associator_naturality_middle_assoc]
    monoidal

/-- Tensor an actual action map on its left without changing its right action. -/
def leftTensorMap (X : C) {M N : RightModule A} (h : M ⟶ N) : leftTensor X M ⟶ leftTensor X N where
  hom := X ◁ h.hom
  act_hom := by
    dsimp only [leftTensor]
    simp only [Category.assoc]
    rw [← whiskerLeft_comp, h.act_hom, whiskerLeft_comp, ← associator_naturality_middle_assoc]

@[simp] theorem leftTensorMap_hom (X : C) {M N : RightModule A} (h : M ⟶ N) :
    (leftTensorMap X h).hom = X ◁ h.hom := rfl

/-- Change the original left prefix without changing the actual final right action. -/
def leftPrefixMap {X Y : C} (f : X ⟶ Y) (M : RightModule A) : leftTensor X M ⟶ leftTensor Y M where
  hom := f ▷ M.X
  act_hom := by
    dsimp only [leftTensor]
    simp only [Category.assoc]
    rw [whisker_exchange, ← associator_naturality_left_assoc]

/-- Tensor original maps in both actual inputs of a left-tensored right action. -/
def leftTensorMapBoth {X Y : C} (f : X ⟶ Y) {M N : RightModule A} (g : M ⟶ N) :
    leftTensor X M ⟶ leftTensor Y N := leftTensorMap X g ≫ leftPrefixMap f N

/-- The complete two-input action map is the actual tensor of the two original carrier maps. -/
@[simp] theorem leftTensorMapBoth_hom {X Y : C} (f : X ⟶ Y) {M N : RightModule A} (g : M ⟶ N) :
    (leftTensorMapBoth f g).hom = f ⊗ₘ g.hom := by
  simp only [leftTensorMapBoth, comp_hom, leftTensorMap_hom, leftPrefixMap]
  exact (tensorHom_def' f g.hom).symm

/-- Two unchanged original inputs give the original identity action map. -/
@[simp] theorem leftTensorMapBoth_id (X : C) (M : RightModule A) :
    leftTensorMapBoth (𝟙 X) (𝟙 M) = 𝟙 (leftTensor X M) := by
  apply Hom.ext
  simp only [leftTensorMapBoth_hom, id_hom, id_tensorHom_id]

/-- Following the original right-input map retains the same original tensor map. -/
theorem leftTensorMapBoth_rightComp {X Y : C} (f : X ⟶ Y) {M N P : RightModule A}
    (g : M ⟶ N) (h : N ⟶ P) :
    leftTensorMapBoth f g ≫ leftTensorMap Y h = leftTensorMapBoth f (g ≫ h) := by
  apply Hom.ext
  simp only [comp_hom, leftTensorMapBoth_hom, leftTensorMap_hom]
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]

/-- The actual associators retain the final old right action while moving an original prefix past a snoc. -/
def leftTensorSnocHom (X : C) (M : RightModule A) (Y : C) :
    leftTensor X (snoc M Y) ⟶ snoc (leftTensor X M) Y where
  hom := (α_ X (M.X ⊗ Y) A.X).inv ≫ (α_ X M.X Y).inv ▷ A.X
  act_hom := by
    dsimp only [leftTensor, snoc, free, freeAct]
    simp only [Category.assoc, comp_whiskerRight]
    monoidal

/-- The original snoc comparison is natural in every original prefix, module, and letter map. -/
@[reassoc] theorem leftTensorSnoc_naturality {X X' Y Y' : C} (f : X ⟶ X')
    {M N : RightModule A} (g : M ⟶ N) (h : Y ⟶ Y') :
    leftTensorMapBoth f (snocMap g h) ≫ leftTensorSnocHom X' N Y' =
      leftTensorSnocHom X M Y ≫ snocMap (leftTensorMapBoth f g) h := by
  apply Hom.ext
  simp only [comp_hom, leftTensorMapBoth_hom, snocMap_hom, leftTensorSnocHom]
  monoidal

/-- Tensoring an original old-letter collapse preserves both original adjacent old multiplications. -/
theorem leftTensorSnoc_collapse (X : C) (M : RightModule A) {K : C} (k : K ⟶ A.X) :
    leftTensorSnocHom X M K ≫ collapseLast (leftTensor X M) k = leftTensorMap X (collapseLast M k) := by
  apply Hom.ext
  simp only [comp_hom, leftTensorSnocHom, collapseLast_hom, leftTensorMap_hom, leftTensor,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

/-- Every actual action map preserves the original collapse after the original snoc comparison. -/
@[reassoc] theorem leftTensorSnoc_collapse_naturality (X : C) {M N : RightModule A}
    (h : leftTensor X M ⟶ N) {K : C} (k : K ⟶ A.X) :
    leftTensorSnocHom X M K ≫ snocMap h (𝟙 K) ≫ collapseLast N k =
      leftTensorMap X (collapseLast M k) ≫ h := by
  rw [collapseLast_naturality, ← Category.assoc, leftTensorSnoc_collapse]

end RightModule

/-- Append the original word to an arbitrary original right-action prefix. -/
abbrev wordContext (A : Mon C) (K L : C) : RightModule A → Word → RightModule A
  | M, .nil => M
  | M, .snoc q b => RightModule.snoc (wordContext A K L M q) (if b then L else K)

/-- A word prefix followed by an original word is precisely its original ordered append. -/
theorem wordContext_word (A : Mon C) (K L : C) (p q : Word) :
    wordContext A K L (wordModule A K L p) q = wordModule A K L (p.append q) := by
  induction q with
  | nil => rfl
  | snoc q b ih => exact congrArg (fun M => RightModule.snoc M (if b then L else K)) ih

/-- The original concatenation into a right-action prefix, preserving the actual final right action. -/
def concatContext (A : Mon C) (K L : C) (M : RightModule A) : (q : Word) →
    RightModule.leftTensor M.X (wordModule A K L q) ⟶ wordContext A K L M q
  | .nil => RightModule.lift M (𝟙 M.X)
  | .snoc q b =>
    RightModule.leftTensorSnocHom M.X (wordModule A K L q) (if b then L else K) ≫
      RightModule.snocMap (concatContext A K L M q) (𝟙 (if b then L else K))

/-- Concatenating the degree-zero word is the original final right action. -/
@[simp] theorem concatContext_nil (A : Mon C) (K L : C) (M : RightModule A) :
    (concatContext A K L M .nil).hom = M.act := by
  simp only [concatContext, RightModule.lift_hom, id_whiskerRight, Category.id_comp]
  rfl

/-- A positive concatenation retains its original final letter and coefficient. -/
@[simp] theorem concatContext_snoc (A : Mon C) (K L : C) (M : RightModule A) (q : Word) (b : Bool) :
    (concatContext A K L M (.snoc q b)).hom =
      (α_ M.X (wordObj A K L q ⊗ (if b then L else K)) A.X).inv ≫
        (α_ M.X (wordObj A K L q) (if b then L else K)).inv ▷ A.X ≫
          ((concatContext A K L M q).hom ▷ (if b then L else K)) ▷ A.X := by
  simp only [concatContext, RightModule.comp_hom, RightModule.leftTensorSnocHom,
    RightModule.snocMap_hom, tensorHom_id, Category.assoc]

/-- The original mixed-word concatenation as a map of its actual final old right action. -/
def concatMixedHom (A : Mon C) (K L : C) (p q : Word) :
    RightModule.leftTensor (wordObj A K L p) (wordModule A K L q) ⟶ wordModule A K L (p.append q) :=
  concatContext A K L (wordModule A K L p) q ≫ eqToHom (wordContext_word A K L p q)

/-- The complete degree-zero concatenation is the original free extension by its actual right action. -/
theorem concatMixedHom_nil (A : Mon C) (K L : C) (p : Word) :
    concatMixedHom A K L p .nil = RightModule.lift (wordModule A K L p) (𝟙 (wordObj A K L p)) := by
  simp only [concatMixedHom, concatContext, eqToHom_refl]
  change RightModule.lift (wordModule A K L p) (𝟙 (wordObj A K L p)) ≫ 𝟙 (wordModule A K L p) =
    RightModule.lift (wordModule A K L p) (𝟙 (wordObj A K L p))
  exact Category.comp_id _

/-- Concatenate the original word carriers by multiplying precisely the two adjacent old coefficients. -/
abbrev concatMixed (A : Mon C) (K L : C) (p q : Word) :
    wordObj A K L p ⊗ wordObj A K L q ⟶ wordObj A K L (p.append q) :=
  (concatMixedHom A K L p q).hom

/-- The complete original right-action square of mixed-word concatenation. -/
@[reassoc] theorem concatMixed_act_hom (A : Mon C) (K L : C) (p q : Word) :
    (α_ (wordObj A K L p) (wordObj A K L q) A.X).hom ≫
        (wordObj A K L p ◁ (wordModule A K L q).act) ≫ concatMixed A K L p q =
      (concatMixed A K L p q ▷ A.X) ≫ (wordModule A K L (p.append q)).act := by
  simpa only [RightModule.leftTensor, Category.assoc] using (concatMixedHom A K L p q).act_hom

/-- Appending a final original letter extends precisely the original concatenation action map. -/
theorem concatMixedHom_snoc (A : Mon C) (K L : C) (p q : Word) (b : Bool) :
    concatMixedHom A K L p (.snoc q b) =
      RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) (if b then L else K) ≫
        RightModule.snocMap (concatMixedHom A K L p q) (𝟙 (if b then L else K)) := by
  simp only [concatMixedHom, concatContext, RightModule.snocMap_comp_id,
    RightModule.snocMap_eqToHom, Category.assoc]

/-- Concatenating the original degree-zero word performs the original final old multiplication. -/
@[simp] theorem concatMixed_nil (A : Mon C) (K L : C) (p : Word) :
    concatMixed A K L p .nil = (wordModule A K L p).act := by
  simp only [concatMixed, concatMixedHom, RightModule.comp_hom, concatContext_nil,
    RightModule.eqToHom_hom]
  change (wordModule A K L p).act ≫ 𝟙 (wordObj A K L p) = (wordModule A K L p).act
  exact Category.comp_id _

/-- Positive mixed-word concatenation retains the original final letter and original final coefficient. -/
@[simp] theorem concatMixed_snoc (A : Mon C) (K L : C) (p q : Word) (b : Bool) :
    concatMixed A K L p (.snoc q b) =
      (α_ (wordObj A K L p) (wordObj A K L q ⊗ (if b then L else K)) A.X).inv ≫
        (α_ (wordObj A K L p) (wordObj A K L q) (if b then L else K)).inv ▷ A.X ≫
          ((concatMixed A K L p q ▷ (if b then L else K)) ▷ A.X) := by
  simp only [concatMixed, concatMixedHom_snoc, RightModule.comp_hom, RightModule.leftTensorSnocHom,
    RightModule.snocMap_hom, tensorHom_id, Category.assoc]

/-- The original monoid unit is the right unit for every original mixed word. -/
@[reassoc] theorem concatMixed_rightUnit (A : Mon C) (K L : C) (p : Word) :
    (wordObj A K L p ◁ A.mon.one) ≫ concatMixed A K L p .nil = (ρ_ (wordObj A K L p)).hom := by
  rw [concatMixed_nil]
  exact (wordModule A K L p).act_one

/-- The actual associators moving an original prefix past the final letter and coefficient. -/
def snocTensor (A : Mon C) (X Y Z : C) : X ⊗ ((Y ⊗ Z) ⊗ A.X) ⟶ ((X ⊗ Y) ⊗ Z) ⊗ A.X :=
  (α_ X (Y ⊗ Z) A.X).inv ≫ (α_ X Y Z).inv ▷ A.X

/-- Moving the original prefix is natural in its complete original carrier map. -/
@[reassoc] theorem snocTensor_naturalityLeft (A : Mon C) {X X' : C} (g : X ⟶ X') (Y Z : C) :
    (g ▷ ((Y ⊗ Z) ⊗ A.X)) ≫ snocTensor A X' Y Z =
      snocTensor A X Y Z ≫ ((g ▷ Y) ▷ Z) ▷ A.X := by
  dsimp only [snocTensor]
  monoidal

/-- Moving the original prefix is natural in the complete original following-word map. -/
@[reassoc] theorem snocTensor_naturalityRight (A : Mon C) (X : C) {Y Y' : C} (g : Y ⟶ Y') (Z : C) :
    (X ◁ ((g ▷ Z) ▷ A.X)) ≫ snocTensor A X Y' Z =
      snocTensor A X Y Z ≫ ((X ◁ g) ▷ Z) ▷ A.X := by
  dsimp only [snocTensor]
  monoidal

/-- Both original ways to regroup three prefixes and a final original letter coincide. -/
@[reassoc] theorem snocTensor_assoc (A : Mon C) (X Y Z T : C) :
    (α_ X Y ((Z ⊗ T) ⊗ A.X)).hom ≫ (X ◁ snocTensor A Y Z T) ≫ snocTensor A X (Y ⊗ Z) T =
      snocTensor A (X ⊗ Y) Z T ≫ ((α_ X Y Z).hom ▷ T) ▷ A.X := by
  dsimp only [snocTensor]
  monoidal

/-- The original ambient left unit is retained while moving the final original letter and coefficient. -/
@[reassoc] theorem snocTensor_unit (A : Mon C) (Y Z : C) :
    snocTensor A (𝟙_ C) Y Z ≫ ((λ_ Y).hom ▷ Z) ▷ A.X = (λ_ ((Y ⊗ Z) ⊗ A.X)).hom := by
  dsimp only [snocTensor]
  monoidal

/-- Equality of original word prefixes transports their original final letter and coefficient maps. -/
theorem wordObj_snoc_eqToHom (A : Mon C) (K L : C) {p q : Word} (h : p = q) (b : Bool) :
    eqToHom (congrArg (wordObj A K L) (congrArg (fun w => Word.snoc w b) h)) =
      (eqToHom (congrArg (wordObj A K L) h) ▷ (if b then L else K)) ▷ A.X := by
  cases h
  simp only [eqToHom_refl, id_whiskerRight]

/-- The original monoid unit enters the original degree-zero word. -/
def wordUnit (A : Mon C) (K L : C) : 𝟙_ C ⟶ wordObj A K L .nil := A.mon.one

/-- The original monoid unit is the left unit for every original mixed word,
with the complete original word transport retained. -/
@[reassoc] theorem concatMixed_leftUnit (A : Mon C) (K L : C) : ∀ (q : Word),
    (wordUnit A K L ▷ wordObj A K L q) ≫ concatMixed A K L .nil q ≫
        eqToHom (congrArg (wordObj A K L) (Word.nil_append q)) = (λ_ (wordObj A K L q)).hom
  | .nil => by
      rw [concatMixed_nil]
      change (A.mon.one ▷ A.X) ≫ A.mon.mul ≫ 𝟙 A.X = (λ_ A.X).hom
      rw [Category.comp_id, A.mon.one_mul]
  | .snoc q b => by
      let X : C := if b then L else K
      have ht : eqToHom (congrArg (wordObj A K L) (Word.nil_append (.snoc q b))) =
          (eqToHom (congrArg (wordObj A K L) (Word.nil_append q)) ▷ X) ▷ A.X :=
        wordObj_snoc_eqToHom A K L (Word.nil_append q) b
      have hh := congrArg (fun f => (f ▷ X) ▷ A.X) (concatMixed_leftUnit A K L q)
      simp only [comp_whiskerRight] at hh
      rw [concatMixed_snoc, ht]
      simp only [Category.assoc]
      have hm : (wordUnit A K L ▷ ((wordObj A K L q ⊗ X) ⊗ A.X)) ≫
          snocTensor A (wordObj A K L .nil) (wordObj A K L q) X ≫
          ((concatMixed A K L .nil q ▷ X) ▷ A.X) ≫
          (eqToHom (congrArg (wordObj A K L) (Word.nil_append q)) ▷ X) ▷ A.X =
        (λ_ ((wordObj A K L q ⊗ X) ⊗ A.X)).hom := by
        rw [snocTensor_naturalityLeft_assoc, hh, snocTensor_unit]
      simpa only [snocTensor, Category.assoc] using hm

/-- Mixed-word concatenation is associative, with the entire original ordered-word transport retained. -/
@[reassoc] theorem concatMixed_assoc (A : Mon C) (K L : C) (p q : Word) : ∀ (r : Word),
    (concatMixed A K L p q ▷ wordObj A K L r) ≫ concatMixed A K L (p.append q) r ≫
        eqToHom (congrArg (wordObj A K L) (Word.append_assoc p q r)) =
      (α_ (wordObj A K L p) (wordObj A K L q) (wordObj A K L r)).hom ≫
        (wordObj A K L p ◁ concatMixed A K L q r) ≫ concatMixed A K L p (q.append r)
  | .nil => by
      simp only [Word.append_nil, concatMixed_nil, eqToHom_refl]
      change (concatMixed A K L p q ▷ A.X) ≫ (wordModule A K L (p.append q)).act ≫
          𝟙 (wordObj A K L (p.append q)) =
        (α_ (wordObj A K L p) (wordObj A K L q) A.X).hom ≫
          (wordObj A K L p ◁ (wordModule A K L q).act) ≫ concatMixed A K L p q
      rw [← Category.assoc, Category.comp_id]
      exact (concatMixed_act_hom A K L p q).symm
  | .snoc r b => by
      let X : C := if b then L else K
      have ht : eqToHom (congrArg (wordObj A K L) (Word.append_assoc p q (.snoc r b))) =
          (eqToHom (congrArg (wordObj A K L) (Word.append_assoc p q r)) ▷ X) ▷ A.X :=
        wordObj_snoc_eqToHom A K L (Word.append_assoc p q r) b
      have hh := congrArg (fun f => (f ▷ X) ▷ A.X) (concatMixed_assoc A K L p q r)
      simp only [comp_whiskerRight] at hh
      simp only [Word.append_snoc, concatMixed_snoc]
      rw [ht]
      simp only [whiskerLeft_comp, Category.assoc]
      have hm :
          (concatMixed A K L p q ▷ ((wordObj A K L r ⊗ X) ⊗ A.X)) ≫
            snocTensor A (wordObj A K L (p.append q)) (wordObj A K L r) X ≫
            ((concatMixed A K L (p.append q) r ▷ X) ▷ A.X) ≫
            (eqToHom (congrArg (wordObj A K L) (Word.append_assoc p q r)) ▷ X) ▷ A.X =
          (α_ (wordObj A K L p) (wordObj A K L q) ((wordObj A K L r ⊗ X) ⊗ A.X)).hom ≫
            (wordObj A K L p ◁ snocTensor A (wordObj A K L q) (wordObj A K L r) X) ≫
            (wordObj A K L p ◁ ((concatMixed A K L q r ▷ X) ▷ A.X)) ≫
            snocTensor A (wordObj A K L p) (wordObj A K L (q.append r)) X ≫
            ((concatMixed A K L p (q.append r) ▷ X) ▷ A.X) := by
        rw [snocTensor_naturalityLeft_assoc, snocTensor_naturalityRight_assoc, snocTensor_assoc_assoc]
        exact congrArg (snocTensor A (wordObj A K L p ⊗ wordObj A K L q) (wordObj A K L r) X ≫ ·) hh
      simpa only [snocTensor, whiskerLeft_comp, Category.assoc, wordObj_snoc] using hm

/-- Original equality of the first word retains the complete original concatenation square. -/
@[reassoc] theorem concatMixed_transportLeft (A : Mon C) (K L : C) {p q : Word} (h : p = q) (r : Word) :
    (eqToHom (congrArg (wordObj A K L) h) ▷ wordObj A K L r) ≫ concatMixed A K L q r =
      concatMixed A K L p r ≫ eqToHom (congrArg (wordObj A K L) (congrArg (fun w => w.append r) h)) := by
  cases h
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]

/-- Original equality of the second word retains the complete original concatenation square. -/
@[reassoc] theorem concatMixed_transportRight (A : Mon C) (K L : C) {q r : Word} (h : q = r) (p : Word) :
    (wordObj A K L p ◁ eqToHom (congrArg (wordObj A K L) h)) ≫ concatMixed A K L p r =
      concatMixed A K L p q ≫ eqToHom (congrArg (wordObj A K L) (congrArg (Word.append p) h)) := by
  cases h
  simp only [eqToHom_refl, whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- Concatenation preserves every original old-letter reduction in both original input words. -/
theorem concatMixedHom_reduction (A : Mon C) {K L : C} (k : K ⟶ A.X) (p : Word) : ∀ (q : Word),
    concatMixedHom A K L p q ≫ wordReduction A k (p.append q) ≫
      eqToHom (congrArg (wordModule A K L) (Word.reduced_append p q)) =
    RightModule.leftTensorMapBoth (wordReduction A k p).hom (wordReduction A k q) ≫
      concatMixedHom A K L p.reduced q.reduced
  | .nil => by
      apply RightModule.Hom.ext
      change (((𝟙 (wordObj A K L p) ▷ A.X) ≫ (wordModule A K L p).act) ≫
          𝟙 (wordObj A K L p)) ≫ (wordReduction A k p).hom ≫ 𝟙 (wordObj A K L p.reduced) =
        ((wordObj A K L p ◁ 𝟙 A.X) ≫ (wordReduction A k p).hom ▷ A.X) ≫
          (((𝟙 (wordObj A K L p.reduced) ▷ A.X) ≫ (wordModule A K L p.reduced).act) ≫
            𝟙 (wordObj A K L p.reduced))
      simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
      exact (wordReduction A k p).act_hom
  | .snoc q true => by
      let e := congrArg (wordModule A K L) (Word.reduced_append p q)
      rw [concatMixedHom_snoc]
      dsimp only [Word.reduced]
      rw [concatMixedHom_snoc]
      change (RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) L ≫
          RightModule.snocMap (concatMixedHom A K L p q) (𝟙 L)) ≫
          RightModule.snocMap (wordReduction A k (p.append q)) (𝟙 L) ≫
          eqToHom (congrArg (fun M => RightModule.snoc M L) e) =
        RightModule.leftTensorMapBoth (wordReduction A k p).hom
          (RightModule.snocMap (wordReduction A k q) (𝟙 L)) ≫
          (RightModule.leftTensorSnocHom (wordObj A K L p.reduced) (wordModule A K L q.reduced) L ≫
            RightModule.snocMap (concatMixedHom A K L p.reduced q.reduced) (𝟙 L))
      rw [← RightModule.snocMap_eqToHom e L]
      calc
        _ = RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) L ≫
            RightModule.snocMap
              (RightModule.leftTensorMapBoth (wordReduction A k p).hom (wordReduction A k q) ≫
                concatMixedHom A K L p.reduced q.reduced) (𝟙 L) := by
          simpa only [Category.assoc, ← RightModule.snocMap_comp_id] using
            congrArg (fun h => RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) L ≫
              RightModule.snocMap h (𝟙 L)) (concatMixedHom_reduction A k p q)
        _ = _ := by
          rw [RightModule.snocMap_comp_id, ← Category.assoc, ← RightModule.leftTensorSnoc_naturality,
            Category.assoc]
  | .snoc q false => by
      let e := congrArg (wordModule A K L) (Word.reduced_append p q)
      rw [concatMixedHom_snoc]
      dsimp only [Word.reduced]
      change (RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) K ≫
          RightModule.snocMap (concatMixedHom A K L p q) (𝟙 K)) ≫
          (RightModule.snocMap (wordReduction A k (p.append q)) (𝟙 K) ≫
            RightModule.collapseLast (wordModule A K L (p.append q).reduced) k) ≫ eqToHom e =
        RightModule.leftTensorMapBoth (wordReduction A k p).hom
          (RightModule.snocMap (wordReduction A k q) (𝟙 K) ≫
            RightModule.collapseLast (wordModule A K L q.reduced) k) ≫
          concatMixedHom A K L p.reduced q.reduced
      have hc := RightModule.collapseLast_naturality (eqToHom e) k
      calc
        _ = RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) K ≫
            RightModule.snocMap
              (RightModule.leftTensorMapBoth (wordReduction A k p).hom (wordReduction A k q) ≫
                concatMixedHom A K L p.reduced q.reduced) (𝟙 K) ≫
            RightModule.collapseLast (wordModule A K L (p.reduced.append q.reduced)) k := by
          rw [Category.assoc, Category.assoc, ← hc]
          simpa only [Category.assoc, RightModule.snocMap_comp_id] using
            congrArg (fun h => RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) K ≫
              RightModule.snocMap h (𝟙 K) ≫
                RightModule.collapseLast (wordModule A K L (p.reduced.append q.reduced)) k)
              (concatMixedHom_reduction A k p q)
        _ = _ := by
          rw [RightModule.snocMap_comp_id]
          simp only [Category.assoc]
          rw [← RightModule.leftTensorSnoc_naturality_assoc, RightModule.leftTensorSnoc_collapse_naturality,
            ← Category.assoc, RightModule.leftTensorMapBoth_rightComp]

/-- The original map of a letter slot to a new slot, including an unchanged original new letter. -/
def toNewLetter {K L : C} (f : K ⟶ L) : (b : Bool) → (if b then L else K) ⟶ L
  | false => f
  | true => 𝟙 L

/-- The original full-face map appends precisely the original letter map. -/
theorem wordToNew_snoc (A : Mon C) {K L : C} (f : K ⟶ L) (q : Word) (b : Bool) :
    wordToNew A f (.snoc q b) = RightModule.snocMap (wordToNew A f q) (toNewLetter f b) := by
  cases b <;> rfl

/-- Concatenation preserves the complete original full-face maps in both original input words. -/
theorem concatMixedHom_fullFace (A : Mon C) {K L : C} (f : K ⟶ L) (p : Word) : ∀ (q : Word),
    concatMixedHom A K L p q ≫ wordToNew A f (p.append q) ≫
      eqToHom (congrArg (wordModule A K L) (Word.fullFaceAppendEq p q)) =
    RightModule.leftTensorMapBoth (wordToNew A f p).hom (wordToNew A f q) ≫
      concatMixedHom A K L (Word.allNew p.length) (Word.allNew q.length)
  | .nil => by
      apply RightModule.Hom.ext
      change (((𝟙 (wordObj A K L p) ▷ A.X) ≫ (wordModule A K L p).act) ≫
          𝟙 (wordObj A K L p)) ≫ (wordToNew A f p).hom ≫
          𝟙 (wordObj A K L (Word.allNew p.length)) =
        ((wordObj A K L p ◁ 𝟙 A.X) ≫ (wordToNew A f p).hom ▷ A.X) ≫
          (((𝟙 (wordObj A K L (Word.allNew p.length)) ▷ A.X) ≫
            (wordModule A K L (Word.allNew p.length)).act) ≫
              𝟙 (wordObj A K L (Word.allNew p.length)))
      simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
      exact (wordToNew A f p).act_hom
  | .snoc q b => by
      let X : C := if b then L else K
      let g : X ⟶ L := toNewLetter f b
      let e := congrArg (wordModule A K L) (Word.fullFaceAppendEq p q)
      simp only [Word.append_snoc, wordToNew_snoc, Word.length, Word.allNew]
      rw [concatMixedHom_snoc]
      change (RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) X ≫
          RightModule.snocMap (concatMixedHom A K L p q) (𝟙 X)) ≫
          RightModule.snocMap (wordToNew A f (p.append q)) g ≫
          eqToHom (congrArg (fun M => RightModule.snoc M L) e) =
        RightModule.leftTensorMapBoth (wordToNew A f p).hom (RightModule.snocMap (wordToNew A f q) g) ≫
          concatMixedHom A K L (Word.allNew p.length) (.snoc (Word.allNew q.length) true)
      rw [concatMixedHom_snoc, ← RightModule.snocMap_eqToHom e L]
      calc
        _ = RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) X ≫
            RightModule.snocMap
              (RightModule.leftTensorMapBoth (wordToNew A f p).hom (wordToNew A f q) ≫
                concatMixedHom A K L (Word.allNew p.length) (Word.allNew q.length)) g := by
          simpa only [Category.assoc, ← RightModule.snocMap_comp, Category.id_comp, Category.comp_id] using
            congrArg (fun h => RightModule.leftTensorSnocHom (wordObj A K L p) (wordModule A K L q) X ≫
              RightModule.snocMap h g) (concatMixedHom_fullFace A f p q)
        _ = _ := by
          have hs := RightModule.snocMap_comp
            (RightModule.leftTensorMapBoth (wordToNew A f p).hom (wordToNew A f q))
            (concatMixedHom A K L (Word.allNew p.length) (Word.allNew q.length)) g (𝟙 L)
          rw [Category.comp_id] at hs
          rw [hs, ← Category.assoc, ← RightModule.leftTensorSnoc_naturality, Category.assoc]
          rfl

/-- Evaluate one original final letter and its original adjacent old coefficient. -/
def evaluateSnoc (A M : Mon C) (b : A ⟶ M) {P X : C} (e : P ⟶ M.X) (x : X ⟶ M.X) :
    (P ⊗ X) ⊗ A.X ⟶ M.X :=
  (((e ⊗ₘ x) ≫ M.mon.mul) ▷ A.X) ≫ (M.X ◁ b.hom) ≫ M.mon.mul

/-- Evaluation of a final letter and old coefficient preserves the actual original target multiplication. -/
@[reassoc] theorem evaluateSnoc_mul (A M : Mon C) (b : A ⟶ M) {P Q X : C}
    (e : P ⟶ M.X) (h : Q ⟶ M.X) (x : X ⟶ M.X) :
    snocTensor A P Q X ≫ evaluateSnoc A M b ((e ⊗ₘ h) ≫ M.mon.mul) x =
      (e ⊗ₘ evaluateSnoc A M b h x) ≫ M.mon.mul := by
  dsimp only [evaluateSnoc, snocTensor]
  simp only [mon_tauto]

/-- Evaluation of an original final slot retains every original preceding carrier map. -/
@[reassoc] theorem evaluateSnoc_precompose (A M : Mon C) (b : A ⟶ M) {P Q X : C}
    (c : P ⟶ Q) (e : Q ⟶ M.X) (x : X ⟶ M.X) :
    ((c ▷ X) ▷ A.X) ≫ evaluateSnoc A M b e x = evaluateSnoc A M b (c ≫ e) x := by
  have hp : (c ▷ X) ≫ (e ⊗ₘ x) = (c ≫ e) ⊗ₘ x := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  calc
    _ = ((((c ▷ X) ≫ (e ⊗ₘ x)) ≫ M.mon.mul) ▷ A.X) ≫ (M.X ◁ b.hom) ≫ M.mon.mul := by
      simp only [evaluateSnoc, comp_whiskerRight, Category.assoc]
    _ = _ := by rw [hp]; rfl

/-- The original value of a mixed letter slot under the original old and new input maps. -/
def evaluationLetter {K L : C} (M : Mon C) (x : K ⟶ M.X) (g : L ⟶ M.X) :
    (b : Bool) → (if b then L else K) ⟶ M.X
  | false => x
  | true => g

/-- The complete original word evaluation appends the original slot value and old coefficient. -/
@[simp] theorem evaluateWord_snoc_hom (A M : Mon C) (b : A ⟶ M) {K L : C}
    (x : K ⟶ M.X) (g : L ⟶ M.X) (q : Word) (c : Bool) :
    (evaluateWord A M b x g (.snoc q c)).hom =
      evaluateSnoc A M b (evaluateWord A M b x g q).hom (evaluationLetter M x g c) := by
  cases c <;> simp only [evaluateWord, evaluationLetter, RightModule.lift_hom,
    RightModule.restrict, evaluateSnoc]

/-- The original full word evaluation preserves concatenation and the original target monoid multiplication. -/
@[reassoc] theorem concatMixed_evaluate (A M : Mon C) (b : A ⟶ M) {K L : C}
    (x : K ⟶ M.X) (g : L ⟶ M.X) (p : Word) : ∀ (q : Word),
    concatMixed A K L p q ≫ (evaluateWord A M b x g (p.append q)).hom =
      ((evaluateWord A M b x g p).hom ⊗ₘ (evaluateWord A M b x g q).hom) ≫ M.mon.mul
  | .nil => by
      have h : (wordModule A K L p).act ≫ (evaluateWord A M b x g p).hom =
          ((evaluateWord A M b x g p).hom ⊗ₘ b.hom) ≫ M.mon.mul := by
        rw [tensorHom_def, Category.assoc]
        exact (evaluateWord A M b x g p).act_hom
      simp only [Word.append_nil, concatMixed_nil, evaluateWord, RightModule.ofMonHom]
      change (wordModule A K L p).act ≫ (evaluateWord A M b x g p).hom =
        ((evaluateWord A M b x g p).hom ⊗ₘ b.hom) ≫ M.mon.mul
      exact h
  | .snoc q c => by
      let X : C := if c then L else K
      let v : X ⟶ M.X := evaluationLetter M x g c
      simp only [Word.append_snoc, evaluateWord_snoc_hom, concatMixed_snoc, Category.assoc]
      have hm : snocTensor A (wordObj A K L p) (wordObj A K L q) X ≫
          ((concatMixed A K L p q ▷ X) ▷ A.X) ≫
          evaluateSnoc A M b (evaluateWord A M b x g (p.append q)).hom v =
        ((evaluateWord A M b x g p).hom ⊗ₘ evaluateSnoc A M b (evaluateWord A M b x g q).hom v) ≫
          M.mon.mul := by
        rw [evaluateSnoc_precompose, concatMixed_evaluate A M b x g p q, evaluateSnoc_mul]
      simpa only [snocTensor, Category.assoc] using hm

/-- Concatenate the actual full new words at their original summed degree. -/
def wordConcat (A : Mon C) (L : C) (n m : ℕ) :
    newWordObj A L n ⊗ newWordObj A L m ⟶ newWordObj A L (n + m) :=
  concatMixed A L L (Word.allNew n) (Word.allNew m) ≫
    eqToHom (congrArg (wordObj A L L) (Word.allNew_append n m))

/-- Full-new-word concatenation is a map of its actual final original right action. -/
def wordConcatHom (A : Mon C) (L : C) (n m : ℕ) :
    RightModule.leftTensor (newWordObj A L n) (wordModule A L L (Word.allNew m)) ⟶
      wordModule A L L (Word.allNew (n + m)) :=
  concatMixedHom A L L (Word.allNew n) (Word.allNew m) ≫
    eqToHom (congrArg (wordModule A L L) (Word.allNew_append n m))

/-- The actual complete action map has precisely the original full-new-word carrier map. -/
@[simp] theorem wordConcatHom_hom (A : Mon C) (L : C) (n m : ℕ) :
    (wordConcatHom A L n m).hom = wordConcat A L n m := by
  simp only [wordConcatHom, RightModule.comp_hom, RightModule.eqToHom_hom, wordConcat, concatMixed]

/-- A positive complete action concatenation retains the actual original letter and coefficient. -/
theorem wordConcatHom_snoc (A : Mon C) (L : C) (n m : ℕ) :
    wordConcatHom A L n (m + 1) =
      RightModule.leftTensorSnocHom (newWordObj A L n) (wordModule A L L (Word.allNew m)) L ≫
        RightModule.snocMap (wordConcatHom A L n m) (𝟙 L) := by
  simp only [wordConcatHom, Word.allNew, concatMixedHom_snoc, RightModule.snocMap_comp_id,
    RightModule.snocMap_eqToHom, Category.assoc]
  rfl

/-- Degree-zero right concatenation is the original old right action. -/
@[simp] theorem wordConcat_zero_right (A : Mon C) (L : C) (n : ℕ) :
    wordConcat A L n 0 = (wordModule A L L (Word.allNew n)).act := by
  dsimp only [wordConcat, Word.allNew]
  rw [concatMixed_nil]
  change (wordModule A L L (Word.allNew n)).act ≫ 𝟙 (newWordObj A L n) =
    (wordModule A L L (Word.allNew n)).act
  exact Category.comp_id _

/-- Every positive concatenation retains the original new letter and final old coefficient. -/
@[simp] theorem wordConcat_succ (A : Mon C) (L : C) (n m : ℕ) :
    wordConcat A L n (m + 1) = snocTensor A (newWordObj A L n) (newWordObj A L m) L ≫
      (wordConcat A L n m ▷ L) ▷ A.X := by
  have h := congrArg RightModule.Hom.hom (wordConcatHom_snoc A L n m)
  simpa only [wordConcatHom_hom, RightModule.comp_hom, RightModule.leftTensorSnocHom,
    RightModule.snocMap_hom, tensorHom_id, snocTensor, Category.assoc] using h

/-- The actual original monoid unit is the right unit in every full new-word degree. -/
@[reassoc] theorem wordConcat_rightUnit (A : Mon C) (L : C) (n : ℕ) :
    (newWordObj A L n ◁ A.mon.one) ≫ wordConcat A L n 0 = (ρ_ (newWordObj A L n)).hom := by
  rw [wordConcat_zero_right]
  exact (wordModule A L L (Word.allNew n)).act_one

/-- The original monoid unit enters its original full-new-word degree zero. -/
def newWordUnit (A : Mon C) (L : C) : 𝟙_ C ⟶ newWordObj A L 0 := A.mon.one

/-- The actual original monoid unit is the left unit, with the complete original zero-addition transport. -/
@[reassoc] theorem wordConcat_leftUnit (A : Mon C) (L : C) (m : ℕ) :
    (newWordUnit A L ▷ newWordObj A L m) ≫ wordConcat A L 0 m ≫
      eqToHom (congrArg (newWordObj A L) (Nat.zero_add m)) = (λ_ (newWordObj A L m)).hom := by
  have ht : eqToHom (congrArg (wordObj A L L) (Word.allNew_append 0 m)) ≫
      eqToHom (congrArg (newWordObj A L) (Nat.zero_add m)) =
      eqToHom (congrArg (wordObj A L L) (Word.nil_append (Word.allNew m))) := by
    rw [eqToHom_trans]
    rfl
  have hm : (newWordUnit A L ▷ newWordObj A L m) ≫
      (concatMixed A L L (Word.allNew 0) (Word.allNew m) ≫
        eqToHom (congrArg (wordObj A L L) (Word.allNew_append 0 m))) ≫
        eqToHom (congrArg (newWordObj A L) (Nat.zero_add m)) = (λ_ (newWordObj A L m)).hom := by
    rw [Category.assoc, ht]
    exact concatMixed_leftUnit A L L (Word.allNew m)
  exact hm

/-- Full-new-word concatenation is associative with the original summed-degree transport retained. -/
@[reassoc] theorem wordConcat_assoc (A : Mon C) (L : C) (n m k : ℕ) :
    (wordConcat A L n m ▷ newWordObj A L k) ≫ wordConcat A L (n + m) k ≫
      eqToHom (congrArg (newWordObj A L) (Nat.add_assoc n m k)) =
    (α_ (newWordObj A L n) (newWordObj A L m) (newWordObj A L k)).hom ≫
      (newWordObj A L n ◁ wordConcat A L m k) ≫ wordConcat A L n (m + k) := by
  have h := congrArg (fun f => f ≫
      eqToHom (congrArg (wordObj A L L) (congrArg (Word.append (Word.allNew n)) (Word.allNew_append m k))) ≫
      eqToHom (congrArg (wordObj A L L) (Word.allNew_append n (m + k))))
    (concatMixed_assoc A L L (Word.allNew n) (Word.allNew m) (Word.allNew k))
  simp only [wordConcat, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [concatMixed_transportLeft_assoc A L L (Word.allNew_append n m) (Word.allNew k),
    concatMixed_transportRight_assoc A L L (Word.allNew_append m k) (Word.allNew n)]
  simpa only [Category.assoc, eqToHom_trans] using h

/-- The complete original old right-action square of full-new-word concatenation. -/
@[reassoc] theorem wordConcat_act_hom (A : Mon C) (L : C) (n m : ℕ) :
    (α_ (newWordObj A L n) (newWordObj A L m) A.X).hom ≫
      (newWordObj A L n ◁ (wordModule A L L (Word.allNew m)).act) ≫ wordConcat A L n m =
    (wordConcat A L n m ▷ A.X) ≫ (wordModule A L L (Word.allNew (n + m))).act := by
  simpa only [RightModule.leftTensor, Category.assoc, wordConcatHom_hom] using
    (wordConcatHom A L n m).act_hom

/-- A full new word uses precisely the same actual module when its unused old-letter object changes. -/
theorem allNewModuleEq (A : Mon C) (K L : C) : ∀ (n : ℕ),
    wordModule A K L (Word.allNew n) = wordModule A L L (Word.allNew n)
  | 0 => rfl
  | n + 1 => congrArg (fun M => RightModule.snoc M L) (allNewModuleEq A K L n)

/-- The original full word's actual complete right-action normalization. -/
def normalizeNewWord (A : Mon C) (K L : C) (n : ℕ) :
    wordModule A K L (Word.allNew n) ⟶ wordModule A L L (Word.allNew n) :=
  eqToHom (allNewModuleEq A K L n)

/-- Full-word normalization has precisely the original full-word carrier transport. -/
@[simp] theorem normalizeNewWord_hom (A : Mon C) (K L : C) (n : ℕ) :
    (normalizeNewWord A K L n).hom = eqToHom (wordObj_allNew A K L n) := by
  simp only [normalizeNewWord, RightModule.eqToHom_hom]

/-- The original degree-zero full-word normalization is the actual identity. -/
@[simp] theorem normalizeNewWord_zero (A : Mon C) (K L : C) :
    normalizeNewWord A K L 0 = 𝟙 (RightModule.regular A) := rfl

/-- Full-word normalization retains the actual original final new letter and old coefficient. -/
theorem normalizeNewWord_snoc (A : Mon C) (K L : C) (n : ℕ) :
    normalizeNewWord A K L (n + 1) = RightModule.snocMap (normalizeNewWord A K L n) (𝟙 L) := by
  dsimp only [normalizeNewWord]
  rw [RightModule.snocMap_eqToHom]
  rfl

/-- The original full-new-word concatenation before its unused old-object normalization. -/
def originalNewConcatHom (A : Mon C) (K L : C) (n m : ℕ) :
    RightModule.leftTensor (wordObj A K L (Word.allNew n)) (wordModule A K L (Word.allNew m)) ⟶
      wordModule A K L (Word.allNew (n + m)) :=
  concatMixedHom A K L (Word.allNew n) (Word.allNew m) ≫
    eqToHom (congrArg (wordModule A K L) (Word.allNew_append n m))

/-- The positive original full-word map appends the unchanged original new slot. -/
theorem originalNewConcatHom_snoc (A : Mon C) (K L : C) (n m : ℕ) :
    originalNewConcatHom A K L n (m + 1) =
      RightModule.leftTensorSnocHom (wordObj A K L (Word.allNew n))
        (wordModule A K L (Word.allNew m)) L ≫
      RightModule.snocMap (originalNewConcatHom A K L n m) (𝟙 L) := by
  simp only [originalNewConcatHom, Word.allNew, concatMixedHom_snoc, RightModule.snocMap_comp_id,
    RightModule.snocMap_eqToHom, Category.assoc]
  rfl

/-- Full new-word concatenation retains the complete original unused-old-object normalization square. -/
theorem originalNewConcatHom_normalize (A : Mon C) (K L : C) (n : ℕ) : ∀ (m : ℕ),
    originalNewConcatHom A K L n m ≫ normalizeNewWord A K L (n + m) =
      RightModule.leftTensorMapBoth (normalizeNewWord A K L n).hom (normalizeNewWord A K L m) ≫
        wordConcatHom A L n m
  | 0 => by
      apply RightModule.Hom.ext
      change ((((𝟙 (wordObj A K L (Word.allNew n)) ▷ A.X) ≫
          (wordModule A K L (Word.allNew n)).act) ≫ 𝟙 (wordObj A K L (Word.allNew n))) ≫
          𝟙 (wordObj A K L (Word.allNew n))) ≫ (normalizeNewWord A K L n).hom =
        ((wordObj A K L (Word.allNew n) ◁ 𝟙 A.X) ≫ (normalizeNewWord A K L n).hom ▷ A.X) ≫
          ((((𝟙 (newWordObj A L n) ▷ A.X) ≫ (wordModule A L L (Word.allNew n)).act) ≫
            𝟙 (newWordObj A L n)) ≫ 𝟙 (newWordObj A L n))
      simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
      exact (normalizeNewWord A K L n).act_hom
  | m + 1 => by
      rw [originalNewConcatHom_snoc, wordConcatHom_snoc, normalizeNewWord_snoc]
      have hn : normalizeNewWord A K L (n + (m + 1)) =
          RightModule.snocMap (normalizeNewWord A K L (n + m)) (𝟙 L) := by
        simpa only [Nat.add_succ] using normalizeNewWord_snoc A K L (n + m)
      rw [hn]
      change (RightModule.leftTensorSnocHom (wordObj A K L (Word.allNew n))
          (wordModule A K L (Word.allNew m)) L ≫
          RightModule.snocMap (originalNewConcatHom A K L n m) (𝟙 L)) ≫
          RightModule.snocMap (normalizeNewWord A K L (n + m)) (𝟙 L) =
        RightModule.leftTensorMapBoth (normalizeNewWord A K L n).hom
          (RightModule.snocMap (normalizeNewWord A K L m) (𝟙 L)) ≫
          (RightModule.leftTensorSnocHom (newWordObj A L n) (wordModule A L L (Word.allNew m)) L ≫
            RightModule.snocMap (wordConcatHom A L n m) (𝟙 L))
      calc
        _ = RightModule.leftTensorSnocHom (wordObj A K L (Word.allNew n))
            (wordModule A K L (Word.allNew m)) L ≫
            RightModule.snocMap
              (RightModule.leftTensorMapBoth (normalizeNewWord A K L n).hom (normalizeNewWord A K L m) ≫
                wordConcatHom A L n m) (𝟙 L) := by
          simpa only [Category.assoc, ← RightModule.snocMap_comp_id] using
            congrArg (fun h => RightModule.leftTensorSnocHom (wordObj A K L (Word.allNew n))
              (wordModule A K L (Word.allNew m)) L ≫ RightModule.snocMap h (𝟙 L))
              (originalNewConcatHom_normalize A K L n m)
        _ = _ := by
          rw [RightModule.snocMap_comp_id, ← Category.assoc, ← RightModule.leftTensorSnoc_naturality,
            Category.assoc]

/-- The complete original full-new-word carrier normalization preserves concatenation. -/
@[reassoc] theorem concatMixed_allNewNormalize (A : Mon C) (K L : C) (n m : ℕ) :
    concatMixed A K L (Word.allNew n) (Word.allNew m) ≫
      eqToHom (congrArg (wordObj A K L) (Word.allNew_append n m)) ≫
      eqToHom (wordObj_allNew A K L (n + m)) =
    (eqToHom (wordObj_allNew A K L n) ⊗ₘ eqToHom (wordObj_allNew A K L m)) ≫ wordConcat A L n m := by
  have h := congrArg RightModule.Hom.hom (originalNewConcatHom_normalize A K L n m)
  simpa only [originalNewConcatHom, RightModule.comp_hom, RightModule.eqToHom_hom,
    normalizeNewWord_hom, RightModule.leftTensorMapBoth_hom, wordConcatHom_hom, concatMixed,
    Category.assoc] using h

/-- Original equalities of both input words retain the entire original concatenation square. -/
@[reassoc] theorem concatMixed_transportBoth (A : Mon C) (K L : C)
    {p p' q q' : Word} (hp : p = p') (hq : q = q') :
    (eqToHom (congrArg (wordObj A K L) hp) ⊗ₘ eqToHom (congrArg (wordObj A K L) hq)) ≫
        concatMixed A K L p' q' =
      concatMixed A K L p q ≫ eqToHom (congrArg (wordObj A K L)
        ((congrArg (fun w => w.append q) hp).trans (congrArg (Word.append p') hq))) := by
  cases hp
  cases hq
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- Concatenation retains the actual normalized old-letter contraction maps in both original words. -/
@[reassoc] theorem concatMixed_reductionToNew (A : Mon C) {K L : C} (k : K ⟶ A.X) (p q : Word) :
    concatMixed A K L p q ≫ wordReductionToNew A k (p.append q) ≫
      eqToHom (congrArg (newWordObj A L) (Word.kept_append p q)) =
    (wordReductionToNew A k p ⊗ₘ wordReductionToNew A k q) ≫ wordConcat A L p.kept q.kept := by
  let hpq := (congrArg (fun w => w.append q.reduced) p.reduced_eq).trans
    (congrArg (Word.append (Word.allNew p.kept)) q.reduced_eq)
  let t : wordObj A K L (p.reduced.append q.reduced) ⟶ newWordObj A L (p.kept + q.kept) :=
    eqToHom (congrArg (wordObj A K L) hpq) ≫
      eqToHom (congrArg (wordObj A K L) (Word.allNew_append p.kept q.kept)) ≫
      eqToHom (wordObj_allNew A K L (p.kept + q.kept))
  have hb := congrArg RightModule.Hom.hom (concatMixedHom_reduction A (L := L) k p q)
  simp only [RightModule.comp_hom, RightModule.eqToHom_hom, RightModule.leftTensorMapBoth_hom] at hb
  change concatMixed A K L p q ≫ (wordReduction A k (p.append q)).hom ≫
      eqToHom (congrArg (wordObj A K L) (Word.reduced_append p q)) =
    ((wordReduction A k p).hom ⊗ₘ (wordReduction A k q).hom) ≫
      concatMixed A K L p.reduced q.reduced at hb
  have h := congrArg (fun f => f ≫ t) hb
  dsimp only [t, hpq] at h
  simp only [Category.assoc] at h
  rw [← concatMixed_transportBoth_assoc A K L p.reduced_eq q.reduced_eq,
    concatMixed_allNewNormalize A K L p.kept q.kept] at h
  simp only [← Category.assoc, tensorHom_comp_tensorHom] at h
  simpa only [wordReductionToNew, reducedWord_eq, Category.assoc, eqToHom_trans] using h

/-- Concatenation retains the complete actual normalized original K-to-L face maps in both input words. -/
@[reassoc] theorem concatMixed_wordToNewHom (A : Mon C) {K L : C} (f : K ⟶ L) (p q : Word) :
    concatMixed A K L p q ≫ wordToNewHom A f (p.append q) ≫
      eqToHom (congrArg (newWordObj A L) (Word.length_append p q)) =
    (wordToNewHom A f p ⊗ₘ wordToNewHom A f q) ≫ wordConcat A L p.length q.length := by
  let t : wordObj A K L ((Word.allNew p.length).append (Word.allNew q.length)) ⟶
      newWordObj A L (p.length + q.length) :=
    eqToHom (congrArg (wordObj A K L) (Word.allNew_append p.length q.length)) ≫
      eqToHom (wordObj_allNew A K L (p.length + q.length))
  have hb := congrArg RightModule.Hom.hom (concatMixedHom_fullFace A f p q)
  simp only [RightModule.comp_hom, RightModule.eqToHom_hom, RightModule.leftTensorMapBoth_hom] at hb
  change concatMixed A K L p q ≫ (wordToNew A f (p.append q)).hom ≫
      eqToHom (congrArg (wordObj A K L) (Word.fullFaceAppendEq p q)) =
    ((wordToNew A f p).hom ⊗ₘ (wordToNew A f q).hom) ≫
      concatMixed A K L (Word.allNew p.length) (Word.allNew q.length) at hb
  have h := congrArg (fun f => f ≫ t) hb
  dsimp only [t] at h
  simp only [Category.assoc] at h
  rw [concatMixed_allNewNormalize A K L p.length q.length] at h
  simp only [← Category.assoc, tensorHom_comp_tensorHom] at h
  simpa only [wordToNewHom, Category.assoc, eqToHom_trans] using h

/-- The original full-word normalization preserves its complete original target evaluation. -/
@[reassoc (attr := simp)] theorem normalizedWord_targetWord (A M : Mon C) (b : A ⟶ M) {K L : C}
    (x : K ⟶ M.X) (g : L ⟶ M.X) (n : ℕ) :
    eqToHom (wordObj_allNew A K L n) ≫ targetWord A M b x g n =
      (evaluateWord A M b x g (Word.allNew n)).hom := by
  dsimp only [targetWord]
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- The original full-word target evaluation preserves concatenation for arbitrary original old-letter values. -/
@[reassoc] theorem wordConcat_targetWord (A M : Mon C) (b : A ⟶ M) {K L : C}
    (x : K ⟶ M.X) (g : L ⟶ M.X) (n m : ℕ) :
    wordConcat A L n m ≫ targetWord A M b x g (n + m) =
      (targetWord A M b x g n ⊗ₘ targetWord A M b x g m) ≫ M.mon.mul := by
  apply (cancel_epi (eqToHom (wordObj_allNew A K L n) ⊗ₘ eqToHom (wordObj_allNew A K L m))).mp
  calc
    _ = concatMixed A K L (Word.allNew n) (Word.allNew m) ≫
        eqToHom (congrArg (wordObj A K L) (Word.allNew_append n m)) ≫
        eqToHom (wordObj_allNew A K L (n + m)) ≫ targetWord A M b x g (n + m) := by
      rw [← Category.assoc, ← concatMixed_allNewNormalize]
      simp only [Category.assoc]
    _ = ((evaluateWord A M b x g (Word.allNew n)).hom ⊗ₘ
        (evaluateWord A M b x g (Word.allNew m)).hom) ≫ M.mon.mul := by
      rw [normalizedWord_targetWord, evaluateWord_transport A M b x g (Word.allNew_append n m)]
      exact concatMixed_evaluate A M b x g (Word.allNew n) (Word.allNew m)
    _ = _ := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, normalizedWord_targetWord, normalizedWord_targetWord]















end CategoryTheory.MonoidalCategory.MonoidWordPushout
