/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordsSubstitution

/-!
# Same-label Hom equivalences on whole relative words

A genuine functor on the original categories that keeps every individual
label and is bijective on each original Hom is bijective on complete
normalized relative words with the same supplied new-arrow family.
The inverse is constructed from its actual Hom inverses and retains
every original segment and new letter.
-/

noncomputable section
universe u v w vD
open CategoryTheory

namespace CategoryTheory.RelativeWords

variable {O : Type u} (C : Category.{v} O) (D : Category.{vD} O)
  (G : O → O → Type w)
  (m : ∀ {a b : O}, @Quiver.Hom O C.toQuiver a b → @Quiver.Hom O D.toQuiver a b)
  (hId : ∀ a, m (@CategoryStruct.id O C.toCategoryStruct a) =
    @CategoryStruct.id O D.toCategoryStruct a)
  (hComp : ∀ {a b c : O} (f : @Quiver.Hom O C.toQuiver a b)
    (g : @Quiver.Hom O C.toQuiver b c),
    m (@CategoryStruct.comp O C.toCategoryStruct a b c f g) =
      @CategoryStruct.comp O D.toCategoryStruct a b c (m f) (m g))

/-- The original Hom maps form the genuine functor on the same individual labels. -/
def sameLabelFunctor : @Functor O C O D :=
  @Functor.mk O C O D (fun a => a) m hId hComp

/-- Relabel every old segment by its actual Hom map and keep every supplied new letter. -/
def mapSameLabel {a b : O} (p : @Word O C G a b) : @Word O D G a b :=
  @substitute O C G O D G (sameLabelFunctor C D m hId hComp)
    (fun {_ _} g => @generator O D G _ _ g) a b p

/-- The same-label whole-word map retains every original old segment. -/
theorem mapSameLabel_old {a b : O} (f : @Quiver.Hom O C.toQuiver a b) :
    mapSameLabel C D G m hId hComp (@Word.old O C G a b f) =
      @Word.old O D G a b (m f) := rfl

/-- The same-label whole-word map retains the complete original cons decomposition. -/
theorem mapSameLabel_cons {a x y b : O} (f : @Quiver.Hom O C.toQuiver a x)
    (g : G x y) (p : @Word O C G y b) :
    mapSameLabel C D G m hId hComp (@Word.cons O C G a x y b f g p) =
      @Word.cons O D G a x y b (m f) g (mapSameLabel C D G m hId hComp p) := by
  rw [mapSameLabel, substitute_cons]
  exact (@Word.assoc O D G _ _ _ _ _ _ _).symm.trans
    (@cons_eq_comp O D G _ _ _ _ _ _ _).symm

/-- The original same-label whole-word map preserves literal concatenation. -/
theorem mapSameLabel_comp {a b c : O} (p : @Word O C G a b) (q : @Word O C G b c) :
    mapSameLabel C D G m hId hComp (@Word.comp O C G a b c p q) =
      @Word.comp O D G a b c (mapSameLabel C D G m hId hComp p)
        (mapSameLabel C D G m hId hComp q) :=
  @substitute_comp O C G O D G (sameLabelFunctor C D m hId hComp) _ a b c p q

variable (hm : ∀ a b, Function.Bijective (@m a b))

/-- Read the actual original Hom inverse at its unchanged endpoints. -/
def inverseHom {a b : O} : @Quiver.Hom O D.toQuiver a b → @Quiver.Hom O C.toQuiver a b :=
  (Equiv.ofBijective (@m a b) (hm a b)).symm

/-- Read each whole word back using actual old-Hom inverses and its same new letters. -/
def inverseWord : {a b : O} → @Word O D G a b → @Word O C G a b
  | _, _, .old f => @Word.old O C G _ _ (inverseHom C D m hm f)
  | _, _, .cons f g p => @Word.cons O C G _ _ _ _ (inverseHom C D m hm f) g (inverseWord p)

/-- Whole old-Hom inverse readback fixes every full original word. -/
theorem inverseWord_mapSameLabel {a b : O} (p : @Word O C G a b) :
    inverseWord C D G m hm (mapSameLabel C D G m hId hComp p) = p := by
  induction p with
  | old f =>
      rw [mapSameLabel_old]
      exact congrArg (@Word.old O C G _ _) (Equiv.symm_apply_apply _ f)
  | cons f g p ih =>
      rw [mapSameLabel_cons]
      change Word.cons _ _ _ = _
      rw [ih]
      exact congrArg (fun f => @Word.cons O C G _ _ _ _ f g p) (Equiv.symm_apply_apply _ f)

/-- Whole original Hom mapping recovers every full target word. -/
theorem mapSameLabel_inverseWord {a b : O} (p : @Word O D G a b) :
    mapSameLabel C D G m hId hComp (inverseWord C D G m hm p) = p := by
  induction p with
  | old f =>
      rw [inverseWord, mapSameLabel_old]
      exact congrArg (@Word.old O D G _ _) (Equiv.apply_symm_apply (Equiv.ofBijective (@m _
        _) (hm _ _)) f)
  | cons f g p ih =>
      rw [inverseWord, mapSameLabel_cons, ih]
      exact congrArg (fun f => @Word.cons O D G _ _ _ _ f g p) (Equiv.apply_symm_apply
        (Equiv.ofBijective (@m _ _)
        (hm _ _)) f)

include hm in
/-- The actual same-label word map is bijective on every complete original Hom. -/
theorem mapSameLabel_bijective (a b : O) :
    Function.Bijective (@mapSameLabel O C D G m hId hComp a b) :=
  ⟨Function.LeftInverse.injective (inverseWord_mapSameLabel C D G m hId hComp hm),
    Function.RightInverse.surjective (mapSameLabel_inverseWord C D G m hId hComp hm)⟩

end CategoryTheory.RelativeWords
