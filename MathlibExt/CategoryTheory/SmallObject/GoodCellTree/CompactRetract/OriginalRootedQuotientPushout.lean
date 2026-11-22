/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.OriginalRetractSplitIso
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Presentable.Retracts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Quotienting an actual original pushout with its given retract target

The original pushout UP and both actual split maps construct the new
quotient comparison and descender. The given target is retained.
The compact local arrow is an explicit identity-source Arrow retract.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.OriginalRootedQuotientPushout

open Limits

variable {C : Type u} [Category.{v} C] [HasCoequalizers C]

section Local

variable {D K : C} (r : D ⟶ K) (a : K ⟶ K)
  (ha : a ≫ a = a) (hRoot : r ≫ a = r)

/-- The actual selected coequalizer retains this same original local idempotent. -/
abbrev localObj : C := IdempotentCoequalizerSplit.obj a

/-- The actual local compact replacement retains the original root r. -/
abbrev localRoot : D ⟶ localObj a := r ≫ IdempotentCoequalizerSplit.projection a

include hRoot in
/-- The chosen local inclusion preserves the same original root function. -/
theorem local_inclusion :
    localRoot r a ≫ IdempotentCoequalizerSplit.inclusion a ha = r := by
  rw [localRoot, Category.assoc, IdempotentCoequalizerSplit.projection_inclusion, hRoot]

/-- The complete local Arrow retract has the same original source and split maps. -/
def localArrowRetract : RetractArrow (localRoot r a) r where
  i := Arrow.homMk (𝟙 D) (IdempotentCoequalizerSplit.inclusion a ha) (by
    change (𝟙 D) ≫ r = localRoot r a ≫ IdempotentCoequalizerSplit.inclusion a ha
    rw [Category.id_comp, local_inclusion r a ha hRoot])
  r := Arrow.homMk (𝟙 D) (IdempotentCoequalizerSplit.projection a) (by
    change (𝟙 D) ≫ localRoot r a = r ≫ IdempotentCoequalizerSplit.projection a
    rw [Category.id_comp])
  retract := by
    apply Arrow.hom_ext
    · change (𝟙 D) ≫ (𝟙 D) = 𝟙 D
      rw [Category.id_comp]
    · change IdempotentCoequalizerSplit.inclusion a ha ≫
        IdempotentCoequalizerSplit.projection a = 𝟙 (localObj a)
      exact IdempotentCoequalizerSplit.inclusion_projection a ha

/-- The actual target object retract uses the same selected original split functions. -/
def localObjectRetract : Retract (localObj a) K where
  i := IdempotentCoequalizerSplit.inclusion a ha
  r := IdempotentCoequalizerSplit.projection a
  retract := IdempotentCoequalizerSplit.inclusion_projection a ha

include ha hRoot in
/-- Every original retract-stable class is preserved through this actual local Arrow retract. -/
theorem local_property (Q : MorphismProperty C) [Q.IsStableUnderRetracts] (hr : Q r) :
    Q (localRoot r a) :=
  MorphismProperty.of_retract (localArrowRetract r a ha hRoot) hr

variable (chi : Cardinal.{w}) [Fact chi.IsRegular]

include ha in
/-- The actual coequalizer target is compact by its original object retract. -/
theorem localTargetPresentable [IsCardinalPresentable K chi] :
    IsCardinalPresentable (localObj a) chi :=
  (localObjectRetract a ha).isCardinalPresentable chi

include ha in
/-- Both compact ends give the entire actual local Arrow its original rank. -/
theorem localArrowPresentable [HasCardinalFilteredColimits C chi]
    [IsCardinalPresentable D chi] [IsCardinalPresentable K chi] :
    IsCardinalPresentable (Arrow.mk (localRoot r a)) chi := by
  let : IsCardinalPresentable (localObj a) chi := localTargetPresentable a ha chi
  exact Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C) (κ := chi)
    (X₁ := D) (X₂ := localObj a) (localRoot r a)

end Local

section OriginalSquare

variable {D X K Z Y : C} (v : D ⟶ X) (r : D ⟶ K)
  (n : X ⟶ Z) (q : K ⟶ Z) (H : IsPushout v r n q)
  (j : Y ⟶ Z) (p : Z ⟶ Y) (hSplit : j ≫ p = 𝟙 Y)
  (a : K ⟶ K) (ha : a ≫ a = a) (hRoot : r ≫ a = r)
  (hInter : a ≫ q = q ≫ (p ≫ j)) (hWhole : n ≫ (p ≫ j) = n)

/-- The new local comparison uses the original q and original target projection p. -/
def comparison : localObj a ⟶ Y :=
  IdempotentCoequalizerSplit.inclusion a ha ≫ q ≫ p

include hSplit hInter in
/-- The entire local projection comparison retains the original q and p functions. -/
theorem projection_comparison :
    IdempotentCoequalizerSplit.projection a ≫ comparison q p a ha = q ≫ p := by
  calc
    _ = (IdempotentCoequalizerSplit.projection a ≫
        IdempotentCoequalizerSplit.inclusion a ha) ≫ q ≫ p := by
      simp only [comparison, Category.assoc]
    _ = a ≫ q ≫ p := by rw [IdempotentCoequalizerSplit.projection_inclusion]
    _ = (a ≫ q) ≫ p := (Category.assoc _ _ _).symm
    _ = (q ≫ (p ≫ j)) ≫ p := congrArg (fun t => t ≫ p) hInter
    _ = q ≫ p := by rw [Category.assoc, Category.assoc, hSplit, Category.comp_id]

include hInter in
/-- The other complete original local comparison square also commutes. -/
theorem comparison_inclusion :
    comparison q p a ha ≫ j = IdempotentCoequalizerSplit.inclusion a ha ≫ q := by
  calc
    _ = IdempotentCoequalizerSplit.inclusion a ha ≫ (q ≫ (p ≫ j)) := by
      simp only [comparison, Category.assoc]
    _ = (IdempotentCoequalizerSplit.inclusion a ha ≫ a) ≫ q := by
      rw [← hInter, ← Category.assoc]
    _ = IdempotentCoequalizerSplit.inclusion a ha ≫ q := by
      have h : IdempotentCoequalizerSplit.inclusion a ha ≫ a =
          IdempotentCoequalizerSplit.inclusion a ha := by
        calc
          _ = IdempotentCoequalizerSplit.inclusion a ha ≫
              (IdempotentCoequalizerSplit.projection a ≫
                IdempotentCoequalizerSplit.inclusion a ha) :=
            congrArg (fun t : K ⟶ K => IdempotentCoequalizerSplit.inclusion a ha ≫ t)
              (IdempotentCoequalizerSplit.projection_inclusion a ha).symm
          _ = (IdempotentCoequalizerSplit.inclusion a ha ≫
              IdempotentCoequalizerSplit.projection a) ≫
                IdempotentCoequalizerSplit.inclusion a ha := (Category.assoc _ _ _).symm
          _ = _ := by
            rw [IdempotentCoequalizerSplit.inclusion_projection, Category.id_comp]
      rw [h]

omit [HasCoequalizers C] in
include hWhole in
/-- The original root/idempotent equation gives the actual whole inclusion square. -/
theorem whole_inclusion : (n ≫ p) ≫ j = n := by
  rw [Category.assoc, hWhole]

/-- The whole Arrow retract is derived from the same original actual split maps. -/
def wholeArrowRetract : RetractArrow (n ≫ p) n where
  i := Arrow.homMk (𝟙 X) j (by
    change (𝟙 X) ≫ n = (n ≫ p) ≫ j
    rw [Category.id_comp, whole_inclusion n j p hWhole])
  r := Arrow.homMk (𝟙 X) p (by
    change (𝟙 X) ≫ (n ≫ p) = n ≫ p
    rw [Category.id_comp])
  retract := by
    apply Arrow.hom_ext
    · change (𝟙 X) ≫ (𝟙 X) = 𝟙 X
      rw [Category.id_comp]
    · change j ≫ p = 𝟙 Y
      exact hSplit

include H hSplit hInter in
/-- The actual final quotient square retains the same original source and target. -/
theorem square :
    v ≫ (n ≫ p) = localRoot r a ≫ comparison q p a ha := by
  calc
    _ = (v ≫ n) ≫ p := (Category.assoc _ _ _).symm
    _ = (r ≫ q) ≫ p := by rw [H.w]
    _ = r ≫ (IdempotentCoequalizerSplit.projection a ≫ comparison q p a ha) := by
      rw [projection_comparison q j p hSplit a ha hInter, Category.assoc]
    _ = _ := (Category.assoc _ _ _).symm

variable {T : C} (x : X ⟶ T) (y : localObj a ⟶ T)
  (h : v ≫ x = localRoot r a ≫ y)

/-- The old descender is constructed from the ORIGINAL H and selected local projection. -/
def originalDesc : Z ⟶ T :=
  H.desc x (IdempotentCoequalizerSplit.projection a ≫ y)
    (h.trans (Category.assoc _ _ _))

/-- Its original source leg remains the same x. -/
theorem original_root_fac : n ≫ originalDesc v r n q H a x y h = x :=
  H.inl_desc _ _ _

/-- Its original local leg remains the same selected local projection followed by y. -/
theorem original_local_fac :
    q ≫ originalDesc v r n q H a x y h =
      IdempotentCoequalizerSplit.projection a ≫ y :=
  H.inr_desc _ _ _

include hInter hWhole in
/-- The original pushout UP derives invariance under the original whole split idempotent. -/
theorem original_fixed :
    (p ≫ j) ≫ originalDesc v r n q H a x y h = originalDesc v r n q H a x y h := by
  apply H.hom_ext
  · rw [← Category.assoc, hWhole]
  · rw [← Category.assoc, ← hInter, Category.assoc, original_local_fac,
      ← Category.assoc, IdempotentCoequalizerSplit.idempotent_projection]

/-- The actual final descender uses the GIVEN target inclusion j. -/
def desc : Y ⟶ T := j ≫ originalDesc v r n q H a x y h

include hWhole in
/-- The actual given target/source route recovers x through the original root equation. -/
theorem root_desc : (n ≫ p) ≫ desc v r n q H j a x y h = x := by
  rw [desc, Category.assoc, ← Category.assoc p j, ← Category.assoc,
    hWhole, original_root_fac]

include hInter in
/-- The actual given target/local route recovers y through both original split equations. -/
theorem comparison_desc :
    comparison q p a ha ≫ desc v r n q H j a x y h = y := by
  rw [desc, ← Category.assoc, comparison_inclusion q j p a ha hInter,
    Category.assoc, original_local_fac, ← Category.assoc,
    IdempotentCoequalizerSplit.inclusion_projection, Category.id_comp]

include hSplit hInter in
/-- Uniqueness uses the ORIGINAL H and the original given target retract equation. -/
theorem desc_unique (m : Y ⟶ T) (hX : (n ≫ p) ≫ m = x)
    (hY : comparison q p a ha ≫ m = y) :
    m = desc v r n q H j a x y h := by
  have hm : p ≫ m = originalDesc v r n q H a x y h := by
    apply H.hom_ext
    · rw [← Category.assoc, hX, original_root_fac]
    · calc
        _ = (q ≫ p) ≫ m := (Category.assoc _ _ _).symm
        _ = (IdempotentCoequalizerSplit.projection a ≫ comparison q p a ha) ≫ m :=
          congrArg (fun t => t ≫ m) (projection_comparison q j p hSplit a ha hInter).symm
        _ = IdempotentCoequalizerSplit.projection a ≫ y := by rw [Category.assoc, hY]
        _ = _ := (original_local_fac v r n q H a x y h).symm
  calc
    m = j ≫ (p ≫ m) := by rw [← Category.assoc, hSplit, Category.id_comp]
    _ = _ := by rw [hm]; rfl

include H hSplit hInter hWhole in
/-- The actual final pushout UP is DERIVED, with the original given target Y. -/
theorem isPushout :
    IsPushout v (localRoot r a) (n ≫ p) (comparison q p a ha) := by
  have hs := square v r n q H j p hSplit a ha hInter
  refine ⟨⟨hs⟩, ⟨PushoutCocone.IsColimit.mk hs ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact desc v r n q H j a s.inl s.inr s.condition
  · intro s
    exact root_desc v r n q H j p a hWhole s.inl s.inr s.condition
  · intro s
    exact comparison_desc v r n q H j p a ha hInter s.inl s.inr s.condition
  · intro s m hx hy
    exact desc_unique v r n q H j p hSplit a ha hInter s.inl s.inr s.condition m hx hy

/-- The original given split also constructs the selected coequalizer endpoint Iso. -/
def endpointIso : IdempotentCoequalizerSplit.obj (p ≫ j) ≅ Y :=
  OriginalRetractSplitIso.iso j p hSplit

end OriginalSquare

end CategoryTheory.SmallObject.OriginalRootedQuotientPushout
