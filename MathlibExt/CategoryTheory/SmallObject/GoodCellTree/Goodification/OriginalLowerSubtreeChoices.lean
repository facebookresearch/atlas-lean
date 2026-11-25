/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerRestriction

/-!
# Original lower-colimit choices inside an original lower subtree

A lower subset of a lower subtree is lifted to its literal original
cell-label subset. Its selected point, cofan and comparisons are the
original whole-tree choices. This allows compact attaching-source capture
inside its original predecessor lower subtree without selecting new points.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.OriginalLowerSubtreeChoices

open Limits LowerSetColimits

variable {P : Type w} [PartialOrder P] (B : LowerSet P)

/-- The literal original lower support represented by a lower subset of the lower subtree. -/
def lift (D : LowerSet B) : LowerSet P where
  carrier := {p | ∃ hp : p ∈ B, (⟨p, hp⟩ : B) ∈ D}
  lower' := by
    intro q p hpq hq
    obtain ⟨hqB, hqD⟩ := hq
    have hpB : p ∈ B := B.lower' hpq hqB
    exact ⟨hpB, D.lower' (show (⟨p, hpB⟩ : B) ≤ ⟨q, hqB⟩ from hpq) hqD⟩

/-- Every lifted original label stays in the original lower subtree. -/
theorem lift_le (D : LowerSet B) : lift B D ≤ B :=
  fun _ h => h.choose

/-- The entire original support lift is monotone on the actual lower subsets. -/
theorem lift_mono {D E : LowerSet B} (h : D ≤ E) : lift B D ≤ lift B E := by
  rintro p ⟨hp, hD⟩
  exact ⟨hp, h hD⟩

/-- The same original label values give the actual full lower-subset order isomorphism. -/
def carrierIso (D : LowerSet B) : D ≃o lift B D where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun p := ⟨⟨p.1, p.2.choose⟩, p.2.choose_spec⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl
  map_rel_iff' := by intro p q; rfl

/-- The whole original subtree support lifts to that same original lower set. -/
theorem lift_top : lift B ⊤ = B := by
  apply le_antisymm (lift_le B ⊤)
  intro p hp
  exact ⟨hp, by simp⟩

variable {C : Type u} [Category.{v} C] {Y : P ⥤ C} (L : LowerSetColimitData Y)

/-- The full selected cofan inside the subtree retains the original whole-tree point and legs. -/
def cocone (D : LowerSet B) : Cocone (restriction (restriction Y B) D) where
  pt := L.obj (lift B D)
  ι :=
    { app p := L.ι (lift B D) (carrierIso B D p)
      naturality p q h := by
        change Y.map (homOfLE (leOfHom h)) ≫
            L.ι (lift B D) (carrierIso B D q) =
          L.ι (lift B D) (carrierIso B D p) ≫ 𝟙 _
        rw [Category.comp_id]
        exact (L.cocone (lift B D)).w ((carrierIso B D).equivalence.functor.map h) }

/-- The whole original selected colimit UP is retained on the literal lower-subtree labels. -/
def isColimit (D : LowerSet B) : IsColimit (cocone B L D) := by
  change IsColimit ((L.cocone (lift B D)).whisker (carrierIso B D).equivalence.functor)
  exact (L.isColimit (lift B D)).whiskerEquivalence (carrierIso B D).equivalence

/-- All actual lower-subtree colimit choices are constructed from the same original L. -/
def choices : LowerSetColimitData (restriction Y B) where
  cocone := cocone B L
  isColimit := isColimit B L

/-- Every actual original subtree lower-point function is the same original selected point. -/
theorem choices_obj_function :
    (choices B L).obj = fun D => L.obj (lift B D) := rfl

/-- Every original subtree cofan leg is retained as the same original whole-tree leg. -/
theorem choices_cofan_function (D : LowerSet B) :
    (choices B L).ι D = fun p => L.ι (lift B D) (carrierIso B D p) := rfl

/-- The full original subtree comparison is the same original lifted-support comparison. -/
theorem choices_map {D E : LowerSet B} (h : D ≤ E) :
    (choices B L).map h = L.map (lift_mono B h) := by
  apply (L.isColimit (lift B D)).hom_ext
  intro p
  obtain ⟨p', rfl⟩ := (carrierIso B D).surjective p
  have hLeft := (choices B L).ι_map h p'
  have hRight := L.ι_map (lift_mono B h) (carrierIso B D p')
  exact hLeft.trans hRight.symm

/-- The actual lift retains the same genuine local support bound through its label isomorphism. -/
theorem lift_bound (chi : Cardinal.{w}) (D : LowerSet B) (hD : HasCardinalLT D chi) :
    HasCardinalLT (lift B D) chi :=
  hD.of_injective (carrierIso B D).symm (carrierIso B D).symm.injective

end CategoryTheory.SmallObject.OriginalLowerSubtreeChoices
