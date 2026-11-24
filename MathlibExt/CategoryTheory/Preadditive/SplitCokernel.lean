/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Cokernels of split complementary projectors

For a split inclusion and retraction, the retraction is a cokernel of the complementary projector.
Its universal property uses preadditivity and the split identity. When the relevant cokernel
exists, it identifies that cokernel with the retract.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X Y : C} (q : X ⟶ X) (i : Y ⟶ X) (r : X ⟶ Y)
  (hi : i ≫ r = 𝟙 Y) (hq : q = 𝟙 X - r ≫ i)

include hi hq in
/-- The original retraction kills the complementary projector. -/
@[reassoc]
theorem splitComplement_comp_retraction : q ≫ r = 0 := by
  rw [hq, Preadditive.sub_comp, Category.id_comp, Category.assoc, hi,
    Category.comp_id, sub_self]

/--
The original retraction is the cokernel cofork, by the universal API. The universal property does
not require a chosen cokernel object.
-/
def splitComplementIsCokernel :
    IsColimit (CokernelCofork.ofπ r (splitComplement_comp_retraction q i r hi hq)) :=
  CokernelCofork.IsColimit.ofπ r (splitComplement_comp_retraction q i r hi hq)
    (fun {Z} f _ => i ≫ f)
    (fun {Z} f hf => by
      have h : f - (r ≫ i ≫ f) = 0 := by
        simpa only [hq, Preadditive.sub_comp, Category.id_comp, Category.assoc] using hf
      exact (sub_eq_zero.mp h).symm)
    (fun {Z} f _ m hm => by
      calc
        m = (i ≫ r) ≫ m := by rw [hi, Category.id_comp]
        _ = i ≫ (r ≫ m) := Category.assoc _ _ _
        _ = i ≫ f := by rw [hm])

variable [HasCokernel q]

/-- The chosen cokernel is canonically the original retract object. -/
def cokernelSplitComplementIso : cokernel q ≅ Y :=
  (cokernelIsCokernel q).coconePointUniqueUpToIso (splitComplementIsCokernel q i r hi hq)

/-- The quotient projection is sent to the original retraction. -/
@[reassoc]
theorem cokernelSplitComplementIso_π_hom :
    cokernel.π q ≫ (cokernelSplitComplementIso q i r hi hq).hom = r :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel q)
    (splitComplementIsCokernel q i r hi hq) WalkingParallelPair.one

/-- The inverse is the original inclusion followed by the quotient projection. -/
theorem cokernelSplitComplementIso_inv :
    (cokernelSplitComplementIso q i r hi hq).inv = i ≫ cokernel.π q := by
  apply (cancel_mono (cokernelSplitComplementIso q i r hi hq).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, cokernelSplitComplementIso_π_hom, hi]

variable {X' Y' : C} (q' : X' ⟶ X') (i' : Y' ⟶ X') (r' : X' ⟶ Y')
  (hi' : i' ≫ r' = 𝟙 Y') (hq' : q' = 𝟙 X' - r' ≫ i') [HasCokernel q']

/-- Endomorphism and retraction squares earn naturality of the cokernel comparison. -/
@[reassoc]
theorem cokernelSplitComplementIso_naturality
    (f : X ⟶ X') (g : Y ⟶ Y') (w : q ≫ f = f ≫ q')
    (hr : f ≫ r' = r ≫ g) :
    cokernel.map q q' f f w ≫ (cokernelSplitComplementIso q' i' r' hi' hq').hom =
      (cokernelSplitComplementIso q i r hi hq).hom ≫ g := by
  have hπ : cokernel.π q ≫ cokernel.map q q' f f w = f ≫ cokernel.π q' :=
    cokernel.π_desc _ _ _
  apply (cancel_epi (cokernel.π q)).1
  calc
    _ = (f ≫ cokernel.π q') ≫ (cokernelSplitComplementIso q' i' r' hi' hq').hom := by
      rw [← Category.assoc, hπ]
    _ = f ≫ r' := by rw [Category.assoc, cokernelSplitComplementIso_π_hom]
    _ = r ≫ g := hr
    _ = _ := by simp only [cokernelSplitComplementIso_π_hom_assoc]

/-- The same constructed comparison gives inverse naturality without a supplied iso square. -/
@[reassoc]
theorem cokernelSplitComplementIso_inv_naturality
    (f : X ⟶ X') (g : Y ⟶ Y') (w : q ≫ f = f ≫ q')
    (hr : f ≫ r' = r ≫ g) :
    g ≫ (cokernelSplitComplementIso q' i' r' hi' hq').inv =
      (cokernelSplitComplementIso q i r hi hq).inv ≫ cokernel.map q q' f f w := by
  apply (cancel_mono (cokernelSplitComplementIso q' i' r' hi' hq').hom).1
  calc
    (g ≫ (cokernelSplitComplementIso q' i' r' hi' hq').inv) ≫
        (cokernelSplitComplementIso q' i' r' hi' hq').hom = g := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (cokernelSplitComplementIso q i r hi hq).inv ≫
        ((cokernelSplitComplementIso q i r hi hq).hom ≫ g) := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (cokernelSplitComplementIso q i r hi hq).inv ≫
        (cokernel.map q q' f f w ≫ (cokernelSplitComplementIso q' i' r' hi' hq').hom) :=
      congrArg (fun m => (cokernelSplitComplementIso q i r hi hq).inv ≫ m)
        (cokernelSplitComplementIso_naturality q i r hi hq q' i' r' hi' hq' f g w hr).symm
    _ = _ := (Category.assoc _ _ _).symm

end CategoryTheory.Limits

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X Y X' Y' : C} {i : Y ⟶ X} {r : X ⟶ Y} {i' : Y' ⟶ X'} {r' : X' ⟶ Y'}

/-- Compatible maps of the original split data commute with their complements. -/
theorem splitComplement_naturality (f : X ⟶ X') (g : Y ⟶ Y')
    (hι : i ≫ f = g ≫ i') (hr : f ≫ r' = r ≫ g) :
    f ≫ (𝟙 X' - r' ≫ i') = (𝟙 X - r ≫ i) ≫ f := by
  have h : f ≫ (r' ≫ i') = (r ≫ i) ≫ f := by
    calc
      _ = (f ≫ r') ≫ i' := (Category.assoc _ _ _).symm
      _ = (r ≫ g) ≫ i' := by rw [hr]
      _ = r ≫ (g ≫ i') := Category.assoc _ _ _
      _ = r ≫ (i ≫ f) := by rw [hι]
      _ = (r ≫ i) ≫ f := (Category.assoc _ _ _).symm
  rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp, h]

end CategoryTheory
