/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingCoherence
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorIndex

/-!
# The actual enriched Day input swap and index braiding

The product swap acts by the symmetry of the entire two-factor Hom object.
The original index braiding is a genuine enriched transformation from the
unchanged tensor functor to its swapped input functor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB uI vI
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingIndex

attribute [local instance] Enriched.prodCategory

section Unit
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]

/-- The full unit-valued pair swaps through the actual value braid. -/
theorem unit_swap {A B : V} (a : 𝟙_ V ⟶ A) (b : 𝟙_ V ⟶ B) :
    (λ_ (𝟙_ V)).inv ≫ (a ⊗ₘ b) ≫ (β_ A B).hom =
      (λ_ (𝟙_ V)).inv ≫ (b ⊗ₘ a) := by
  have hu : (β_ (𝟙_ V) (𝟙_ V)).hom = 𝟙 ((𝟙_ V) ⊗ (𝟙_ V)) := by
    rw [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id]
  rw [braiding_naturality, hu, Category.id_comp]

end Unit
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]

/-- Swap the original objects and the complete product-enriched Hom factors. -/
def swap
    {A : Type uA} [EnrichedCategory V A]
    {B : Type uB} [EnrichedCategory V B] : EnrichedFunctor V (A × B) (B × A) where
  obj X := (X.2, X.1)
  map X Y := (β_ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)).hom
  map_id X :=
    (Category.assoc (λ_ (𝟙_ V)).inv (eId V X.1 ⊗ₘ eId V X.2)
      (β_ (X.1 ⟶[V] X.1) (X.2 ⟶[V] X.2)).hom).trans
        (unit_swap (eId V X.1) (eId V X.2))
  map_comp X Y Z := by
    let H := X.1 ⟶[V] Y.1
    let K := X.2 ⟶[V] Y.2
    let H' := Y.1 ⟶[V] Z.1
    let K' := Y.2 ⟶[V] Z.2
    let c : H ⊗ H' ⟶ (X.1 ⟶[V] Z.1) := eComp V X.1 Y.1 Z.1
    let d : K ⊗ K' ⟶ (X.2 ⟶[V] Z.2) := eComp V X.2 Y.2 Z.2
    change (tensorμ H K H' K' ≫ (c ⊗ₘ d)) ≫
        (β_ (X.1 ⟶[V] Z.1) (X.2 ⟶[V] Z.2)).hom =
      ((β_ H K).hom ⊗ₘ (β_ H' K').hom) ≫ tensorμ K H K' H' ≫ (d ⊗ₘ c)
    calc
      _ = tensorμ H K H' K' ≫ (β_ (H ⊗ H') (K ⊗ K')).hom ≫ (d ⊗ₘ c) := by
        simpa only [Category.assoc] using
          congrArg (fun v => tensorμ H K H' K' ≫ v) (braiding_naturality c d)
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun v => v ≫ (d ⊗ₘ c))
          (BraidingCoherence.tensorMu_swap H K H' K')

/-- The swap retains its literal complete Hom symmetry. -/
theorem swap_map
    {A : Type uA} [EnrichedCategory V A]
    {B : Type uB} [EnrichedCategory V B] (X Y : A × B) :
    (swap (V := V)).map X Y = (β_ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)).hom := rfl

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [BraidedCategory I]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)

/-- The actual original index tensor with its inputs swapped on full Hom objects. -/
abbrev tensor : EnrichedFunctor V (I × I) I :=
  (swap (V := V)).comp V d.tensorEnrichedFunctor

/-- The original index braiding, retaining its full enriched naturality. -/
abbrev indexBraiding :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) d.tensorEnrichedFunctor (tensor d) :=
  b.braidingGraded

/-- Every component is the actual original index braiding arrow. -/
theorem indexBraiding_app (X : I × I) :
    (indexBraiding d b).app X = eHomEquiv V (β_ X.1 X.2).hom :=
  b.braidingGraded_app X

include b in
/-- The full swapped index Hom map is the original map transported by the actual index braid. -/
theorem indexMap_congr (X Y : I × I) :
    (tensor d).map X Y = d.tensorEnrichedFunctor.map X Y ≫
      (Iso.eHomCongr V (β_ X.1 X.2) (β_ Y.1 Y.2)).hom := by
  have hn : ∀ X Y : I × I,
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
        (d.tensorEnrichedFunctor.map X Y ⊗ₘ eHomEquiv V (β_ Y.1 Y.2).hom) ≫
        eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) (Y.2 ⊗ Y.1) =
      (eHomEquiv V (β_ X.1 X.2).hom ⊗ₘ (tensor d).map X Y) ≫
        eComp V (X.1 ⊗ X.2) (X.2 ⊗ X.1) (Y.2 ⊗ Y.1) := by
    intro X Y
    have h := (indexBraiding d b).naturality X Y
    simp only [Center.ofBraided, Center.ofBraidedObj, indexBraiding_app] at h
    exact h
  exact EnrichedFunctor.ofRawIsoComponents_map_eq d.tensorEnrichedFunctor (tensor d).obj
    (tensor d).map (fun X => β_ X.1 X.2) hn X Y

end CategoryTheory.EnrichedDayKernel.BraidingIndex
