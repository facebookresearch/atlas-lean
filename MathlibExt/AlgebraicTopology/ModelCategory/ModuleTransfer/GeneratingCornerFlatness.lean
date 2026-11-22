/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.FreeCellFlatness
public import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells

/-!
The exact original coefficient flatness certificate and h-monoidality give
base generating-arrow flatness, with no added cofibrancy of either original
I-domain or weak-map endpoint. The whole base pushout corner is retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.GeneratingCornerFlatness

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C]

/-- The original whole Arrow braid changes only the tensor order of the same h-cofibration. -/
theorem leftTensor_hCof (h : HMonoidality C) {K L : C} (i : K ⟶ L)
    (hi : cofibrations C i) (X : C) : hCofibrations C (X ◁ i) := by
  let e : Arrow.mk (i ▷ X) ≅ Arrow.mk (X ◁ i) :=
    Arrow.isoMk (β_ K X) (β_ L X) (braiding_naturality_left i X).symm
  exact ((hCofibrations C).arrow_mk_iso_iff e).mp (h.cofibration_tensor i hi X)

/-- Source and target coefficient flatness imply the actual generating pushout-product is weak. -/
theorem generatingPushoutProduct_weak
    (I : MorphismProperty C) (hI : I ≤ cofibrations C)
    (hMono : HMonoidality C)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness I)
    {X Y K L : C} (f : X ⟶ Y) (hf : weakEquivalences C f)
    (i : K ⟶ L) (hi : I i) :
    weakEquivalences C ((Arrow.mk f □ Arrow.mk i).hom) := by
  obtain ⟨hK, hL⟩ := hFlat f hf i hi
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f i
  have hLeg : hCofibrations C (X ◁ i) := leftTensor_hCof hMono i (hI i hi) X
  have hInr : weakEquivalences C s.inr :=
    (hLeg (X ⊗ K) (X ⊗ L) (𝟙 _) (X ◁ i) (𝟙 _) IsPushout.of_id_fst).of_isPushout
      s.isPushout.flip hK
  apply (weakEquivalences C).of_precomp s.inr s.ι hInr
  rw [s.inr_ι]
  exact hL

end HomotopicalAlgebra.ModuleTransfer.GeneratingCornerFlatness
