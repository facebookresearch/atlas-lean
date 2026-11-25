/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalUnitFromPushoutProduct
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct

/-!
# Pushout-product reduction using the original generating classes

Generator products are extended to the same original double orthogonal
classes by the actual tensor lifting adjunction. A separate MMSS 12.6
reduction uses a cofibration pushout-product law and independently proved
all-source tensor weak preservation with a cofibrant factor. Its proof
keeps the chosen tensor pushout, both legs and their factor equation.

The original generating families and model structure are never replaced.
Native stable applications still have to prove their actual free-generator
products or their all-source tensor invariance. Unit cofibrancy and the
same supplied unit factor are separate inputs to the final constructors.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [ModelCategory C] [MonoidalCategory C]

/-- Every original weak map, including maps with arbitrary endpoints,
remains weak under right tensor by a true cofibrant object. This is an
independent hypothesis in stable applications. -/
def CofibrantRightTensorWeakPreservation : Prop :=
  ∀ (K : C), IsCofibrant K → ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    weakEquivalences C f → weakEquivalences C (f ▷ K)

variable {C}

section CofibrantEndpoints

variable [MonoidalClosed C]

/-- The source tensor-invariance input and the cofibration PP law prove
the actual trivial PP assertion against a cofibration with both cofibrant
endpoints. The original tensor pushout supplies the two-out-of-three step. -/
theorem pushoutProduct_trivial_of_cofibrant_right_endpoints
    (hC : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (hW : CofibrantRightTensorWeakPreservation C)
    {A B K L : C} (i : A ⟶ B) (j : K ⟶ L)
    [IsCofibrant K] [IsCofibrant L]
    (hi : trivialCofibrations C i) (hj : cofibrations C j) :
    trivialCofibrations C ((Arrow.mk i □ Arrow.mk j).hom) := by
  have hiK : trivialCofibrations C (i ▷ K) :=
    ⟨whiskerRight_mem_of_isCofibrant (cofibrations C) hC i K hi.1,
      hW K inferInstance i hi.2⟩
  have hleg : trivialCofibrations C (pushout.inr (i ▷ K) (A ◁ j)) :=
    (trivialCofibrations C).pushout_inr (i ▷ K) (A ◁ j) hiK
  have hfac : pushout.inr (i ▷ K) (A ◁ j) ≫
      (Arrow.mk i □ Arrow.mk j).hom = i ▷ L := by
    change pushout.inr (i ▷ K) (A ◁ j) ≫
      pushout.desc (B ◁ j) (i ▷ L) ((whisker_exchange i j).symm) = i ▷ L
    exact pushout.inr_desc _ _ _
  have hweak : weakEquivalences C (Arrow.mk i □ Arrow.mk j).hom :=
    (weakEquivalences C).of_precomp (pushout.inr (i ▷ K) (A ◁ j))
      (Arrow.mk i □ Arrow.mk j).hom hleg.2 (by rw [hfac]; exact hW L inferInstance i hi.2)
  exact ⟨hC i j hi.1 hj, hweak⟩

end CofibrantEndpoints

namespace CofibrantGenerationData

variable [BraidedCategory C] [MonoidalClosed C]
variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- Literal I-generator cofibration products extend to every pair of
cofibrations in the same selected model, using its original I right class. -/
theorem cofibrationPushoutProduct_of_generatorProducts
    (G : CofibrantGenerationData C κ)
    (hII : PushoutProductLe G.I G.I (cofibrations C)) :
    PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C) := by
  have hI : G.I.rlp.llp = cofibrations C := by
    rw [G.I_rlp, trivialFibrations_llp]
  intro A B K L i j hi hj
  rw [← hI] at hi hj ⊢
  exact pushoutProduct_mem_rlp_llp G.I G.I G.I
    (fun {_ _ _ _} a ha b hb ↦ by rw [hI]; exact hII a b ha hb) hi hj

/-- Literal J-by-I products extend to the actual trivial-by-cofibration
branch of the same original model. -/
theorem trivialPushoutProductLeft_of_generatorProducts
    (G : CofibrantGenerationData C κ)
    (hJI : PushoutProductLe G.J G.I (trivialCofibrations C)) :
    PushoutProductLe (trivialCofibrations C) (cofibrations C)
      (trivialCofibrations C) := by
  have hI : G.I.rlp.llp = cofibrations C := by
    rw [G.I_rlp, trivialFibrations_llp]
  have hJ : G.J.rlp.llp = trivialCofibrations C := by
    rw [G.J_rlp, fibrations_llp]
  intro A B K L i j hi hj
  rw [← hJ] at hi ⊢
  rw [← hI] at hj
  exact pushoutProduct_mem_rlp_llp G.J G.I G.J
    (fun {_ _ _ _} a ha b hb ↦ by rw [hJ]; exact hJI a b ha hb) hi hj

/-- The two actual original generator-product tests give all three PP
laws. The whole-arrow braiding supplies the other trivial branch. -/
theorem pushoutProductAxiom_of_generatorProducts
    (G : CofibrantGenerationData C κ)
    (hII : PushoutProductLe G.I G.I (cofibrations C))
    (hJI : PushoutProductLe G.J G.I (trivialCofibrations C)) :
    MonoidalPushoutProductAxiom C :=
  monoidalPushoutProductAxiom_of_left
    (G.cofibrationPushoutProduct_of_generatorProducts hII)
    (G.trivialPushoutProductLeft_of_generatorProducts hJI)

/-- When the original trivial generating family is a literal union,
retain its two original summands and prove their actual products
separately before extending the same family by WFS closure. -/
theorem pushoutProductAxiom_of_splitGenerators
    (G : CofibrantGenerationData C κ) (J K : MorphismProperty C)
    (hJK : G.J = J ⊔ K)
    (hII : PushoutProductLe G.I G.I (cofibrations C))
    (hJI : PushoutProductLe J G.I (trivialCofibrations C))
    (hKI : PushoutProductLe K G.I (trivialCofibrations C)) :
    MonoidalPushoutProductAxiom C := by
  apply G.pushoutProductAxiom_of_generatorProducts hII
  intro A B X Y i j hi hj
  rw [hJK] at hi
  rcases hi with hi | hi
  · exact hJI i j hi hj
  · exact hKI i j hi hj

/-- MMSS's cofibrant-factor tensor-invariance reduction extends from the
same original I-family to every cofibration. No trivial PP law is assumed
in this proof. -/
theorem trivialPushoutProductLeft_of_tensorWeakPreservation
    (G : CofibrantGenerationData C κ)
    (hC : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (hW : CofibrantRightTensorWeakPreservation C)
    (hIends : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), G.I f → IsCofibrant X ∧ IsCofibrant Y) :
    PushoutProductLe (trivialCofibrations C) (cofibrations C)
      (trivialCofibrations C) := by
  have hI : G.I.rlp.llp = cofibrations C := by
    rw [G.I_rlp, trivialFibrations_llp]
  have hT : (trivialCofibrations C).rlp.llp = trivialCofibrations C := by
    rw [trivialCofibrations_rlp, fibrations_llp]
  intro A B K L i j hi hj
  have hi' : (trivialCofibrations C).rlp.llp i := by rw [hT]; exact hi
  have hj' : G.I.rlp.llp j := by rw [hI]; exact hj
  rw [← hT]
  apply pushoutProduct_mem_rlp_llp (trivialCofibrations C) G.I (trivialCofibrations C)
    ?_ hi' hj'
  intro X Y X' Y' a ha b hb
  have hends := hIends b hb
  let _ : IsCofibrant X' := hends.1
  let _ : IsCofibrant Y' := hends.2
  have hbC : cofibrations C b := by
    rw [← hI]
    exact G.I.le_llp_rlp b hb
  rw [hT]
  exact pushoutProduct_trivial_of_cofibrant_right_endpoints hC hW a b ha hbC

/-- Independently proved all-source cofibrant-factor tensor weakness,
original I endpoint cofibrancy and the cofibration PP law give the whole
PP axiom record for the same model. -/
theorem pushoutProductAxiom_of_tensorWeakPreservation
    (G : CofibrantGenerationData C κ)
    (hC : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (hW : CofibrantRightTensorWeakPreservation C)
    (hIends : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), G.I f → IsCofibrant X ∧ IsCofibrant Y) :
    MonoidalPushoutProductAxiom C :=
  monoidalPushoutProductAxiom_of_left hC
    (G.trivialPushoutProductLeft_of_tensorWeakPreservation hC hW hIends)

omit [BraidedCategory C] in
/-- Genuine original generator products and true unit cofibrancy yield
the full model axioms with the SAME supplied initial-unit factor. -/
theorem monoidalModelOfGeneratorProducts
    [SymmetricCategory C] [IsCofibrant (𝟙_ C)]
    (G : CofibrantGenerationData C κ)
    (hII : PushoutProductLe G.I G.I (cofibrations C))
    (hJI : PushoutProductLe G.J G.I (trivialCofibrations C))
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) : IsClosedSymmetricMonoidalModelCategory C :=
  (G.pushoutProductAxiom_of_generatorProducts hII hJI).monoidalModelOfUnitFactor d

omit [BraidedCategory C] in
/-- The tensor-invariance criterion also keeps the same original chosen
unit factor. Its all-source tensor and true unit-cofibrancy requirements
remain explicit until a native application proves them. -/
theorem monoidalModelOfTensorWeakPreservation
    [SymmetricCategory C] [IsCofibrant (𝟙_ C)]
    (G : CofibrantGenerationData C κ)
    (hC : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (hW : CofibrantRightTensorWeakPreservation C)
    (hIends : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), G.I f → IsCofibrant X ∧ IsCofibrant Y)
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) : IsClosedSymmetricMonoidalModelCategory C :=
  (G.pushoutProductAxiom_of_tensorWeakPreservation hC hW hIends).monoidalModelOfUnitFactor d

end CofibrantGenerationData

end HomotopicalAlgebra
