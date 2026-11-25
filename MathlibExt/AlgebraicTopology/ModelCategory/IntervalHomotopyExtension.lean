/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.HomotopyExtension
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Interval endpoint extension from the pushout-product axiom

An arrow `e : 𝟙_ C ⟶ J` gives a natural endpoint inclusion `X ⟶ J ⊗ X`
using the inverse left unitor. In a closed symmetric monoidal model category
whose objects are fibrant, a trivial-cofibration endpoint gives the interval
homotopy extension property for every cofibration. A compatible map and
endpoint homotopy extend by lifting the corresponding pushout-product arrow
against the target’s terminal fibration.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uC vC
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped MonoidalCategory

namespace CategoryTheory.IntervalEndpointExtension
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

/-- The full original monoidal endpoint inclusion on every object and morphism. -/
def inclusionNatTrans (J : C) (e : 𝟙_ C ⟶ J) : 𝟭 C ⟶ tensorLeft J where
  app X := (λ_ X).inv ≫ e ▷ X
  naturality {X Y} f := by
    change f ≫ ((λ_ Y).inv ≫ e ▷ Y) = ((λ_ X).inv ≫ e ▷ X) ≫ J ◁ f
    symm
    calc
      _ = (λ_ X).inv ≫ (e ▷ X ≫ J ◁ f) := Category.assoc _ _ _
      _ = (λ_ X).inv ≫ ((𝟙_ C) ◁ f ≫ e ▷ Y) :=
        congrArg (fun q => (λ_ X).inv ≫ q) (whisker_exchange e f).symm
      _ = ((λ_ X).inv ≫ (𝟙_ C) ◁ f) ≫ e ▷ Y := (Category.assoc _ _ _).symm
      _ = (f ≫ (λ_ Y).inv) ≫ e ▷ Y :=
        congrArg (fun q => q ≫ e ▷ Y) (leftUnitor_inv_naturality f).symm
      _ = _ := Category.assoc _ _ _

/-- EVERY complete actual endpoint component retains the original inverse unitor and endpoint. -/
theorem inclusionNatTrans_app (J : C) (e : 𝟙_ C ⟶ J) (X : C) :
    (inclusionNatTrans J e).app X = (λ_ X).inv ≫ e ▷ X := rfl

/-- The ENTIRE endpoint component function is the original full monoidal map family. -/
theorem inclusionNatTrans_whole (J : C) (e : 𝟙_ C ⟶ J) :
    (fun X : C => (inclusionNatTrans J e).app X) =
      (fun X => (λ_ X).inv ≫ e ▷ X) := rfl

variable [ModelCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C] [∀ Y : C, IsFibrant Y]

/--
Genuine pushout-product/model lifting gives the ALL-target based extension property, retaining
both actual coefficients and the entire chosen pushout-product record.
-/
theorem modelCofibration_mem (J : C) (e : 𝟙_ C ⟶ J)
    (he : trivialCofibrations C e) {A X : C} (i : A ⟶ X) (hi : cofibrations C i) :
    IntervalHomotopyExtension.property (tensorLeft J) (inclusionNatTrans J e) i := by
  intro Y f H h0
  change (((λ_ A).inv ≫ e ▷ A) ≫ H) = i ≫ f at h0
  let po := Functor.PushoutObjObj.ofHasPushout (curriedTensor C) e i
  have hPP : trivialCofibrations C po.ι :=
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left e i he hi
  have hc : (e ▷ A) ≫ H = (𝟙_ C) ◁ i ≫ (λ_ X).hom ≫ f := by
    have h := congrArg (fun q : A ⟶ Y => (λ_ A).hom ≫ q) h0
    have h' : (e ▷ A) ≫ H = (λ_ A).hom ≫ i ≫ f := by
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
    exact h'.trans (leftUnitor_naturality_assoc i f).symm
  let d : po.pt ⟶ Y := po.isPushout.desc H ((λ_ X).hom ≫ f) hc
  have hdLeft : po.inl ≫ d = H := po.isPushout.inl_desc H ((λ_ X).hom ≫ f) hc
  have hdRight : po.inr ≫ d = (λ_ X).hom ≫ f :=
    po.isPushout.inr_desc H ((λ_ X).hom ≫ f) hc
  have hTime : po.inl ≫ po.ι = J ◁ i := po.inl_ι
  have hEndpoint : po.inr ≫ po.ι = e ▷ X := po.inr_ι
  let _ : Cofibration po.ι := (HomotopicalAlgebra.cofibration_iff _).mpr hPP.1
  let _ : WeakEquivalence po.ι := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hPP.2
  let sq : CommSq d po.ι (terminal.from Y) (terminal.from (J ⊗ X)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  let K : J ⊗ X ⟶ Y := sq.lift
  have hK : po.ι ≫ K = d := sq.fac_left
  refine ⟨K, ?_, ?_⟩
  · change (((λ_ X).inv ≫ e ▷ X) ≫ K) = f
    rw [← hEndpoint, Category.assoc, Category.assoc, hK, hdRight,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · change J ◁ i ≫ K = H
    rw [← hTime, Category.assoc, hK, hdLeft]

end CategoryTheory.IntervalEndpointExtension
