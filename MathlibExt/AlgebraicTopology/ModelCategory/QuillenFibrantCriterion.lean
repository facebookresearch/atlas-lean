/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# The fibrant-object criterion for Quillen adjunctions

This file formalizes Joyal--Tierney Proposition 7.15.  A cofibration is
trivial exactly when it lifts against every fibration whose two endpoints
are fibrant.  Consequently, an adjunction is Quillen as soon as its left
adjoint preserves cofibrations and its right adjoint preserves fibrations
between fibrant objects.

The endpoint restriction is essential: the right adjoint is not assumed to
preserve arbitrary fibrations before the Quillen conclusion is available.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]

/-- Fibrations whose source and target are fibrant in the selected model
structure. -/
def fibrationsBetweenFibrantObjects : MorphismProperty C :=
  fun X Y p ↦ fibrations C p ∧ IsFibrant X ∧ IsFibrant Y

@[simp]
theorem mem_fibrationsBetweenFibrantObjects_iff {X Y : C} (p : X ⟶ Y) :
    fibrationsBetweenFibrantObjects (C := C) p ↔
      fibrations C p ∧ IsFibrant X ∧ IsFibrant Y :=
  Iff.rfl

/-- A functor preserves fibrations between fibrant objects when the image of
each such fibration is a fibration.  No assertion about fibrancy of the image
objects is included. -/
def PreservesFibrationsBetweenFibrantObjects
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D] (F : C ⥤ D) : Prop :=
  fibrationsBetweenFibrantObjects (C := C) ≤ (fibrations D).inverseImage F

@[simp]
theorem preservesFibrationsBetweenFibrantObjects_iff
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D] (F : C ⥤ D) :
    PreservesFibrationsBetweenFibrantObjects F ↔
      ∀ ⦃X Y : C⦄ (p : X ⟶ Y), fibrations C p →
        IsFibrant X → IsFibrant Y → fibrations D (F.map p) := by
  constructor
  · intro h X Y p hp hX hY
    exact h p ⟨hp, hX, hY⟩
  · intro h X Y p hp
    exact h p hp.1 hp.2.1 hp.2.2

theorem PreservesFibrationsBetweenFibrantObjects.map_fibration
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D] {F : C ⥤ D}
    (hF : PreservesFibrationsBetweenFibrantObjects F)
    {X Y : C} {p : X ⟶ Y} (hp : fibrations C p)
    (hX : IsFibrant X) (hY : IsFibrant Y) :
    fibrations D (F.map p) :=
  hF p ⟨hp, hX, hY⟩

/-- Joyal--Tierney Lemma 7.14: among cofibrations, lifting against all
fibrations between fibrant objects detects the trivial cofibrations. -/
theorem trivialCofibration_iff_llp_fibrationsBetweenFibrantObjects
    {A B : C} (i : A ⟶ B) (hi : cofibrations C i) :
    trivialCofibrations C i ↔
      (fibrationsBetweenFibrantObjects (C := C)).llp i := by
  constructor
  · intro hiT X Y p hp
    exact hasLiftingProperty_of_wfs i p hiT hp.1
  · intro hiLift
    let r := factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from B)
    let _ : Fibration r.p := (fibration_iff (f := r.p)).2 r.hp
    let _ : IsFibrant (⊤_ C) :=
      (isFibrant_iff_of_isTerminal (𝟙 _) terminalIsTerminal).2
        (by infer_instance)
    let _ : IsFibrant r.Z := isFibrant_of_fibration r.p
    let j := r.i
    let d := factorizationData (trivialCofibrations C) (fibrations C) (i ≫ j)
    let _ : Fibration d.p := (fibration_iff (f := d.p)).2 d.hp
    let _ : IsFibrant d.Z := isFibrant_of_fibration d.p
    have hpEndpoints : fibrationsBetweenFibrantObjects (C := C) d.p :=
      ⟨d.hp, inferInstance, inferInstance⟩
    let _ : HasLiftingProperty i d.p := hiLift d.p hpEndpoints
    let sq : CommSq d.i i d.p j := ⟨d.fac⟩
    let Q := toHomotopyCategory C
    let _ : IsIso (Q.map d.i) :=
      Localization.inverts Q (weakEquivalences C) d.i d.hi.2
    let _ : IsIso (Q.map j) :=
      Localization.inverts Q (weakEquivalences C) j r.hi.2
    have hHomInv : Q.map i ≫ (Q.map sq.lift ≫ inv (Q.map d.i)) = 𝟙 _ := by
      rw [← Category.assoc, ← Q.map_comp, sq.fac_left]
      exact IsIso.hom_inv_id _
    have hInvHom : (Q.map sq.lift ≫ inv (Q.map d.i)) ≫ Q.map i = 𝟙 _ := by
      have hMapFac : Q.map i ≫ Q.map j = Q.map d.i ≫ Q.map d.p := by
        rw [← Q.map_comp, ← Q.map_comp, d.fac]
      apply (cancel_mono (Q.map j)).1
      rw [Category.id_comp]
      simp only [Category.assoc]
      rw [hMapFac]
      simp only [IsIso.inv_hom_id_assoc]
      rw [← Q.map_comp, sq.fac_right]
    let _ : IsIso (Q.map i) :=
      ⟨⟨Q.map sq.lift ≫ inv (Q.map d.i), hHomInv, hInvHom⟩⟩
    exact ⟨hi,
      (weakEquivalence_iff_isIso_toHomotopyCategory_map i).2 inferInstance⟩

end HomotopicalAlgebra

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

open HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}

/-- Joyal--Tierney Proposition 7.15: preserving cofibrations on the left and
fibrations between fibrant objects on the right is enough to construct a
Quillen adjunction. -/
theorem mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects
    (hL : PreservesCofibrations L)
    (hR : PreservesFibrationsBetweenFibrantObjects R) :
    IsQuillenAdjunction adj where
  preservesCofibrations := hL
  preservesTrivialCofibrations := by
    intro A B i hi
    have hiCof : cofibrations D (L.map i) := hL i hi.1
    change trivialCofibrations D (L.map i)
    rw [trivialCofibration_iff_llp_fibrationsBetweenFibrantObjects
      (L.map i) hiCof]
    intro X Y p hp
    have hRp : fibrations C (R.map p) :=
      hR.map_fibration hp.1 hp.2.1 hp.2.2
    have hLift : HasLiftingProperty i (R.map p) :=
      hasLiftingProperty_of_wfs i (R.map p) hi hRp
    exact (adj.hasLiftingProperty_iff i p).2 hLift

/-- Under the fibrant-object criterion, a weak equivalence between cofibrant
objects is sent to a weak equivalence.  This is the Brown-lemma step used in
localization comparisons. -/
theorem map_weakEquivalence_of_cofibrant_of_fibrantCriterion
    (adj : L ⊣ R)
    (hL : PreservesCofibrations L)
    (hR : PreservesFibrationsBetweenFibrantObjects R)
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f)
    (hX : IsCofibrant X) (hY : IsCofibrant Y) :
    weakEquivalences D (L.map f) := by
  let _ : IsQuillenAdjunction adj :=
    mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects hL hR
  let _ : WeakEquivalence f := (weakEquivalence_iff f).2 hf
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant Y := hY
  exact (weakEquivalence_iff (L.map f)).1
    (map_weakEquivalence_of_cofibrant (adj := adj) f)

/-- If every source object is cofibrant, the fibrant-object criterion makes
the left adjoint preserve every weak equivalence.  This is the all-arrow
form needed for model structures whose cofibrations are monomorphisms on a
presheaf category. -/
theorem map_weakEquivalence_of_allObjectsCofibrant_of_fibrantCriterion
    (adj : L ⊣ R)
    (hL : PreservesCofibrations L)
    (hR : PreservesFibrationsBetweenFibrantObjects R)
    (hCof : ∀ X : C, IsCofibrant X)
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences D (L.map f) :=
  map_weakEquivalence_of_cofibrant_of_fibrantCriterion
    adj hL hR f hf (hCof X) (hCof Y)

end CategoryTheory.Adjunction.IsQuillenAdjunction
