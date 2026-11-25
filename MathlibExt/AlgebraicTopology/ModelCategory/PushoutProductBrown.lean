/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductQuillen
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Brown invariance before the unit axiom

Tensor weak preservation is deduced from the actual pushout-product
Quillen adjunctions. The endpoints of the weak map and the tensor factor
are cofibrant. A separate general Brown lemma retains any caller-supplied
Brown or coproduct factorization; neither tensor result selects a unit
replacement or assumes a monoidal-model unit witness.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v₁ v₂ u₁ u₂ v u

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped MonoidalCategory

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}

/-- Brown's proof for the caller's actual factorization. Its middle object,
cofibration, trivial fibration and cofibrant section are retained literally. -/
theorem map_weakEquivalence_of_cofibrantBrownFactorization
    {X Y : C} (f : X ⟶ Y) (h : CofibrantBrownFactorization f)
    [IsQuillenAdjunction adj] [WeakEquivalence f] :
    WeakEquivalence (L.map f) := by
  have hi : HomotopicalAlgebra.trivialCofibrations D (L.map h.i) :=
    (inferInstance : IsQuillenAdjunction adj).preservesTrivialCofibrations
      h.i (HomotopicalAlgebra.mem_trivialCofibrations h.i)
  have hs : HomotopicalAlgebra.trivialCofibrations D (L.map h.s) :=
    (inferInstance : IsQuillenAdjunction adj).preservesTrivialCofibrations
      h.s (HomotopicalAlgebra.mem_trivialCofibrations h.s)
  let _ : WeakEquivalence (L.map h.i) :=
    ((HomotopicalAlgebra.mem_trivialCofibrations_iff (f := L.map h.i)).mp hi).2
  let _ : WeakEquivalence (L.map h.s) :=
    ((HomotopicalAlgebra.mem_trivialCofibrations_iff (f := L.map h.s)).mp hs).2
  have hs_p : L.map h.s ≫ L.map h.p = 𝟙 (L.obj Y) := by
    rw [← L.map_comp, h.s_p, L.map_id]
  let _ : WeakEquivalence (L.map h.p) :=
    HomotopicalAlgebra.weakEquivalence_of_precomp_of_fac hs_p
  rw [← h.fac, L.map_comp]
  infer_instance

/-- Brown invariance can use exactly the factorization of the caller's
coproduct fold map. No factorization is rerun or chosen from `Nonempty`. -/
theorem map_weakEquivalence_of_coproductFactorization
    {X Y : C} (f : X ⟶ Y)
    (h : MorphismProperty.MapFactorizationData
      (HomotopicalAlgebra.cofibrations C) (HomotopicalAlgebra.trivialFibrations C)
      (coprod.desc f (𝟙 Y)))
    [IsQuillenAdjunction adj] [WeakEquivalence f]
    [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (L.map f) :=
  map_weakEquivalence_of_cofibrantBrownFactorization (adj := adj) f
    (CofibrantBrownFactorization.mk' f h)

end CategoryTheory.Adjunction.IsQuillenAdjunction

namespace HomotopicalAlgebra.MonoidalPushoutProductAxiom

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
variable (hPP : MonoidalPushoutProductAxiom C)
include hPP

/-- Left tensor preserves a weak map using its same given Brown
factorization, once the actual tensor factor is cofibrant. -/
theorem whiskerLeft_weakEquivalence_of_cofibrantBrownFactorization
    (K : C) [IsCofibrant K] {X Y : C} (f : X ⟶ Y)
    (h : CofibrantBrownFactorization f) [WeakEquivalence f] :
    WeakEquivalence (K ◁ f) := by
  let _ : (ihom.adjunction K).IsQuillenAdjunction :=
    hPP.ihomAdjunction_isQuillenAdjunction K
  exact Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrantBrownFactorization
    (adj := ihom.adjunction K) f h

/-- Right tensor preserves a weak map using its same given Brown
factorization and the actual right-tensor adjunction. -/
theorem whiskerRight_weakEquivalence_of_cofibrantBrownFactorization
    {X Y : C} (f : X ⟶ Y) (K : C) [IsCofibrant K]
    (h : CofibrantBrownFactorization f) [WeakEquivalence f] :
    WeakEquivalence (f ▷ K) := by
  let _ : (tensorRightIhomAdjunction K).IsQuillenAdjunction :=
    hPP.tensorRightIhomAdjunction_isQuillenAdjunction K
  exact Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrantBrownFactorization
    (adj := tensorRightIhomAdjunction K) f h

/-- Actual left tensor weak preservation between both cofibrant endpoints
follows from pushout-products and Brown, without a unit axiom. -/
theorem whiskerLeft_weakEquivalence_of_cofibrant
    (K : C) [IsCofibrant K] {X Y : C} (f : X ⟶ Y)
    [WeakEquivalence f] [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (K ◁ f) := by
  let _ : (ihom.adjunction K).IsQuillenAdjunction :=
    hPP.ihomAdjunction_isQuillenAdjunction K
  exact Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
    (adj := ihom.adjunction K) f

/-- Actual right tensor weak preservation between both cofibrant endpoints
uses the pushout-product precursor and the specified right adjunction. -/
theorem whiskerRight_weakEquivalence_of_cofibrant
    {X Y : C} (f : X ⟶ Y) (K : C) [IsCofibrant K]
    [WeakEquivalence f] [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (f ▷ K) := by
  let _ : (tensorRightIhomAdjunction K).IsQuillenAdjunction :=
    hPP.tensorRightIhomAdjunction_isQuillenAdjunction K
  exact Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
    (adj := tensorRightIhomAdjunction K) f

/-- A caller's coproduct fold factor gives the actual left tensor weak
map, with the original middle object and both factor legs. -/
theorem whiskerLeft_weakEquivalence_of_coproductFactorization
    (K : C) [IsCofibrant K] {X Y : C} (f : X ⟶ Y)
    (h : MorphismProperty.MapFactorizationData
      (cofibrations C) (trivialFibrations C) (coprod.desc f (𝟙 Y)))
    [WeakEquivalence f] [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (K ◁ f) :=
  hPP.whiskerLeft_weakEquivalence_of_cofibrantBrownFactorization K f
    (CofibrantBrownFactorization.mk' f h)

/-- The same caller's coproduct fold factor gives the right tensor weak
map; it is not replaced by a tensor-specific factorization. -/
theorem whiskerRight_weakEquivalence_of_coproductFactorization
    {X Y : C} (f : X ⟶ Y) (K : C) [IsCofibrant K]
    (h : MorphismProperty.MapFactorizationData
      (cofibrations C) (trivialFibrations C) (coprod.desc f (𝟙 Y)))
    [WeakEquivalence f] [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (f ▷ K) :=
  hPP.whiskerRight_weakEquivalence_of_cofibrantBrownFactorization f K
    (CofibrantBrownFactorization.mk' f h)

/-- Membership form of the left tensor Brown theorem, with both true
cofibrant endpoints supplied explicitly. -/
theorem whiskerLeft_mem_weakEquivalences
    (K : C) (hK : IsCofibrant K) {X Y : C} (f : X ⟶ Y)
    (hX : IsCofibrant X) (hY : IsCofibrant Y) (hf : weakEquivalences C f) :
    weakEquivalences C (K ◁ f) := by
  let _ : IsCofibrant K := hK
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant Y := hY
  let _ : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  let _ : WeakEquivalence (K ◁ f) := hPP.whiskerLeft_weakEquivalence_of_cofibrant K f
  exact mem_weakEquivalences _

/-- Membership form of the right tensor Brown theorem for the same
original map and both true cofibrant endpoints. -/
theorem whiskerRight_mem_weakEquivalences
    {X Y : C} (f : X ⟶ Y) (K : C) (hK : IsCofibrant K)
    (hX : IsCofibrant X) (hY : IsCofibrant Y) (hf : weakEquivalences C f) :
    weakEquivalences C (f ▷ K) := by
  let _ : IsCofibrant K := hK
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant Y := hY
  let _ : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  let _ : WeakEquivalence (f ▷ K) := hPP.whiskerRight_weakEquivalence_of_cofibrant f K
  exact mem_weakEquivalences _

/-- The literal tensor of two weak equivalences between cofibrant objects
is weak. The proof factors that same tensor map into its two whiskers. -/
theorem tensorHom_weakEquivalence
    {X Y A B : C} (f : X ⟶ Y) (g : A ⟶ B)
    [WeakEquivalence f] [WeakEquivalence g]
    [IsCofibrant X] [IsCofibrant Y] [IsCofibrant A] [IsCofibrant B] :
    WeakEquivalence (f ⊗ₘ g) := by
  let _ : WeakEquivalence (f ▷ A) := hPP.whiskerRight_weakEquivalence_of_cofibrant f A
  let _ : WeakEquivalence (Y ◁ g) := hPP.whiskerLeft_weakEquivalence_of_cofibrant Y g
  rw [tensorHom_def]
  infer_instance

/-- Actual internal Hom by a cofibrant factor preserves weak maps between
fibrant targets, using the same closed Quillen right adjoint. -/
theorem ihom_weakEquivalence_of_fibrant
    (K : C) [IsCofibrant K] {X Y : C} (f : X ⟶ Y)
    [WeakEquivalence f] [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence ((ihom K).map f) := by
  let _ : (ihom.adjunction K).IsQuillenAdjunction :=
    hPP.ihomAdjunction_isQuillenAdjunction K
  exact Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
    (adj := ihom.adjunction K) f

end HomotopicalAlgebra.MonoidalPushoutProductAxiom
