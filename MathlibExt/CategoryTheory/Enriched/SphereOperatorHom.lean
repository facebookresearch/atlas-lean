/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Kernel

/-!
# The full sphere-operator coend hom object

Fixing the second factor of the selected enriched tensor gives the weight
I(a tensor n,k). Its weighted coend with an enriched coefficient functor S
is the actual hom object required by the sphere-operator index. The full
I(a,b) balancing relation is retained. Composition and the spectrum carrier
are separate subsequent constructions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

namespace CategoryTheory.Enriched.SphereOperator

open MonoidalCategory Opposite BraidedCategory Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

attribute [local instance] Enriched.prodCategory

/-- Insert a fixed object using its entire enriched identity hom. -/
def fixedRightProduct (n : I) : EnrichedFunctor V I (I × I) where
  obj a := (a, n)
  map a b := (ρ_ (a ⟶[V] b)).inv ≫
    (𝟙 (a ⟶[V] b) ⊗ₘ eId V n)
  map_id a := by
    change eId V a ≫ (ρ_ (a ⟶[V] a)).inv ≫
        (𝟙 (a ⟶[V] a) ⊗ₘ eId V n) =
      (λ_ (𝟙_ V)).inv ≫ (eId V a ⊗ₘ eId V n)
    rw [rightUnitor_inv_naturality_assoc, unitors_inv_equal]
    slice_lhs 2 3 =>
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
      simp
  map_comp a b c := by
    have hIdentity : (eId V n ⊗ₘ eId V n) ≫ eComp V n n n =
        (λ_ (𝟙_ V)).hom ≫ eId V n := by
      rw [← cancel_epi (λ_ (𝟙_ V)).inv]
      simp only [Iso.inv_hom_id_assoc]
      rw [leftUnitor_inv_comp_tensorHom_assoc]
      rw [e_id_comp, Category.comp_id]
    have hTensorUnit {X Y Z : V} (f : X ⟶ Y) (g : 𝟙_ V ⟶ Z) :
        f ⊗ₘ g = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv ≫ Y ◁ g := by
      rw [← cancel_epi (ρ_ X).inv]
      simp only [Iso.inv_hom_id_assoc]
      exact rightUnitor_inv_comp_tensorHom f g
    change eComp V a b c ≫ (ρ_ (a ⟶[V] c)).inv ≫
        (𝟙 (a ⟶[V] c) ⊗ₘ eId V n) =
      (((ρ_ (a ⟶[V] b)).inv ≫
          (𝟙 (a ⟶[V] b) ⊗ₘ eId V n)) ⊗ₘ
        ((ρ_ (b ⟶[V] c)).inv ≫
          (𝟙 (b ⟶[V] c) ⊗ₘ eId V n))) ≫
        MonoidalCategory.tensorμ (a ⟶[V] b) (n ⟶[V] n)
          (b ⟶[V] c) (n ⟶[V] n) ≫
        (eComp V a b c ⊗ₘ eComp V n n n)
    rw [← cancel_epi (ρ_ ((a ⟶[V] b) ⊗ (b ⟶[V] c))).hom]
    nth_rewrite 2 [MonoidalCategory.tensor_right_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [MonoidalCategory.tensorμ_natural_assoc, tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rw [hIdentity]
    nth_rewrite 2 [← Category.id_comp (eComp V a b c)]
    rw [← tensorHom_comp_tensorHom]
    simp only [id_tensorHom]
    rw [hTensorUnit, ← MonoidalCategory.rightUnitor_monoidal_assoc,
      ← MonoidalCategory.tensor_right_unitality_assoc]

/-- Tensor with the fixed object through the selected full enriched tensor. -/
def fixedRightTensor (d : EnrichedMonoidalCategoryData V I) (n : I) :
    EnrichedFunctor V I I :=
  (fixedRightProduct (V := V) n).comp V d.tensorEnrichedFunctor

@[simp]
theorem fixedRightTensor_obj (d : EnrichedMonoidalCategoryData V I) (n a : I) :
    (fixedRightTensor d n).obj a = a ⊗ n := rfl

/-- The map uses the original full I(a,b) hom object and the fixed identity. -/
@[simp]
theorem fixedRightTensor_map (d : EnrichedMonoidalCategoryData V I) (n a b : I) :
    (fixedRightTensor d n).map a b =
      (ρ_ (a ⟶[V] b)).inv ≫ (𝟙 (a ⟶[V] b) ⊗ₘ eId V n) ≫
        d.tensorMap a b n n := by
  change ((ρ_ (a ⟶[V] b)).inv ≫
    (𝟙 (a ⟶[V] b) ⊗ₘ eId V n)) ≫ d.tensorMap a b n n = _
  exact Category.assoc _ _ _

/-- The fixed-factor enriched tensor preserves every original ordinary tensor-right map. -/
theorem fixedRightTensor_point (d : EnrichedMonoidalCategoryData V I) (n : I)
    {a b : I} (f : a ⟶ b) :
    eHomEquiv V f ≫ (fixedRightTensor d n).map a b = eHomEquiv V (f ▷ n) := by
  let H : V := a ⟶[V] b
  let p : 𝟙_ V ⟶ H := eHomEquiv V f
  have hp : (p ▷ (𝟙_ V)) ≫ (H ◁ eId V n) = p ⊗ₘ eId V n := by
    rw [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp]
  rw [fixedRightTensor_map, id_tensorHom]
  change p ≫ (ρ_ H).inv ≫ (H ◁ eId V n) ≫ d.tensorMap a b n n = _
  rw [rightUnitor_inv_naturality_assoc]
  rw [← Category.assoc (p ▷ (𝟙_ V)) (H ◁ eId V n) _, hp]
  simpa only [p, eHomEquiv_id, unitors_inv_equal, tensorHom_id] using
    d.tensorMap_eHomEquiv f (𝟙 n)

/-- The entire fixed-factor map preserves the enriched identity. -/
theorem fixedRightTensor_id (d : EnrichedMonoidalCategoryData V I) (n a : I) :
    eId V a ≫ (fixedRightTensor d n).map a a = eId V (a ⊗ n) :=
  (fixedRightTensor d n).map_id a

/-- The entire fixed-factor map preserves source-first enriched composition. -/
theorem fixedRightTensor_comp (d : EnrichedMonoidalCategoryData V I) (n a b c : I) :
    eComp V a b c ≫ (fixedRightTensor d n).map a c =
      ((fixedRightTensor d n).map a b ⊗ₘ (fixedRightTensor d n).map b c) ≫
        eComp V (a ⊗ n) (b ⊗ n) (c ⊗ n) :=
  (fixedRightTensor d n).map_comp a b c

/-- The opposite of the actual fixed-factor enriched tensor. -/
def oppositeFixedRightTensor (d : EnrichedMonoidalCategoryData V I) (n : I) :
    EnrichedFunctor V Iᵒᵖ Iᵒᵖ where
  obj a := op ((fixedRightTensor d n).obj a.unop)
  map a b := (fixedRightTensor d n).map b.unop a.unop
  map_id a := (fixedRightTensor d n).map_id a.unop
  map_comp a b c := by
    rw [eComp_op_eq, eComp_op_eq]
    rw [Category.assoc, (fixedRightTensor d n).map_comp]
    have h := braiding_naturality
      ((fixedRightTensor d n).map b.unop a.unop)
      ((fixedRightTensor d n).map c.unop b.unop)
    simpa only [Category.assoc] using congrArg
      (fun q => q ≫ eComp V ((fixedRightTensor d n).obj c.unop)
        ((fixedRightTensor d n).obj b.unop) ((fixedRightTensor d n).obj a.unop)) h.symm

variable [MonoidalClosed V]

/-- The actual I(a tensor n,k) contravariant enriched weight. -/
abbrev weight (d : EnrichedMonoidalCategoryData V I) (n k : I) :
    EnrichedFunctor V Iᵒᵖ V :=
  (oppositeFixedRightTensor d n).comp V
    (EnrichedFunctor.contravariantRepresentable V I k)

@[simp]
theorem weight_obj (d : EnrichedMonoidalCategoryData V I) (n k a : I) :
    (weight d n k).obj (op a) = ((a ⊗ n) ⟶[V] k) := rfl

/-- The complete weight action uses the tensor map and native composition. -/
theorem weight_uncurry_map (d : EnrichedMonoidalCategoryData V I) (n k a b : I) :
    MonoidalClosed.uncurry ((weight d n k).map (op b) (op a)) =
      ((b ⊗ n) ⟶[V] k) ◁ (fixedRightTensor d n).map a b ≫
        (β_ ((b ⊗ n) ⟶[V] k) ((a ⊗ n) ⟶[V] (b ⊗ n))).hom ≫
        eComp V (a ⊗ n) (b ⊗ n) k := by
  change MonoidalClosed.uncurry
      ((fixedRightTensor d n).map a b ≫ MonoidalClosed.curry
        ((β_ ((b ⊗ n) ⟶[V] k) ((a ⊗ n) ⟶[V] (b ⊗ n))).hom ≫
          eComp V (a ⊗ n) (b ⊗ n) k)) = _
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]

variable (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V) (n k : I)

/-- The original integrand is the full I(a tensor n,k) hom tensor S(a). -/
@[simp]
theorem operator_objects (a : I) :
    weightedCoend.objects (weight d n k) S a = ((a ⊗ n) ⟶[V] k) ⊗ S.obj a := rfl

/-- The original relation retains the entire enriched I(a,b) parameter. -/
@[simp]
theorem operator_relations (a b : I) :
    weightedCoend.relations (weight d n k) S (a, b) =
      ((b ⊗ n) ⟶[V] k) ⊗ ((a ⟶[V] b) ⊗ S.obj a) := rfl

variable [HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- The genuine operator hom, ∫ᵃ I(a tensor n,k) tensor S(a). -/
abbrev Hom : V := weightedCoend (weight d n k) S

/-- The canonical generators satisfy the full concrete operator balance. -/
theorem operator_balance (a b : I) :
    ((α_ ((b ⊗ n) ⟶[V] k) (a ⟶[V] b) (S.obj a)).inv ≫
        (((((b ⊗ n) ⟶[V] k) ◁ (fixedRightTensor d n).map a b) ≫
          (β_ ((b ⊗ n) ⟶[V] k) ((a ⊗ n) ⟶[V] (b ⊗ n))).hom ≫
          eComp V (a ⊗ n) (b ⊗ n) k) ⊗ₘ 𝟙 (S.obj a))) ≫
      weightedCoend.ι (weight d n k) S a =
    (((b ⊗ n) ⟶[V] k) ◁
      ((β_ (a ⟶[V] b) (S.obj a)).hom ≫
        MonoidalClosed.uncurry (S.map a b))) ≫
      weightedCoend.ι (weight d n k) S b := by
  have h := weightedCoend.condition (weight d n k) S a b
  rw [weight_uncurry_map] at h
  simpa only [weight_obj] using h

end CategoryTheory.Enriched.SphereOperator
