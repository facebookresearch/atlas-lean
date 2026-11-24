/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorHom

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

namespace CategoryTheory.Enriched.SphereOperatorTests

open MonoidalCategory Opposite Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

#check SphereOperator.fixedRightProduct
#check SphereOperator.fixedRightTensor
#check SphereOperator.fixedRightTensor.{0, 0, 0, 0}
#check SphereOperator.fixedRightTensor.{0, 1, 1, 0}
#check SphereOperator.fixedRightTensor.{1, 0, 0, 1}
#check SphereOperator.fixedRightTensor.{1, 1, 1, 1}
#check SphereOperator.weight
#check SphereOperator.weight.{0, 0, 0, 0}
#check SphereOperator.weight.{0, 1, 1, 0}
#check SphereOperator.weight.{1, 0, 0, 1}
#check SphereOperator.weight.{1, 1, 1, 1}
#check SphereOperator.Hom
#check SphereOperator.Hom.{0, 0, 0, 0}
#check SphereOperator.Hom.{0, 1, 1, 0}
#check SphereOperator.Hom.{1, 0, 0, 1}
#check SphereOperator.Hom.{1, 1, 1, 1}
#check SphereOperator.operator_objects
#check SphereOperator.operator_relations
#check SphereOperator.operator_balance
#check weightedCoend.ι
#check weightedCoend.condition
#check weightedCoend.desc
#check weightedCoend.ι_desc
#check weightedCoend.hom_ext

example (d : EnrichedMonoidalCategoryData V I) (n a : I) :
    (SphereOperator.fixedRightTensor d n).obj a = a ⊗ n :=
  SphereOperator.fixedRightTensor_obj d n a

example (d : EnrichedMonoidalCategoryData V I) (n a b : I) :
    (SphereOperator.fixedRightTensor d n).map a b =
      (ρ_ (a ⟶[V] b)).inv ≫ (𝟙 (a ⟶[V] b) ⊗ₘ eId V n) ≫
        d.tensorMap a b n n := SphereOperator.fixedRightTensor_map d n a b

example (d : EnrichedMonoidalCategoryData V I) (n a : I) :
    eId V a ≫ (SphereOperator.fixedRightTensor d n).map a a = eId V (a ⊗ n) :=
  SphereOperator.fixedRightTensor_id d n a

example (d : EnrichedMonoidalCategoryData V I) (n a b c : I) :
    eComp V a b c ≫ (SphereOperator.fixedRightTensor d n).map a c =
      ((SphereOperator.fixedRightTensor d n).map a b ⊗ₘ
        (SphereOperator.fixedRightTensor d n).map b c) ≫
          eComp V (a ⊗ n) (b ⊗ n) (c ⊗ n) :=
  SphereOperator.fixedRightTensor_comp d n a b c

example (d : EnrichedMonoidalCategoryData V I) (n k a : I) :
    (SphereOperator.weight d n k).obj (op a) = ((a ⊗ n) ⟶[V] k) :=
  SphereOperator.weight_obj d n k a

example (d : EnrichedMonoidalCategoryData V I) (n k a b : I) :
    MonoidalClosed.uncurry ((SphereOperator.weight d n k).map (op b) (op a)) =
      ((b ⊗ n) ⟶[V] k) ◁ (SphereOperator.fixedRightTensor d n).map a b ≫
        (β_ ((b ⊗ n) ⟶[V] k) ((a ⊗ n) ⟶[V] (b ⊗ n))).hom ≫
          eComp V (a ⊗ n) (b ⊗ n) k :=
  SphereOperator.weight_uncurry_map d n k a b

variable (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V) (n k : I)

example (a : I) :
    weightedCoend.objects (SphereOperator.weight d n k) S a =
      ((a ⊗ n) ⟶[V] k) ⊗ S.obj a := SphereOperator.operator_objects d S n k a

example (a b : I) :
    weightedCoend.relations (SphereOperator.weight d n k) S (a, b) =
      ((b ⊗ n) ⟶[V] k) ⊗ ((a ⟶[V] b) ⊗ S.obj a) :=
  SphereOperator.operator_relations d S n k a b

section ParticularColimits

variable [HasCoproduct (weightedCoend.relations (SphereOperator.weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (SphereOperator.weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (SphereOperator.weight d n k) S)
    (weightedCoend.rightMap (SphereOperator.weight d n k) S)]

example : SphereOperator.Hom d S n k = weightedCoend (SphereOperator.weight d n k) S := rfl

example (a b : I) :
    ((α_ ((b ⊗ n) ⟶[V] k) (a ⟶[V] b) (S.obj a)).inv ≫
        (((((b ⊗ n) ⟶[V] k) ◁ (SphereOperator.fixedRightTensor d n).map a b) ≫
          (β_ ((b ⊗ n) ⟶[V] k) ((a ⊗ n) ⟶[V] (b ⊗ n))).hom ≫
          eComp V (a ⊗ n) (b ⊗ n) k) ⊗ₘ 𝟙 (S.obj a))) ≫
      weightedCoend.ι (SphereOperator.weight d n k) S a =
    (((b ⊗ n) ⟶[V] k) ◁
      ((β_ (a ⟶[V] b) (S.obj a)).hom ≫ MonoidalClosed.uncurry (S.map a b))) ≫
        weightedCoend.ι (SphereOperator.weight d n k) S b :=
  SphereOperator.operator_balance d S n k a b

example {X : V}
    (q : ∀ a, weightedCoend.objects (SphereOperator.weight d n k) S a ⟶ X)
    (h : ∀ a b,
      ((α_ ((SphereOperator.weight d n k).obj (op b)) (a ⟶[V] b) (S.obj a)).inv ≫
          (MonoidalClosed.uncurry ((SphereOperator.weight d n k).map (op b) (op a)) ⊗ₘ
            𝟙 (S.obj a))) ≫ q a =
        ((SphereOperator.weight d n k).obj (op b) ◁
          ((β_ (a ⟶[V] b) (S.obj a)).hom ≫ MonoidalClosed.uncurry (S.map a b))) ≫ q b)
    (a : I) :
    weightedCoend.ι (SphereOperator.weight d n k) S a ≫
        weightedCoend.desc (SphereOperator.weight d n k) S q h = q a :=
  weightedCoend.ι_desc (SphereOperator.weight d n k) S q h a

example {X : V} (f g : SphereOperator.Hom d S n k ⟶ X)
    (h : ∀ a, weightedCoend.ι (SphereOperator.weight d n k) S a ≫ f =
      weightedCoend.ι (SphereOperator.weight d n k) S a ≫ g) : f = g :=
  weightedCoend.hom_ext (SphereOperator.weight d n k) S h

/-! The canonical coend interface also gives the original full Hom correspondence,
locally in this client rather than through a second public coend API. -/
example (X : V) :
    let W := SphereOperator.weight d n k
    let B (q : ∀ a, weightedCoend.objects W S a ⟶ X) : Prop :=
      ∀ a b,
        ((α_ (W.obj (op b)) (a ⟶[V] b) (S.obj a)).inv ≫
            (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ 𝟙 (S.obj a))) ≫ q a =
          (W.obj (op b) ◁
            ((β_ (a ⟶[V] b) (S.obj a)).hom ≫ MonoidalClosed.uncurry (S.map a b))) ≫ q b
    (SphereOperator.Hom d S n k ⟶ X) ≃
      {q : ∀ a, weightedCoend.objects W S a ⟶ X // B q} := by
  dsimp only
  refine
    { toFun := fun f => ?_
      invFun := fun q => weightedCoend.desc (SphereOperator.weight d n k) S q.val q.property
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨fun a => weightedCoend.ι (SphereOperator.weight d n k) S a ≫ f, ?_⟩
    intro a b
    simpa only [Category.assoc] using congrArg (fun q => q ≫ f)
      (weightedCoend.condition (SphereOperator.weight d n k) S a b)
  · intro f
    apply weightedCoend.hom_ext (SphereOperator.weight d n k) S
    intro a
    apply weightedCoend.ι_desc
  · intro q
    apply Subtype.ext
    funext a
    exact weightedCoend.ι_desc (SphereOperator.weight d n k) S q.val q.property a

end ParticularColimits

#guard_msgs (error, substring := true) in
example : V := SphereOperator.Hom d S n k

#print axioms SphereOperator.fixedRightProduct
#print axioms SphereOperator.fixedRightTensor
#print axioms SphereOperator.oppositeFixedRightTensor
#print axioms SphereOperator.weight
#print axioms SphereOperator.Hom
#print axioms SphereOperator.operator_balance

end CategoryTheory.Enriched.SphereOperatorTests
