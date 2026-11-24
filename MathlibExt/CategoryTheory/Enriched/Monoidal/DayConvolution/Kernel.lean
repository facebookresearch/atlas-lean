/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend

/-!
# Enriched Day kernels and their universal property

An enriched binary functor gives the weight at each output object. The
weighted coend represents families balanced over the whole enriched hom.
Only its two particular coproducts and particular coequalizer are needed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC uD uK uV vV

namespace CategoryTheory.EnrichedDayKernel

open MonoidalCategory BraidedCategory Opposite Limits
open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]

/-- The literal opposite of the selected enriched binary functor. -/
def oppositeTensor (T : EnrichedFunctor V (C × D) K) :
    EnrichedFunctor V (C × D)ᵒᵖ Kᵒᵖ where
  obj X := op (T.obj X.unop)
  map X Y := T.map Y.unop X.unop
  map_id X := T.map_id X.unop
  map_comp X Y Z := by
    rw [eComp_op_eq, eComp_op_eq]
    rw [Category.assoc, T.map_comp]
    have h := braiding_naturality (T.map Y.unop X.unop) (T.map Z.unop Y.unop)
    simpa only [Category.assoc] using congrArg
      (fun q => q ≫ eComp V (T.obj Z.unop) (T.obj Y.unop) (T.obj X.unop)) h.symm

/-- The opposite tensor retains the selected objects. -/
@[simp]
theorem oppositeTensor_obj (T : EnrichedFunctor V (C × D) K) (X : (C × D)ᵒᵖ) :
    (oppositeTensor T).obj X = op (T.obj X.unop) := rfl

/-- The opposite tensor retains the entire reversed enriched hom map. -/
@[simp]
theorem oppositeTensor_map (T : EnrichedFunctor V (C × D) K) (X Y : (C × D)ᵒᵖ) :
    (oppositeTensor T).map X Y = T.map Y.unop X.unop := rfl

variable [MonoidalClosed V]

/-- The contravariant representable weight of a Day kernel at k. -/
abbrev weight (T : EnrichedFunctor V (C × D) K) (k : K) :
    EnrichedFunctor V (C × D)ᵒᵖ V :=
  (oppositeTensor T).comp V (EnrichedFunctor.contravariantRepresentable V K k)

/-- The weight is the actual enriched hom from the selected binary object. -/
@[simp]
theorem weight_obj (T : EnrichedFunctor V (C × D) K) (k : K) (a : C × D) :
    (weight T k).obj (op a) = (T.obj a ⟶[V] k) := rfl

/-- The full contravariant weight action uses the positive braid and enriched composition. -/
theorem weight_uncurry_map (T : EnrichedFunctor V (C × D) K) (k : K) (a b : C × D) :
    MonoidalClosed.uncurry ((weight T k).map (op b) (op a)) =
      (T.obj b ⟶[V] k) ◁ T.map a b ≫
        (β_ (T.obj b ⟶[V] k) (T.obj a ⟶[V] T.obj b)).hom ≫
        eComp V (T.obj a) (T.obj b) k := by
  change MonoidalClosed.uncurry
      (T.map a b ≫ MonoidalClosed.curry
        ((β_ (T.obj b ⟶[V] k) (T.obj a ⟶[V] T.obj b)).hom ≫
          eComp V (T.obj a) (T.obj b) k)) = _
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]

variable (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K)

/-- The integrands in the particular Day coproduct. -/
abbrev objects : C × D → V :=
  Enriched.weightedCoend.objects (weight T k) (F.externalTensor G)

/-- The full hom-object integrands in the particular relation coproduct. -/
abbrev relations : (C × D) × (C × D) → V :=
  Enriched.weightedCoend.relations (weight T k) (F.externalTensor G)

/-- A family balanced over the entire product-enriched hom object. -/
abbrev Balanced {X : V} (q : ∀ a, objects T F G k a ⟶ X) : Prop :=
  ∀ a b,
    ((α_ ((weight T k).obj (op b)) (a ⟶[V] b) ((F.externalTensor G).obj a)).inv ≫
        (MonoidalClosed.uncurry ((weight T k).map (op b) (op a)) ⊗ₘ
          𝟙 ((F.externalTensor G).obj a))) ≫ q a =
      ((weight T k).obj (op b) ◁
        ((β_ (a ⟶[V] b) ((F.externalTensor G).obj a)).hom ≫
          MonoidalClosed.uncurry ((F.externalTensor G).map a b))) ≫ q b

variable [HasCoproduct (relations T F G k)] [HasCoproduct (objects T F G k)]

/-- The particular parallel map induced by the contravariant weight action. -/
abbrev leftMap : (∐ relations T F G k) ⟶ ∐ objects T F G k :=
  Enriched.weightedCoend.leftMap (weight T k) (F.externalTensor G)

/-- The particular parallel map induced by the covariant diagram action. -/
abbrev rightMap : (∐ relations T F G k) ⟶ ∐ objects T F G k :=
  Enriched.weightedCoend.rightMap (weight T k) (F.externalTensor G)

variable [HasCoequalizer (leftMap T F G k) (rightMap T F G k)]

/-- The selected Day kernel object at k. -/
abbrev obj : V := Enriched.weightedCoend (weight T k) (F.externalTensor G)

/-- The actual integrand generator into the selected coend. -/
def gen (a : C × D) : objects T F G k a ⟶ obj T F G k :=
  Enriched.weightedCoend.ι (weight T k) (F.externalTensor G) a

/-- The selected generators satisfy the full enriched balancing equation. -/
theorem gen_balanced : Balanced T F G k (gen T F G k) := by
  intro a b
  exact Enriched.weightedCoend.condition (weight T k) (F.externalTensor G) a b

/-- Descend any genuinely balanced family through the selected coend. -/
def desc {X : V} (q : ∀ a, objects T F G k a ⟶ X) (h : Balanced T F G k q) :
    obj T F G k ⟶ X :=
  Enriched.weightedCoend.desc (weight T k) (F.externalTensor G) q h

/-- A descended map agrees with the supplied family on every generator. -/
@[reassoc]
theorem gen_desc {X : V} (q : ∀ a, objects T F G k a ⟶ X)
    (h : Balanced T F G k q) (a : C × D) :
    gen T F G k a ≫ desc T F G k q h = q a :=
  Enriched.weightedCoend.ι_desc (weight T k) (F.externalTensor G) q h a

/-- Equality of maps from the coend is tested on its actual generators. -/
theorem hom_ext {X : V} {f g : obj T F G k ⟶ X}
    (h : ∀ a, gen T F G k a ≫ f = gen T F G k a ≫ g) : f = g :=
  Enriched.weightedCoend.hom_ext (weight T k) (F.externalTensor G) h

/-- The Day kernel represents precisely the genuinely balanced families. -/
def homEquiv (X : V) :
    (obj T F G k ⟶ X) ≃
      {q : ∀ a, objects T F G k a ⟶ X // Balanced T F G k q} where
  toFun f := ⟨fun a => gen T F G k a ≫ f, by
    intro a b
    simpa only [Category.assoc] using congrArg (fun q => q ≫ f)
      (gen_balanced T F G k a b)⟩
  invFun q := desc T F G k q.val q.property
  left_inv f := by
    apply hom_ext T F G k
    intro a
    apply gen_desc
  right_inv q := by
    apply Subtype.ext
    funext a
    exact gen_desc T F G k q.val q.property a

end CategoryTheory.EnrichedDayKernel
