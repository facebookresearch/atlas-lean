/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStablePuppeConnecting
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoBiproducts

/-!
# The original ordinary-stable cofiber coaction

The target is the same original R-product/biproduct of the actual
Q-cofiber and its original framing suspension. The two maps are the
identity and the same cone/framing boundary. This is the stable
coaction presentation of Hovey, Model Categories, Remark 7.1.3.
The original product universal property proves uniqueness and complete
Arrow naturality. Its original coproduct desc gives the full right
Hom action, with unit, associativity and both naturality directions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStableCofiberCoaction

open OrdinaryStablePuppeGroups

private theorem compositionDesc {D : Type*} [Category* D] [Preadditive D]
    {T X Y P E : D} (c : T ⟶ P) (p : P ⟶ X) (q : P ⟶ Y)
    (f : T ⟶ X) (h : T ⟶ Y) (a : X ⟶ E) (b : Y ⟶ E)
    (hp : c ≫ p = f) (hq : c ≫ q = h) :
    c ≫ (p ≫ a + q ≫ b) = f ≫ a + h ≫ b := by
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hp, hq]

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)

/-- The entire original coproduct map retains the two original bicone projection words. -/
theorem desc_apply {X Y E : HomotopyCategory C} (p : X ⟶ E) (q : Y ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OrdinaryStableHoBiproducts.desc g p q =
      (OrdinaryStableHoBiproducts.bicone g X Y).fst ≫ p +
        (OrdinaryStableHoBiproducts.bicone g X Y).snd ≫ q :=
  rfl

/-- The same original lift and coproduct desc retain all four caller maps. -/
theorem lift_desc {T X Y E : HomotopyCategory C}
    (f : T ⟶ X) (h : T ⟶ Y) (p : X ⟶ E) (q : Y ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    GeneratedOrdinaryHoProducts.lift g f h ≫ OrdinaryStableHoBiproducts.desc g p q =
      f ≫ p + h ≫ q := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [desc_apply]
  exact @compositionDesc (HomotopyCategory C) _ (OrdinaryStableHoPreadditive.preadditive g)
    T X Y (OrdinaryStableHoBiproducts.bicone g X Y).pt E
    (GeneratedOrdinaryHoProducts.lift g f h)
    (OrdinaryStableHoBiproducts.bicone g X Y).fst
    (OrdinaryStableHoBiproducts.bicone g X Y).snd f h p q
    (GeneratedOrdinaryHoProducts.lift_fst g f h) (GeneratedOrdinaryHoProducts.lift_snd g f h)

/-- The coaction uses the SAME original generated product of the actual two source objects. -/
def target (F : Arrow C) : HomotopyCategory C :=
  GeneratedOrdinaryHoProducts.product g (cofiberHo g Z hZ F)
    ((Σ).obj ((toHomotopyCategory C).obj F.left))

/-- Both coaction components are the actual identity and the original cone/framing boundary. -/
def coaction (F : Arrow C) : cofiberHo g Z hZ F ⟶ target g Z hZ F :=
  GeneratedOrdinaryHoProducts.lift g (𝟙 (cofiberHo g Z hZ F))
    (OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F)

omit [(DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- The original first product projection recovers the entire identity map. -/
theorem coaction_fst (F : Arrow C) :
    coaction g Z hZ F ≫
      (GeneratedOrdinaryHoProducts.fan g (cofiberHo g Z hZ F)
        ((Σ).obj ((toHomotopyCategory C).obj F.left))).fst = 𝟙 (cofiberHo g Z hZ F) :=
  GeneratedOrdinaryHoProducts.lift_fst g _ _

omit [(DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- The original second projection is the same complete source boundary, including its sign. -/
theorem coaction_snd (F : Arrow C) :
    coaction g Z hZ F ≫
      (GeneratedOrdinaryHoProducts.fan g (cofiberHo g Z hZ F)
        ((Σ).obj ((toHomotopyCategory C).obj F.left))).snd =
      OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F :=
  GeneratedOrdinaryHoProducts.lift_snd g _ _

omit [(DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- Both original projection equations determine the whole coaction uniquely. -/
theorem coaction_unique (F : Arrow C) (p : cofiberHo g Z hZ F ⟶ target g Z hZ F)
    (h₁ : p ≫ (GeneratedOrdinaryHoProducts.fan g (cofiberHo g Z hZ F)
      ((Σ).obj ((toHomotopyCategory C).obj F.left))).fst = 𝟙 (cofiberHo g Z hZ F))
    (h₂ : p ≫ (GeneratedOrdinaryHoProducts.fan g (cofiberHo g Z hZ F)
      ((Σ).obj ((toHomotopyCategory C).obj F.left))).snd =
        OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F) :
    p = coaction g Z hZ F :=
  GeneratedOrdinaryHoProducts.hom_ext g _ _
    (h₁.trans (coaction_fst g Z hZ F).symm) (h₂.trans (coaction_snd g Z hZ F).symm)

/-- Every original Arrow square maps the same two original product coordinates. -/
def targetMap {F G : Arrow C} (a : F ⟶ G) : target g Z hZ F ⟶ target g Z hZ G :=
  GeneratedOrdinaryHoProducts.lift g
    ((GeneratedOrdinaryHoProducts.fan g (cofiberHo g Z hZ F)
      ((Σ).obj ((toHomotopyCategory C).obj F.left))).fst ≫
        OrdinaryStablePuppeConnecting.cofiberMap g Z hZ a)
    ((GeneratedOrdinaryHoProducts.fan g (cofiberHo g Z hZ F)
      ((Σ).obj ((toHomotopyCategory C).obj F.left))).snd ≫
        (Σ).map ((toHomotopyCategory C).map a.left))

omit [(DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- Both original Arrow components retain the whole coaction square. -/
theorem coaction_naturality {F G : Arrow C} (a : F ⟶ G) :
    OrdinaryStablePuppeConnecting.cofiberMap g Z hZ a ≫ coaction g Z hZ G =
      coaction g Z hZ F ≫ targetMap g Z hZ a := by
  unfold targetMap target
  apply GeneratedOrdinaryHoProducts.hom_ext g
  · rw [Category.assoc, coaction_fst, Category.comp_id, Category.assoc,
      GeneratedOrdinaryHoProducts.lift_fst, ← Category.assoc, coaction_fst, Category.id_comp]
  · rw [Category.assoc, coaction_snd, Category.assoc, GeneratedOrdinaryHoProducts.lift_snd,
      ← Category.assoc, coaction_snd]
    exact OrdinaryStablePuppeConnecting.boundary_naturality g Z hZ a

/-- The stable right Hom action retains the original source boundary and additive Hom operations. -/
def act (F : Arrow C) (E : HomotopyCategory C)
    (f : cofiberHo g Z hZ F ⟶ E)
    (a : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E) : cofiberHo g Z hZ F ⟶ E := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact f + OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F ≫ a

/-- The entire action function keeps the original cofiber map and original connecting word. -/
theorem act_apply (F : Arrow C) (E : HomotopyCategory C)
    (f : cofiberHo g Z hZ F ⟶ E)
    (a : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    act g Z hZ F E f a = f + OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F ≫ a :=
  rfl

/-- The full right action is induced by the actual coaction and the original coproduct desc. -/
theorem act_from_coaction (F : Arrow C) (E : HomotopyCategory C)
    (f : cofiberHo g Z hZ F ⟶ E)
    (a : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E) :
    coaction g Z hZ F ≫ OrdinaryStableHoBiproducts.desc g f a = act g Z hZ F E f a := by
  let := OrdinaryStableHoPreadditive.preadditive g
  unfold coaction
  rw [lift_desc, Category.id_comp, act_apply]

/-- The actual additive zero of the original suspension Hom group is the action unit. -/
theorem act_zero (F : Arrow C) (E : HomotopyCategory C) (f : cofiberHo g Z hZ F ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    act g Z hZ F E f 0 = f := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [act_apply, comp_zero, add_zero]

/-- The source-built Hom action is associative under the same original represented group addition. -/
theorem act_add (F : Arrow C) (E : HomotopyCategory C) (f : cofiberHo g Z hZ F ⟶ E)
    (a b : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    act g Z hZ F E (act g Z hZ F E f a) b = act g Z hZ F E f (a + b) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [act_apply, act_apply, act_apply, Preadditive.comp_add, add_assoc]

/-- Every original target Ho morphism preserves the whole action and actual connecting function. -/
theorem act_target (F : Arrow C) {E E' : HomotopyCategory C} (t : E ⟶ E')
    (f : cofiberHo g Z hZ F ⟶ E)
    (a : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E) :
    act g Z hZ F E f a ≫ t = act g Z hZ F E' (f ≫ t) (a ≫ t) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [act_apply, act_apply, Preadditive.add_comp, Category.assoc]

/-- Both original input-square components preserve the actual source coaction action. -/
theorem act_source {F G : Arrow C} (t : F ⟶ G) (E : HomotopyCategory C)
    (f : cofiberHo g Z hZ G ⟶ E)
    (a : (Σ).obj ((toHomotopyCategory C).obj G.left) ⟶ E) :
    OrdinaryStablePuppeConnecting.cofiberMap g Z hZ t ≫ act g Z hZ G E f a =
      act g Z hZ F E (OrdinaryStablePuppeConnecting.cofiberMap g Z hZ t ≫ f)
        ((Σ).map ((toHomotopyCategory C).map t.left) ≫ a) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [act_apply, act_apply, Preadditive.comp_add, ← Category.assoc,
    OrdinaryStablePuppeConnecting.boundary_naturality, Category.assoc]

end HomotopicalAlgebra.OrdinaryStableCofiberCoaction
