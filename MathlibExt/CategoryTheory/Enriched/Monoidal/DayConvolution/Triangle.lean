/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorFunctor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Unitors

/-!
# Triangle

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorTriangle

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- Insert an actual supplied unit-point in the weight factor of a coefficient word. -/
abbrev pointInsert {R : V} (q : 𝟙_ V ⟶ R) (A : V) : A ⟶ R ⊗ A :=
  (λ_ A).inv ≫ (q ⊗ₘ 𝟙 A)

@[reassoc]
theorem pointInsert_natural {R A B : V} (q : 𝟙_ V ⟶ R) (f : A ⟶ B) :
    pointInsert q A ≫ R ◁ f = f ≫ pointInsert q B := by
  simp only [pointInsert, Category.assoc]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id]

@[reassoc]
theorem pointInsert_tensor {R : V} (q : 𝟙_ V ⟶ R) (A B : V) :
    pointInsert q A ▷ B ≫ (α_ R A B).hom = pointInsert q (A ⊗ B) := by
  simp only [pointInsert, comp_whiskerRight, tensorHom_id, Category.assoc]
  rw [associator_naturality_left]
  monoidal

@[reassoc]
theorem pointInsert_weight {R W X : V} (q : 𝟙_ V ⟶ R) (A : V) (k : W ⊗ R ⟶ X) :
    W ◁ pointInsert q A ≫ (α_ W R A).inv ≫ (k ⊗ₘ 𝟙 A) =
      ((ρ_ W).inv ≫ (𝟙 W ⊗ₘ q) ≫ k) ⊗ₘ 𝟙 A := by
  simp only [pointInsert, whiskerLeft_comp, Category.assoc, tensorHom_id]
  rw [associator_inv_naturality_middle_assoc]
  have h : W ◁ (λ_ A).inv ≫ (α_ W (𝟙_ V) A).inv = (ρ_ W).inv ▷ A := by
    monoidal
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [comp_whiskerRight, id_tensorHom, Category.assoc]

section Front
variable [SymmetricCategory V]

@[reassoc]
theorem pointInsert_front {R : V} (q : 𝟙_ V ⟶ R) (B A : V) :
    B ◁ pointInsert q A ≫ (AssociatorRightContraction.frontHomIso R B A).hom =
      pointInsert q (B ⊗ A) := by
  simp only [AssociatorRightContraction.frontHomIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Iso.refl_hom, pointInsert, whiskerLeft_comp, Category.assoc, tensorHom_id]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc]
  rw [associator_naturality_left]
  rw [braiding_tensorUnit_right]
  monoidal

end Front

section IndexPoints

variable [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)

attribute [local instance] Enriched.prodCategory

omit [MonoidalClosed V] in
theorem rightInclusion_tensor_point {x y : I} (f : x ⟶ y) (k : I) :
    eHomEquiv V f ≫ (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) k).map x y ≫
        d.tensorMap x y k k = eHomEquiv V (f ▷ k) := by
  let r : (x ⟶[V] y) ⟶ (x ⟶[V] y) ⊗ (k ⟶[V] k) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) k).map x y
  have hr : r = (ρ_ (x ⟶[V] y)).inv ≫ (𝟙 (x ⟶[V] y) ⊗ₘ eId V k) :=
    EnrichedFunctor.prodLeftInclusion_map k x y
  change eHomEquiv V f ≫ r ≫ d.tensorMap x y k k = _
  rw [hr, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  simpa only [eHomEquiv_id, unitors_inv_equal, tensorHom_id] using d.tensorMap_eHomEquiv f (𝟙 k)

omit [MonoidalClosed V] in
theorem leftInclusion_tensor_point {x y : I} (f : x ⟶ y) (k : I) :
    eHomEquiv V f ≫ (EnrichedFunctor.prodRightInclusion (V := V) (B := I) k).map x y ≫
        d.tensorMap k k x y = eHomEquiv V (k ◁ f) := by
  let r : (x ⟶[V] y) ⟶ (k ⟶[V] k) ⊗ (x ⟶[V] y) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := I) k).map x y
  have hr : r = (λ_ (x ⟶[V] y)).inv ≫ (eId V k ⊗ₘ 𝟙 (x ⟶[V] y)) :=
    EnrichedFunctor.prodRightInclusion_map k x y
  change eHomEquiv V f ≫ r ≫ d.tensorMap k k x y = _
  rw [hr, Category.assoc]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  simpa only [eHomEquiv_id, id_tensorHom] using d.tensorMap_eHomEquiv (𝟙 k) f

omit [MonoidalClosed V] [MonoidalCategory I] in
theorem point_precomposition {x y : I} (f : x ⟶ y) (m : I) :
    (ρ_ (y ⟶[V] m)).inv ≫ (𝟙 (y ⟶[V] m) ⊗ₘ eHomEquiv V f) ≫
        (β_ (y ⟶[V] m) (x ⟶[V] y)).hom ≫ eComp V x y m =
      eHomWhiskerRight V f m := by
  simp only [eHomWhiskerRight]
  rw [BraidedCategory.braiding_naturality_assoc, rightUnitor_inv_braiding_assoc, tensorHom_id]

/-- Evaluate the original full left weight-slice action on its actual index arrow. -/
theorem left_sliceBase_point (m : I) (p a : I × I) (f : (a.1 ⊗ a.2) ⟶ p.1) :
    (ρ_ ((p.1 ⊗ p.2) ⟶[V] m)).inv ≫
        (𝟙 ((p.1 ⊗ p.2) ⟶[V] m) ⊗ₘ eHomEquiv V f) ≫
          AssociatorFlattening.sliceBase d m p a = eHomWhiskerRight V (f ▷ p.2) m := by
  let W : V := (p.1 ⊗ p.2) ⟶[V] m
  let R : V := (a.1 ⊗ a.2) ⟶[V] p.1
  let S : V := ((a.1 ⊗ a.2) ⊗ p.2) ⟶[V] (p.1 ⊗ p.2)
  let P : V := (a.1 ⊗ a.2, p.2) ⟶[V] p
  let W' : V := ((a.1 ⊗ a.2) ⊗ p.2) ⟶[V] m
  let i : R ⟶ P :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) p.2).map (a.1 ⊗ a.2) p.1
  let tm : P ⟶ S := d.tensorMap (a.1 ⊗ a.2) p.1 p.2 p.2
  let t : R ⟶ S := i ≫ tm
  let w : P ⟶ (ihom W).obj W' :=
    (weight d.tensorEnrichedFunctor m).map (op p) (op (a.1 ⊗ a.2, p.2))
  let tail : W ⊗ S ⟶ W' := (β_ W S).hom ≫ eComp V ((a.1 ⊗ a.2) ⊗ p.2) (p.1 ⊗ p.2) m
  let c : W ⊗ R ⟶ W' := AssociatorFlattening.sliceBase d m p a
  have ht : eHomEquiv V f ≫ t = eHomEquiv V (f ▷ p.2) :=
    rightInclusion_tensor_point d f p.2
  have hw : MonoidalClosed.uncurry w = W ◁ tm ≫ tail :=
    weight_uncurry_map d.tensorEnrichedFunctor m (a.1 ⊗ a.2, p.2) p
  have hdef : c = W ◁ i ≫ MonoidalClosed.uncurry w := rfl
  have hs : c = W ◁ t ≫ tail :=
    hdef.trans ((congrArg (fun z => W ◁ i ≫ z) hw).trans
      (whiskerLeft_comp_assoc W i tm tail).symm)
  change (ρ_ W).inv ≫ (𝟙 W ⊗ₘ eHomEquiv V f) ≫ c = eHomWhiskerRight V (f ▷ p.2) m
  have h0 : (ρ_ W).inv ≫ (𝟙 W ⊗ₘ eHomEquiv V f) ≫ c =
      (ρ_ W).inv ≫ W ◁ (eHomEquiv V f ≫ t) ≫ tail := by
    exact (congrArg (fun z => (ρ_ W).inv ≫ (𝟙 W ⊗ₘ eHomEquiv V f) ≫ z) hs).trans
      (by simp only [id_tensorHom, whiskerLeft_comp, Category.assoc])
  have h1 := congrArg (fun z => (ρ_ W).inv ≫ W ◁ z ≫ tail) ht
  have h2 : (ρ_ W).inv ≫ W ◁ eHomEquiv V (f ▷ p.2) ≫ tail =
      eHomWhiskerRight V (f ▷ p.2) m := by
    simpa only [id_tensorHom] using point_precomposition (f ▷ p.2) m
  exact h0.trans (h1.trans h2)

/-- Evaluate the original full right weight-slice action on its actual index arrow. -/
theorem right_sliceBase_point (m : I) (p a : I × I) (f : (a.1 ⊗ a.2) ⟶ p.2) :
    (ρ_ ((p.1 ⊗ p.2) ⟶[V] m)).inv ≫
        (𝟙 ((p.1 ⊗ p.2) ⟶[V] m) ⊗ₘ eHomEquiv V f) ≫
          AssociatorRightFlattening.sliceBase d m p a = eHomWhiskerRight V (p.1 ◁ f) m := by
  let W : V := (p.1 ⊗ p.2) ⟶[V] m
  let R : V := (a.1 ⊗ a.2) ⟶[V] p.2
  let S : V := (p.1 ⊗ (a.1 ⊗ a.2)) ⟶[V] (p.1 ⊗ p.2)
  let P : V := (p.1, a.1 ⊗ a.2) ⟶[V] p
  let W' : V := (p.1 ⊗ (a.1 ⊗ a.2)) ⟶[V] m
  let i : R ⟶ P :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := I) p.1).map (a.1 ⊗ a.2) p.2
  let tm : P ⟶ S := d.tensorMap p.1 p.1 (a.1 ⊗ a.2) p.2
  let t : R ⟶ S := i ≫ tm
  let w : P ⟶ (ihom W).obj W' :=
    (weight d.tensorEnrichedFunctor m).map (op p) (op (p.1, a.1 ⊗ a.2))
  let tail : W ⊗ S ⟶ W' := (β_ W S).hom ≫ eComp V (p.1 ⊗ (a.1 ⊗ a.2)) (p.1 ⊗ p.2) m
  let c : W ⊗ R ⟶ W' := AssociatorRightFlattening.sliceBase d m p a
  have ht : eHomEquiv V f ≫ t = eHomEquiv V (p.1 ◁ f) :=
    leftInclusion_tensor_point d f p.1
  have hw : MonoidalClosed.uncurry w = W ◁ tm ≫ tail :=
    weight_uncurry_map d.tensorEnrichedFunctor m (p.1, a.1 ⊗ a.2) p
  have hdef : c = W ◁ i ≫ MonoidalClosed.uncurry w := rfl
  have hs : c = W ◁ t ≫ tail :=
    hdef.trans ((congrArg (fun z => W ◁ i ≫ z) hw).trans
      (whiskerLeft_comp_assoc W i tm tail).symm)
  change (ρ_ W).inv ≫ (𝟙 W ⊗ₘ eHomEquiv V f) ≫ c = eHomWhiskerRight V (p.1 ◁ f) m
  have h0 : (ρ_ W).inv ≫ (𝟙 W ⊗ₘ eHomEquiv V f) ≫ c =
      (ρ_ W).inv ≫ W ◁ (eHomEquiv V f ≫ t) ≫ tail := by
    exact (congrArg (fun z => (ρ_ W).inv ≫ (𝟙 W ⊗ₘ eHomEquiv V f) ≫ z) hs).trans
      (by simp only [id_tensorHom, whiskerLeft_comp, Category.assoc])
  have h1 := congrArg (fun z => (ρ_ W).inv ≫ W ◁ z ≫ tail) ht
  have h2 : (ρ_ W).inv ≫ W ◁ eHomEquiv V (p.1 ◁ f) ≫ tail =
      eHomWhiskerRight V (p.1 ◁ f) m := by
    simpa only [id_tensorHom] using point_precomposition (p.1 ◁ f) m
  exact h0.trans (h1.trans h2)

variable (F G H : EnrichedFunctor V I V)

/-- Contract an actual left nested integrand with its original supplied point in the inner Hom. -/
theorem left_contractWord_point (m : I) (p a : I × I) (f : (a.1 ⊗ a.2) ⟶ p.1) :
    ((p.1 ⊗ p.2) ⟶[V] m) ◁
        (pointInsert (eHomEquiv V f) (F.obj a.1 ⊗ G.obj a.2) ▷ H.obj p.2) ≫
          AssociatorFlattening.contractWord d F G H m p a =
      eHomWhiskerRight V (f ▷ p.2) m ⊗ₘ 𝟙 ((F.obj a.1 ⊗ G.obj a.2) ⊗ H.obj p.2) := by
  let W : V := (p.1 ⊗ p.2) ⟶[V] m
  let R : V := (a.1 ⊗ a.2) ⟶[V] p.1
  let A := F.obj a.1 ⊗ G.obj a.2
  let B := H.obj p.2
  let k : W ⊗ R ⟶ (((a.1 ⊗ a.2) ⊗ p.2) ⟶[V] m) :=
    AssociatorFlattening.sliceBase d m p a
  change W ◁ (pointInsert (eHomEquiv V f) A ▷ B) ≫
    W ◁ (α_ R A B).hom ≫ (α_ W R (A ⊗ B)).inv ≫ (k ⊗ₘ 𝟙 (A ⊗ B)) = _
  rw [← whiskerLeft_comp_assoc, pointInsert_tensor, pointInsert_weight]
  have hk : (ρ_ W).inv ≫ (𝟙 W ⊗ₘ eHomEquiv V f) ≫ k = eHomWhiskerRight V (f ▷ p.2) m :=
    left_sliceBase_point d m p a f
  exact congrArg (fun z => z ⊗ₘ 𝟙 (A ⊗ B)) hk

/-- Contract the actual right nested integrand with its original point and ordered coefficients. -/
theorem right_contractWord_point (m : I) (p a : I × I) (f : (a.1 ⊗ a.2) ⟶ p.2) :
    ((p.1 ⊗ p.2) ⟶[V] m) ◁
        (F.obj p.1 ◁ pointInsert (eHomEquiv V f) (G.obj a.1 ⊗ H.obj a.2)) ≫
          AssociatorRightFlattening.contractWord d F G H m p a =
      eHomWhiskerRight V (p.1 ◁ f) m ⊗ₘ 𝟙 (F.obj p.1 ⊗ (G.obj a.1 ⊗ H.obj a.2)) := by
  let W : V := (p.1 ⊗ p.2) ⟶[V] m
  let R : V := (a.1 ⊗ a.2) ⟶[V] p.2
  let B := F.obj p.1
  let A := G.obj a.1 ⊗ H.obj a.2
  let k : W ⊗ R ⟶ ((p.1 ⊗ (a.1 ⊗ a.2)) ⟶[V] m) :=
    AssociatorRightFlattening.sliceBase d m p a
  change W ◁ (B ◁ pointInsert (eHomEquiv V f) A) ≫
    W ◁ (AssociatorRightContraction.frontHomIso R B A).hom ≫
      (α_ W R (B ⊗ A)).inv ≫ (k ⊗ₘ 𝟙 (B ⊗ A)) = _
  rw [← whiskerLeft_comp_assoc, pointInsert_front, pointInsert_weight]
  have hk : (ρ_ W).inv ≫ (𝟙 W ⊗ₘ eHomEquiv V f) ≫ k = eHomWhiskerRight V (p.1 ◁ f) m :=
    right_sliceBase_point d m p a f
  exact congrArg (fun z => z ⊗ₘ 𝟙 (B ⊗ A)) hk

end IndexPoints

/-- The actual inverse right-unit coefficient insertion. -/
abbrev rightPointInsert {R : V} (q : 𝟙_ V ⟶ R) (A : V) : A ⟶ A ⊗ R :=
  (ρ_ A).inv ≫ (𝟙 A ⊗ₘ q)

/-- The coefficient associator takes the right unit insertion to the left unit insertion. -/
@[reassoc]
theorem unitInsertion_associator {R : V} (q : 𝟙_ V ⟶ R) (A B : V) :
    rightPointInsert q A ▷ B ≫ (α_ A R B).hom = A ◁ pointInsert q B := by
  simp only [rightPointInsert, pointInsert, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc, id_tensorHom, tensorHom_id]
  rw [associator_naturality_middle]
  monoidal

section PairFamilies

variable [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)

attribute [local instance] Enriched.prodCategory

/-- The original enriched covariant representable at the original index unit. -/
abbrev unit : EnrichedFunctor V I V := GradedYoneda.representable (V := V) (𝟙_ I)

variable
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
    d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]

section LeftPointGenerators

variable (F G H : EnrichedFunctor V I V) (m : I)
  [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]

/-- The original left nested generator with its supplied index point is the corresponding flat
  generator. -/
theorem left_point_generator (p a : I × I) (f : (a.1 ⊗ a.2) ⟶ p.1) :
    ((p.1 ⊗ p.2) ⟶[V] m) ◁
        (pointInsert (eHomEquiv V f) (F.obj a.1 ⊗ G.obj a.2) ▷ H.obj p.2) ≫
      AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p
        a =
    (eHomWhiskerRight V (f ▷ p.2) m ⊗ₘ 𝟙 ((F.obj a.1 ⊗ G.obj a.2) ⊗ H.obj p.2)) ≫
      AssociatorFlat.leftGenerator d F G H m (a, p.2) ≫ AssociatorFlattening.flatToNested d F G H m
        := by
  let W : V := (p.1 ⊗ p.2) ⟶[V] m
  let A := F.obj a.1 ⊗ G.obj a.2
  let B := H.obj p.2
  let D := AssociatorFaces.Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p a
  let DL := AssociatorFlat.leftObjects d F G H m (a, p.2)
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let P := AssociatorFlat.leftPoint d F G H m
  let b : W ⊗ (A ⊗ B) ⟶ D := W ◁ (pointInsert (eHomEquiv V f) A ▷ B)
  let c : D ⟶ DL := AssociatorFlattening.contractWord d F G H m p a
  let g : DL ⟶ P := AssociatorFlat.leftGenerator d F G H m (a, p.2)
  let l : P ⟶ N := AssociatorFlattening.flatToNested d F G H m
  let n : D ⟶ N := AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m p a
  let k : W ⊗ (A ⊗ B) ⟶ DL := eHomWhiskerRight V (f ▷ p.2) m ⊗ₘ 𝟙 (A ⊗ B)
  have hf : c ≫ g ≫ l = n := AssociatorFlattening.contractWord_generator_factorization d F G H m p a
  have hp : b ≫ c = k := left_contractWord_point d F G H m p a f
  have h₀ := congrArg (fun z => b ≫ z) hf
  have h₁ := congrArg (fun z => z ≫ g ≫ l) hp
  simp only [Category.assoc] at h₀ h₁
  change b ≫ n = k ≫ g ≫ l
  exact h₀.symm.trans h₁

end LeftPointGenerators

section RightPointGenerators

variable (F G H : EnrichedFunctor V I V) (m : I)
  [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]

/-- The original right nested generator with its supplied index point keeps the right flat
  coefficient word. -/
theorem right_point_generator (p a : I × I) (f : (a.1 ⊗ a.2) ⟶ p.2) :
    ((p.1 ⊗ p.2) ⟶[V] m) ◁
        (F.obj p.1 ◁ pointInsert (eHomEquiv V f) (G.obj a.1 ⊗ H.obj a.2)) ≫
      AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
        p a =
    (eHomWhiskerRight V (p.1 ◁ f) m ⊗ₘ 𝟙 (F.obj p.1 ⊗ (G.obj a.1 ⊗ H.obj a.2))) ≫
      AssociatorFlat.rightGenerator d F G H m ((p.1, a.1), a.2) ≫
        AssociatorRightFlattening.flatToNested d F G H m := by
  let W : V := (p.1 ⊗ p.2) ⟶[V] m
  let A := G.obj a.1 ⊗ H.obj a.2
  let B := F.obj p.1
  let D := AssociatorFaces.Right.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p a
  let DR := AssociatorFlat.rightObjects d F G H m ((p.1, a.1), a.2)
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
    H) m
  let P := AssociatorFlat.rightPoint d F G H m
  let b : W ⊗ (B ⊗ A) ⟶ D := W ◁ (B ◁ pointInsert (eHomEquiv V f) A)
  let c : D ⟶ DR := AssociatorRightFlattening.contractWord d F G H m p a
  let g : DR ⟶ P := AssociatorFlat.rightGenerator d F G H m ((p.1, a.1), a.2)
  let r : P ⟶ N := AssociatorRightFlattening.flatToNested d F G H m
  let n : D ⟶ N := AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m p a
  let k : W ⊗ (B ⊗ A) ⟶ DR := eHomWhiskerRight V (p.1 ◁ f) m ⊗ₘ 𝟙 (B ⊗ A)
  have hf : c ≫ g ≫ r = n := AssociatorRightFlattening.contractWord_generator_factorization d F G H
    m p a
  have hp : b ≫ c = k := right_contractWord_point d F G H m p a f
  have h₀ := congrArg (fun z => b ≫ z) hf
  have h₁ := congrArg (fun z => z ≫ g ≫ r) hp
  simp only [Category.assoc] at h₀ h₁
  change b ≫ n = k ≫ g ≫ r
  exact h₀.symm.trans h₁

end RightPointGenerators

/-- The original right unitor inverse is its original coefficient insertion followed by its point
  generator. -/
theorem rightInvComponent_point (F : EnrichedFunctor V I V) (a : I) :
    Unitors.rightInvComponent d F a =
      rightPointInsert (eId V (𝟙_ I)) (F.obj a) ≫
        pointInsert (eHomEquiv V (ρ_ a).hom) (F.obj a ⊗ (unit (V := V) (I := I)).obj (𝟙_ I)) ≫
          EnrichedDayKernel.gen d.tensorEnrichedFunctor F (unit (V := V) (I := I)) a (a, 𝟙_ I) := by
  let A := F.obj a
  let R : V := 𝟙_ I ⟶[V] 𝟙_ I
  let s : A ⟶ A ⊗ R := rightPointInsert (eId V (𝟙_ I)) A
  let q : 𝟙_ V ⟶ ((a ⊗ 𝟙_ I) ⟶[V] a) := eHomEquiv V (ρ_ a).hom
  let g : ((a ⊗ 𝟙_ I) ⟶[V] a) ⊗ (A ⊗ R) ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor F (unit (V := V) (I := I)) a :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (unit (V := V) (I := I)) a (a, 𝟙_ I)
  change (λ_ A).inv ≫ (q ⊗ₘ s) ≫ g = s ≫ ((λ_ (A ⊗ R)).inv ≫ (q ⊗ₘ 𝟙 (A ⊗ R))) ≫ g
  simpa only [tensorHom_id, Category.assoc] using
    congrArg (fun z => z ≫ g) (leftUnitor_inv_comp_tensorHom q s)

/-- The original left unitor inverse retains the supplied unit identity and original endpoint point.
-/
theorem leftInvComponent_point (G : EnrichedFunctor V I V) (k : I) :
    Unitors.leftInvComponent d G k =
      pointInsert (eId V (𝟙_ I)) (G.obj k) ≫
        pointInsert (eHomEquiv V (λ_ k).hom) ((unit (V := V) (I := I)).obj (𝟙_ I) ⊗ G.obj k) ≫
          EnrichedDayKernel.gen d.tensorEnrichedFunctor (unit (V := V) (I := I)) G k (𝟙_ I, k) := by
  let B := G.obj k
  let R : V := 𝟙_ I ⟶[V] 𝟙_ I
  let s : B ⟶ R ⊗ B := pointInsert (eId V (𝟙_ I)) B
  let q : 𝟙_ V ⟶ ((𝟙_ I ⊗ k) ⟶[V] k) := eHomEquiv V (λ_ k).hom
  let g : ((𝟙_ I ⊗ k) ⟶[V] k) ⊗ (R ⊗ B) ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor (unit (V := V) (I := I)) G k :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (unit (V := V) (I := I)) G k (𝟙_ I, k)
  change (λ_ B).inv ≫ (q ⊗ₘ s) ≫ g = s ≫ ((λ_ (R ⊗ B)).inv ≫ (q ⊗ₘ 𝟙 (R ⊗ B))) ≫ g
  simpa only [tensorHom_id, Category.assoc] using
    congrArg (fun z => z ≫ g) (leftUnitor_inv_comp_tensorHom q s)

section UnitSeeds

variable (F G : EnrichedFunctor V I V) (m : I)
  [HasCoproduct (AssociatorFlat.leftObjects d F (unit (V := V) (I := I)) G m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F (unit (V := V) (I := I)) G m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F (unit (V := V) (I := I)) G m)
    (AssociatorFlat.leftMap1 d F (unit (V := V) (I := I)) G m)]
  [HasCoproduct (AssociatorFlat.rightObjects d F (unit (V := V) (I := I)) G m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F (unit (V := V) (I := I)) G m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F (unit (V := V) (I := I)) G m)
    (AssociatorFlat.rightMap1 d F (unit (V := V) (I := I)) G m)]

/-- The original right unit inverse gives this literal seed of the left flat triple. -/
abbrev leftFlatUnitSeed (a k : I) : EnrichedDayKernel.objects d.tensorEnrichedFunctor F G m (a, k) ⟶
    AssociatorFlat.leftPoint d F (unit (V := V) (I := I)) G m :=
  (eHomWhiskerRight V ((ρ_ a).hom ▷ k) m ⊗ₘ
    (rightPointInsert (eId V (𝟙_ I)) (F.obj a) ▷ G.obj k)) ≫
      AssociatorFlat.leftGenerator d F (unit (V := V) (I := I)) G m ((a, 𝟙_ I), k)

/-- The original left unit inverse gives the literal seed of the right flat triple. -/
abbrev rightFlatUnitSeed (a k : I) : EnrichedDayKernel.objects d.tensorEnrichedFunctor F G m (a, k)
  ⟶
    AssociatorFlat.rightPoint d F (unit (V := V) (I := I)) G m :=
  (eHomWhiskerRight V (a ◁ (λ_ k).hom) m ⊗ₘ
    (F.obj a ◁ pointInsert (eId V (𝟙_ I)) (G.obj k))) ≫
      AssociatorFlat.rightGenerator d F (unit (V := V) (I := I)) G m ((a, 𝟙_ I), k)

omit
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
    d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)] in
/-- The original index and coefficient triangles identify the actual flat unit seeds. -/
theorem unitSeed_flat_associator (a k : I) :
    leftFlatUnitSeed d F G m a k ≫ (AssociatorFlat.iso d F (unit (V := V) (I := I)) G m).hom =
      rightFlatUnitSeed d F G m a k := by
  let U := unit (V := V) (I := I)
  let X : (I × I) × I := ((a, 𝟙_ I), k)
  let W : V := (a ⊗ k) ⟶[V] m
  let WL : V := ((a ⊗ 𝟙_ I) ⊗ k) ⟶[V] m
  let WR : V := (a ⊗ (𝟙_ I ⊗ k)) ⟶[V] m
  let A := F.obj a
  let B := G.obj k
  let R : V := 𝟙_ I ⟶[V] 𝟙_ I
  let wl : W ⟶ WL := eHomWhiskerRight V ((ρ_ a).hom ▷ k) m
  let wr : W ⟶ WR := eHomWhiskerRight V (a ◁ (λ_ k).hom) m
  let wi : WL ⟶ WR := eHomWhiskerRight V (α_ a (𝟙_ I) k).inv m
  let cl : A ⊗ B ⟶ (A ⊗ R) ⊗ B := rightPointInsert (eId V (𝟙_ I)) A ▷ B
  let cr : A ⊗ B ⟶ A ⊗ (R ⊗ B) := A ◁ pointInsert (eId V (𝟙_ I)) B
  let ca : (A ⊗ R) ⊗ B ⟶ A ⊗ (R ⊗ B) := (α_ A R B).hom
  let L := AssociatorFlat.leftPoint d F U G m
  let P := AssociatorFlat.rightPoint d F U G m
  let gl : WL ⊗ ((A ⊗ R) ⊗ B) ⟶ L := AssociatorFlat.leftGenerator d F U G m X
  let gr : WR ⊗ (A ⊗ (R ⊗ B)) ⟶ P := AssociatorFlat.rightGenerator d F U G m X
  let f : L ⟶ P := (AssociatorFlat.iso d F U G m).hom
  have hg : gl ≫ f = (wi ⊗ₘ ca) ≫ gr := AssociatorFlat.leftGenerator_iso_hom d F U G m X
  have hw : wl ≫ wi = wr := by
    change eHomWhiskerRight V ((ρ_ a).hom ▷ k) m ≫
      eHomWhiskerRight V (α_ a (𝟙_ I) k).inv m = eHomWhiskerRight V (a ◁ (λ_ k).hom) m
    rw [← eHomWhiskerRight_comp]
    have ht : (α_ a (𝟙_ I) k).inv ≫ ((ρ_ a).hom ▷ k) = a ◁ (λ_ k).hom := by
      rw [← MonoidalCategory.triangle a k]
      simp only [Iso.inv_hom_id_assoc]
    exact congrArg (fun z => eHomWhiskerRight V z m) ht
  have hc : cl ≫ ca = cr := unitInsertion_associator (eId V (𝟙_ I)) A B
  change ((wl ⊗ₘ cl) ≫ gl) ≫ f = (wr ⊗ₘ cr) ≫ gr
  rw [Category.assoc, hg, ← Category.assoc, tensorHom_comp_tensorHom, hw, hc]

omit
  [HasCoproduct (AssociatorFlat.rightObjects d F (unit (V := V) (I := I)) G m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F (unit (V := V) (I := I)) G m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F (unit (V := V) (I := I)) G m)
    (AssociatorFlat.rightMap1 d F (unit (V := V) (I := I)) G m)] in
/-- Every original F⋆G generator enters the left flat unit seed through the actual right unitor
  inverse. -/
theorem leftFlatUnitSeed_flatToNested (a k : I) :
    leftFlatUnitSeed d F G m a k ≫
        AssociatorFlattening.flatToNested d F (unit (V := V) (I := I)) G m =
      EnrichedDayKernel.gen d.tensorEnrichedFunctor F G m (a, k) ≫
        Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorInv d F)
          (GradedNatTrans.unitId G) m := by
  let U := unit (V := V) (I := I)
  let W : V := (a ⊗ k) ⟶[V] m
  let A := F.obj a
  let B := G.obj k
  let R : V := (a ⊗ 𝟙_ I) ⟶[V] a
  let Q := A ⊗ U.obj (𝟙_ I)
  let s : A ⟶ Q := rightPointInsert (eId V (𝟙_ I)) A
  let q : 𝟙_ V ⟶ R := eHomEquiv V (ρ_ a).hom
  let w : W ⟶ (((a ⊗ 𝟙_ I) ⊗ k) ⟶[V] m) := eHomWhiskerRight V ((ρ_ a).hom ▷ k) m
  let P := AssociatorFlat.leftPoint d F U G m
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    U) G m
  let Y := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G m
  let inner : R ⊗ Q ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor F U a :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F U a (a, 𝟙_ I)
  let outer : W ⊗ (EnrichedDayKernel.obj d.tensorEnrichedFunctor F U a ⊗ B) ⟶ N :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F U) G m
      (a, k)
  let n : W ⊗ ((R ⊗ Q) ⊗ B) ⟶ N := W ◁ (inner ▷ B) ≫ outer
  let pre : W ⊗ (Q ⊗ B) ⟶ W ⊗ ((R ⊗ Q) ⊗ B) := W ◁ (pointInsert q Q ▷ B)
  let coef : W ⊗ (A ⊗ B) ⟶ W ⊗ (Q ⊗ B) := W ◁ (s ▷ B)
  let g : W ⊗ (A ⊗ B) ⟶ Y := EnrichedDayKernel.gen d.tensorEnrichedFunctor F G m (a, k)
  let i : Y ⟶ N := Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorInv d F)
    (GradedNatTrans.unitId G) m
  let gl : (((a ⊗ 𝟙_ I) ⊗ k) ⟶[V] m) ⊗ (Q ⊗ B) ⟶ P :=
    AssociatorFlat.leftGenerator d F U G m ((a, 𝟙_ I), k)
  let l : P ⟶ N := AssociatorFlattening.flatToNested d F U G m
  have hpoint : pre ≫ n = (w ⊗ₘ 𝟙 (Q ⊗ B)) ≫ gl ≫ l :=
    left_point_generator d F U G m (a, k) (a, 𝟙_ I) (ρ_ a).hom
  have hinv : Unitors.rightInvComponent d F a = s ≫ pointInsert q Q ≫ inner :=
    rightInvComponent_point d F a
  have hmap : g ≫ i = W ◁ (Unitors.rightInvComponent d F a ▷ B) ≫ outer := by
    have h : g ≫ i = (𝟙 W ⊗ₘ
        ((eHomEquiv V).symm ((Unitors.rightUnitorInv d F).app a) ⊗ₘ
          (eHomEquiv V).symm ((GradedNatTrans.unitId G).app k))) ≫ outer :=
      Input.gen_mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorInv d F)
        (GradedNatTrans.unitId G) m (a, k)
    rw [Unitors.rightUnitorInv_component, GradedNatTrans.unitId_component] at h
    exact h.trans (by rw [id_tensorHom, tensorHom_id])
  have hn : coef ≫ pre ≫ n = g ≫ i := by
    rw [hmap, hinv]
    simp only [coef, pre, n, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  have ht : coef ≫ (w ⊗ₘ 𝟙 (Q ⊗ B)) = w ⊗ₘ (s ▷ B) := by
    simp only [coef, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have h₀ := congrArg (fun z => coef ≫ z) hpoint
  have h₁ := congrArg (fun z => z ≫ gl ≫ l) ht
  simp only [Category.assoc] at h₀ h₁
  change ((w ⊗ₘ (s ▷ B)) ≫ gl) ≫ l = g ≫ i
  simpa only [Category.assoc] using (h₀.trans h₁).symm.trans hn

omit
  [HasCoproduct (AssociatorFlat.leftObjects d F (unit (V := V) (I := I)) G m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F (unit (V := V) (I := I)) G m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F (unit (V := V) (I := I)) G m)
    (AssociatorFlat.leftMap1 d F (unit (V := V) (I := I)) G m)] in
/-- Every original F⋆G generator gives the original right flat unit seed through the actual left
  inverse. -/
theorem rightFlatUnitSeed_flatToNested (a k : I) :
    rightFlatUnitSeed d F G m a k ≫
        AssociatorRightFlattening.flatToNested d F (unit (V := V) (I := I)) G m =
      EnrichedDayKernel.gen d.tensorEnrichedFunctor F G m (a, k) ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
          (Unitors.leftUnitorInv d G) m := by
  let U := unit (V := V) (I := I)
  let W : V := (a ⊗ k) ⟶[V] m
  let A := F.obj a
  let B := G.obj k
  let R : V := (𝟙_ I ⊗ k) ⟶[V] k
  let Q := U.obj (𝟙_ I) ⊗ B
  let s : B ⟶ Q := pointInsert (eId V (𝟙_ I)) B
  let q : 𝟙_ V ⟶ R := eHomEquiv V (λ_ k).hom
  let w : W ⟶ ((a ⊗ (𝟙_ I ⊗ k)) ⟶[V] m) := eHomWhiskerRight V (a ◁ (λ_ k).hom) m
  let P := AssociatorFlat.rightPoint d F U G m
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor U
    G) m
  let Y := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G m
  let inner : R ⊗ Q ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor U G k :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor U G k (𝟙_ I, k)
  let outer : W ⊗ (A ⊗ EnrichedDayKernel.obj d.tensorEnrichedFunctor U G k) ⟶ N :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor U G) m
      (a, k)
  let n : W ⊗ (A ⊗ (R ⊗ Q)) ⟶ N := W ◁ (A ◁ inner) ≫ outer
  let pre : W ⊗ (A ⊗ Q) ⟶ W ⊗ (A ⊗ (R ⊗ Q)) := W ◁ (A ◁ pointInsert q Q)
  let coef : W ⊗ (A ⊗ B) ⟶ W ⊗ (A ⊗ Q) := W ◁ (A ◁ s)
  let g : W ⊗ (A ⊗ B) ⟶ Y := EnrichedDayKernel.gen d.tensorEnrichedFunctor F G m (a, k)
  let i : Y ⟶ N := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (Unitors.leftUnitorInv d G) m
  let gr : ((a ⊗ (𝟙_ I ⊗ k)) ⟶[V] m) ⊗ (A ⊗ Q) ⟶ P :=
    AssociatorFlat.rightGenerator d F U G m ((a, 𝟙_ I), k)
  let r : P ⟶ N := AssociatorRightFlattening.flatToNested d F U G m
  have hpoint : pre ≫ n = (w ⊗ₘ 𝟙 (A ⊗ Q)) ≫ gr ≫ r :=
    right_point_generator d F U G m (a, k) (𝟙_ I, k) (λ_ k).hom
  have hinv : Unitors.leftInvComponent d G k = s ≫ pointInsert q Q ≫ inner :=
    leftInvComponent_point d G k
  have hmap : g ≫ i = W ◁ (A ◁ Unitors.leftInvComponent d G k) ≫ outer := by
    have h : g ≫ i = (𝟙 W ⊗ₘ
        ((eHomEquiv V).symm ((GradedNatTrans.unitId F).app a) ⊗ₘ
          (eHomEquiv V).symm ((Unitors.leftUnitorInv d G).app k))) ≫ outer :=
      Input.gen_mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
        (Unitors.leftUnitorInv d G) m (a, k)
    rw [Unitors.leftUnitorInv_component, GradedNatTrans.unitId_component] at h
    exact h.trans (by rw [id_tensorHom, id_tensorHom])
  have hn : coef ≫ pre ≫ n = g ≫ i := by
    rw [hmap, hinv]
    simp only [coef, pre, n, whiskerLeft_comp, Category.assoc]
  have ht : coef ≫ (w ⊗ₘ 𝟙 (A ⊗ Q)) = w ⊗ₘ (A ◁ s) := by
    simp only [coef, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have h₀ := congrArg (fun z => coef ≫ z) hpoint
  have h₁ := congrArg (fun z => z ≫ gr ≫ r) ht
  simp only [Category.assoc] at h₀ h₁
  change ((w ⊗ₘ (A ◁ s)) ≫ gr) ≫ r = g ≫ i
  simpa only [Category.assoc] using (h₀.trans h₁).symm.trans hn

end UnitSeeds

/-- The actual right unitor and its inverse remain inverse after applying the unchanged Day
  bifunctor. -/
theorem rightUnitor_tensor_hom_inv_id (F G : EnrichedFunctor V I V) (m : I) :
    Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorHom d F) (GradedNatTrans.unitId G) m ≫
      Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorInv d F) (GradedNatTrans.unitId G) m =
        𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor
          (Output.functor d.tensorEnrichedFunctor F (unit (V := V) (I := I))) G m) := by
  have hc : GradedNatTrans.unitComp (Unitors.rightUnitorHom d F) (Unitors.rightUnitorInv d F) =
      GradedNatTrans.unitId (Output.functor d.tensorEnrichedFunctor F (unit (V := V) (I := I))) :=
    (Unitors.rightUnitor d F).hom_inv_id
  have hg : GradedNatTrans.unitComp (GradedNatTrans.unitId G) (GradedNatTrans.unitId G) =
      GradedNatTrans.unitId G := Category.id_comp (𝟙 (⟨G⟩ : EnrichedFunctorCat V I))
  have h := Input.mapAt_comp d.tensorEnrichedFunctor (Unitors.rightUnitorHom d F)
    (Unitors.rightUnitorInv d F) (GradedNatTrans.unitId G) (GradedNatTrans.unitId G) m
  rw [hc, hg, Input.mapAt_id] at h
  exact h.symm

/-- The original left inverse and unitor remain inverse on the actual right Day input. -/
theorem leftUnitor_tensor_inv_hom_id (F G : EnrichedFunctor V I V) (m : I) :
    Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F) (Unitors.leftUnitorInv d G) m ≫
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F) (Unitors.leftUnitorHom d G) m =
        𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor F G m) := by
  have hc : GradedNatTrans.unitComp (Unitors.leftUnitorInv d G) (Unitors.leftUnitorHom d G) =
      GradedNatTrans.unitId G := (Unitors.leftUnitor d G).inv_hom_id
  have hf : GradedNatTrans.unitComp (GradedNatTrans.unitId F) (GradedNatTrans.unitId F) =
      GradedNatTrans.unitId F := Category.id_comp (𝟙 (⟨F⟩ : EnrichedFunctorCat V I))
  have h := Input.mapAt_comp d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (GradedNatTrans.unitId F) (Unitors.leftUnitorInv d G) (Unitors.leftUnitorHom d G) m
  rw [hc, hf, Input.mapAt_id] at h
  exact h.symm

section WholeCoherence

variable
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer (AssociatorFlat.leftMap0 d F G H m)
    (AssociatorFlat.leftMap1 d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.simultaneousObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor
    F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.simultaneousRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Left.simultaneousLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      F G H m)
    (AssociatorPresentation.Left.simultaneousRightMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Left.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)
    (AssociatorFaces.Left.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
      H m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Left.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
      H m pq)
    (AssociatorPresentation.Left.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorPresentation.Left.innerObjects
    d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.outerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
    H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Left.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
      m)
    (AssociatorPresentation.Left.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
      m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.rightRelations d F G H
    m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer (AssociatorFlat.rightMap0 d F G H m)
    (AssociatorFlat.rightMap1 d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Right.simultaneousObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Right.simultaneousRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Right.simultaneousLeftMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m)
    (AssociatorPresentation.Right.simultaneousRightMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Right.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Right.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
    p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Right.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)
    (AssociatorFaces.Right.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Right.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Right.relationRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      G H F m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Right.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)
    (AssociatorPresentation.Right.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Right.innerObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F
    m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Right.outerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H
    F m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Right.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F
      m)
    (AssociatorPresentation.Right.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H
      F m)]


/-- The actual associator identifies both original unit inverse maps on every F⋆G generator. -/
theorem inverse_unit_associator (F G : EnrichedFunctor V I V) (m : I) :
    Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorInv d F) (GradedNatTrans.unitId G) m ≫
        (AssociatorConstruction.componentIso d F (unit (V := V) (I := I)) G m).hom =
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F) (Unitors.leftUnitorInv d G) m :=
        by
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor F G m
  rintro ⟨a, k⟩
  let U := unit (V := V) (I := I)
  let D := EnrichedDayKernel.objects d.tensorEnrichedFunctor F G m (a, k)
  let Y := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G m
  let L := AssociatorFlat.leftPoint d F U G m
  let R := AssociatorFlat.rightPoint d F U G m
  let NL := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    U) G m
  let NR := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
    U G) m
  let g : D ⟶ Y := EnrichedDayKernel.gen d.tensorEnrichedFunctor F G m (a, k)
  let sL : D ⟶ L := leftFlatUnitSeed d F G m a k
  let sR : D ⟶ R := rightFlatUnitSeed d F G m a k
  let l : L ⟶ NL := AssociatorFlattening.flatToNested d F U G m
  let li : NL ⟶ L := AssociatorFlattening.nestedToFlat d F U G m
  let r : R ⟶ NR := AssociatorRightFlattening.flatToNested d F U G m
  let e : L ⟶ R := (AssociatorFlat.iso d F U G m).hom
  let h : NL ⟶ NR := (AssociatorConstruction.componentIso d F U G m).hom
  let iR : Y ⟶ NL := Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorInv d F)
    (GradedNatTrans.unitId G) m
  let iL : Y ⟶ NR := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (Unitors.leftUnitorInv d G) m
  have hl : sL ≫ l = g ≫ iR := leftFlatUnitSeed_flatToNested d F G m a k
  have hr : sR ≫ r = g ≫ iL := rightFlatUnitSeed_flatToNested d F G m a k
  have he : sL ≫ e = sR := unitSeed_flat_associator d F G m a k
  have hcomp : h = li ≫ e ≫ r := AssociatorConstruction.componentIso_hom d F U G m
  have hi : l ≫ li = 𝟙 L := AssociatorFlattening.flatToNested_nestedToFlat d F U G m
  have ha : l ≫ h = e ≫ r := by
    rw [hcomp]
    have ht := congrArg (fun z => z ≫ e ≫ r) hi
    simpa only [Category.assoc, Category.id_comp] using ht
  change g ≫ (iR ≫ h) = g ≫ iL
  calc
    _ = (sL ≫ l) ≫ h := by rw [hl, Category.assoc]
    _ = sL ≫ e ≫ r := by rw [Category.assoc, ha]
    _ = sR ≫ r := by rw [← Category.assoc, he]
    _ = _ := hr

/-- Triangle coherence for the original chosen Day values and original genuine unit transformations.
-/
theorem triangle_component (F G : EnrichedFunctor V I V) (m : I) :
    (AssociatorConstruction.componentIso d F (unit (V := V) (I := I)) G m).hom ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F) (Unitors.leftUnitorHom d G) m
          =
      Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorHom d F) (GradedNatTrans.unitId G) m
        := by
  let U := unit (V := V) (I := I)
  let Y := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G m
  let L := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    U) G m
  let R := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor U
    G) m
  let a : L ⟶ R := (AssociatorConstruction.componentIso d F U G m).hom
  let hR : L ⟶ Y := Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorHom d F)
    (GradedNatTrans.unitId G) m
  let iR : Y ⟶ L := Input.mapAt d.tensorEnrichedFunctor (Unitors.rightUnitorInv d F)
    (GradedNatTrans.unitId G) m
  let hL : R ⟶ Y := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (Unitors.leftUnitorHom d G) m
  let iL : Y ⟶ R := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (Unitors.leftUnitorInv d G) m
  have hr : hR ≫ iR = 𝟙 L := rightUnitor_tensor_hom_inv_id d F G m
  have hl : iL ≫ hL = 𝟙 Y := leftUnitor_tensor_inv_hom_id d F G m
  have ha : iR ≫ a = iL := inverse_unit_associator d F G m
  change a ≫ hL = hR
  calc
    _ = (hR ≫ iR) ≫ a ≫ hL := by rw [hr, Category.id_comp]
    _ = hR ≫ iL ≫ hL := by
      simpa only [Category.assoc] using congrArg (fun z => hR ≫ z ≫ hL) ha
    _ = _ := by rw [hl, Category.comp_id]

/-- The actual natural associator and original unitors satisfy triangle on the SAME Day bifunctor.
-/
theorem triangle (F G : EnrichedFunctorCat V I) :
    (AssociatorConstruction.associator d).hom.app ((F, ⟨unit (V := V) (I := I)⟩), G) ≫
        (Input.bifunctor d.tensorEnrichedFunctor).map
          (X := (F, ⟨Output.functor d.tensorEnrichedFunctor (unit (V := V) (I := I))
            G.toEnrichedFunctor⟩))
          (Y := (F, G)) (𝟙 F, (Unitors.leftUnitor d G.toEnrichedFunctor).hom) =
      (Input.bifunctor d.tensorEnrichedFunctor).map
        (X := (⟨Output.functor d.tensorEnrichedFunctor F.toEnrichedFunctor (unit (V := V) (I :=
          I))⟩, G))
        (Y := (F, G)) ((Unitors.rightUnitor d F.toEnrichedFunctor).hom, 𝟙 G) := by
  apply EnrichedFunctorCat.hom_ext
  intro m
  rw [EnrichedFunctorCat.component_comp, AssociatorConstruction.associator_hom_component,
    Input.bifunctor_map_component, Input.bifunctor_map_component]
  exact triangle_component d F.toEnrichedFunctor G.toEnrichedFunctor m

end WholeCoherence

end PairFamilies
end CategoryTheory.EnrichedDayKernel.AssociatorTriangle
