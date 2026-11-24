/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Evaluation
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Free genuine enriched functors

The free object at a with coefficient X has object X tensor Hom(a,b).
All actions and unit-graded maps retain the full original enriched Hom objects.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uA uV vV

namespace CategoryTheory.EnrichedFunctorCat.Free

open MonoidalCategory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- The full right-oriented free action, with the original enriched composition. -/
def action (a : A) (X : V) (b c : A) :
    (X ⊗ (a ⟶[V] b)) ⊗ (b ⟶[V] c) ⟶ X ⊗ (a ⟶[V] c) :=
  (α_ X (a ⟶[V] b) (b ⟶[V] c)).hom ≫ X ◁ eComp V a b c

omit [BraidedCategory V] [MonoidalClosed V] in
/-- The free action preserves the actual enriched identity. -/
theorem action_id (a : A) (X : V) (b : A) :
    ((X ⊗ (a ⟶[V] b)) ◁ eId V b) ≫ action a X b b =
      (ρ_ (X ⊗ (a ⟶[V] b))).hom := by
  let H := a ⟶[V] b
  have hUnit : H ◁ eId V b ≫ eComp V a b b = (ρ_ H).hom := by
    apply (cancel_epi (ρ_ H).inv).1
    simpa only [H, Category.assoc, Iso.inv_hom_id] using e_comp_id V a b
  dsimp only [action]
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp, hUnit]
  exact (rightUnitor_tensor_hom X H).symm

omit [BraidedCategory V] [MonoidalClosed V] in
/-- The entire enriched Hom action satisfies source-first associativity. -/
theorem action_comp (a : A) (X : V) (b c d : A) :
    ((X ⊗ (a ⟶[V] b)) ◁ eComp V b c d) ≫ action a X b d =
      (α_ (X ⊗ (a ⟶[V] b)) (b ⟶[V] c) (c ⟶[V] d)).inv ≫
        (action a X b c ▷ (c ⟶[V] d)) ≫ action a X c d := by
  let P := a ⟶[V] b
  let Q := b ⟶[V] c
  let R := c ⟶[V] d
  let T := a ⟶[V] c
  have hComp : P ◁ eComp V b c d ≫ eComp V a b d =
      (α_ P Q R).inv ≫ (eComp V a b c ▷ R) ≫ eComp V a c d :=
    (e_assoc V a b c d).symm
  dsimp only [action]
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp, hComp]
  simp only [whiskerLeft_comp]
  rw [← pentagon_inv_hom_hom_hom_inv_assoc]
  rw [← associator_naturality_middle_assoc]
  simp only [comp_whiskerRight, Category.assoc]

/-- The free enriched functor with the original tensor coefficient and full Hom action. -/
abbrev object (a : A) (X : V) : EnrichedFunctorCat V A where
  toEnrichedFunctor :=
    { obj := fun b => X ⊗ (a ⟶[V] b)
      map := fun b c => MonoidalClosed.curry (action a X b c)
      map_id := fun b => by
        apply MonoidalClosed.uncurry_injective
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
          MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
          MonoidalClosed.uncurry_curry]
        exact action_id a X b
      map_comp := fun b c d => by
        apply MonoidalClosed.uncurry_injective
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
          MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_curry,
          MonoidalClosed.uncurry_curry]
        exact action_comp a X b c d }

/-- Extend an actual coefficient map using the entire original enriched action. -/
def extensionComponent (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj a) (b : A) :
    X ⊗ (a ⟶[V] b) ⟶ F.toEnrichedFunctor.obj b :=
  (f ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)

omit [BraidedCategory V] in
/-- The extension components satisfy full enriched Hom-object naturality. -/
theorem extensionComponent_natural (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj a) (b c : A) :
    MonoidalClosed.uncurry ((object a X).toEnrichedFunctor.map b c) ≫
        extensionComponent a X F f c =
      (extensionComponent a X F f b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map b c) := by
  let P := a ⟶[V] b
  let Q := b ⟶[V] c
  let H := a ⟶[V] c
  let Y := F.toEnrichedFunctor.obj a
  have hTensor : (X ◁ eComp V a b c) ≫ (f ▷ H) =
      (f ▷ (P ⊗ Q)) ≫ (Y ◁ eComp V a b c) := by
    rw [whisker_exchange]
  have hComp := congrArg MonoidalClosed.uncurry (F.toEnrichedFunctor.map_comp a b c)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eComp] at hComp
  rw [tensorHom_id]
  change MonoidalClosed.uncurry (MonoidalClosed.curry (action a X b c)) ≫
      extensionComponent a X F f c =
    (extensionComponent a X F f b ▷ Q) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map b c)
  rw [MonoidalClosed.uncurry_curry]
  dsimp only [action, extensionComponent]
  rw [tensorHom_id, tensorHom_id]
  simp only [Category.assoc]
  have hTensorPost := congrArg
    (fun q => (α_ X P Q).hom ≫ q ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a c)) hTensor
  have hCompPost := congrArg
    (fun q => (α_ X P Q).hom ≫ (f ▷ (P ⊗ Q)) ≫ q) hComp
  calc
    _ = (α_ X P Q).hom ≫ (f ▷ (P ⊗ Q)) ≫ Y ◁ eComp V a b c ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map a c) := by
      simpa only [P, Q, H, Y, Category.assoc] using hTensorPost
    _ = (α_ X P Q).hom ≫ (f ▷ (P ⊗ Q)) ≫ (α_ Y P Q).inv ≫
        (MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ▷ Q) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map b c) := by
      simpa only [P, Q, Y, Category.assoc] using hCompPost
    _ = _ := by
      rw [← associator_naturality_left_assoc, Iso.hom_inv_id_assoc]
      rw [comp_whiskerRight]
      exact (Category.assoc _ _ _).symm

/-- The supplied coefficient map extends to a genuine unit-graded transformation. -/
def extend (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj a) : object a X ⟶ F :=
  GradedNatTrans.unitOfComponents (extensionComponent a X F f)
    (extensionComponent_natural a X F f)

/-- The extension's actual ordinary components are the specified action maps. -/
@[simp]
theorem extend_component (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj a) (b : A) :
    EnrichedFunctorCat.component (extend a X F f) b = extensionComponent a X F f b :=
  GradedNatTrans.unitOfComponents_component _ _ b

/-- Evaluate a free-functor transformation at the original enriched identity. -/
def evaluate (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (t : object a X ⟶ F) : X ⟶ F.toEnrichedFunctor.obj a :=
  (ρ_ X).inv ≫ (X ◁ eId V a) ≫ EnrichedFunctorCat.component t a

/-- Evaluation of the actual extension recovers the original coefficient map. -/
@[simp]
theorem evaluate_extend (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj a) : evaluate a X F (extend a X F f) = f := by
  let Y := F.toEnrichedFunctor.obj a
  have hId := congrArg MonoidalClosed.uncurry (F.toEnrichedFunctor.map_id a)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at hId
  rw [evaluate, extend_component]
  simp only [extensionComponent, tensorHom_id]
  rw [whisker_exchange_assoc]
  rw [hId]
  exact (whiskerRight_id_symm f).symm

/-- Full Hom naturality reconstructs every ordinary component from identity evaluation. -/
theorem reconstruct_component (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (t : object a X ⟶ F) (b : A) :
    EnrichedFunctorCat.component t b = extensionComponent a X F (evaluate a X F t) b := by
  let H := a ⟶[V] b
  let E := a ⟶[V] a
  let pad : X ⊗ H ⟶ (X ⊗ E) ⊗ H :=
    ((ρ_ X).inv ▷ H) ≫ ((X ◁ eId V a) ▷ H)
  have hPad : pad ≫ action a X a b = 𝟙 (X ⊗ H) := by
    have hLeftUnit := e_id_comp V a b
    have hCanonical : pad ≫ (α_ X E H).hom =
        (X ◁ (λ_ H).inv) ≫ X ◁ (eId V a ▷ H) := by
      dsimp only [pad, E, H]
      monoidal
    rw [action, ← Category.assoc, hCanonical]
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
    have hUnit := congrArg (fun q => X ◁ q) hLeftUnit
    simpa only [H, Category.assoc, whiskerLeft_id] using hUnit
  have hn := t.uncurriedNaturality a b
  rw [MonoidalClosed.uncurry_curry, tensorHom_id] at hn
  change action a X a b ≫ EnrichedFunctorCat.component t b =
    (EnrichedFunctorCat.component t a ▷ H) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) at hn
  have h := congrArg (fun q => pad ≫ q) hn
  rw [← Category.assoc, hPad, Category.id_comp] at h
  dsimp only [extensionComponent, evaluate]
  rw [tensorHom_id]
  change EnrichedFunctorCat.component t b =
    (((ρ_ X).inv ≫ (X ◁ eId V a) ≫ EnrichedFunctorCat.component t a) ▷ H) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)
  simpa only [pad, comp_whiskerRight, Category.assoc] using h

/-- The supplied genuine transformation is recovered by its actual identity evaluation. -/
@[simp]
theorem extend_evaluate (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (t : object a X ⟶ F) : extend a X F (evaluate a X F t) = t := by
  apply EnrichedFunctorCat.hom_ext
  intro b
  rw [extend_component]
  exact (reconstruct_component a X F t b).symm

/-- The full ordinary Hom correspondence, with actual extension and identity evaluation. -/
def homEquiv (a : A) (X : V) (F : EnrichedFunctorCat V A) :
    (object a X ⟶ F) ≃ (X ⟶ F.toEnrichedFunctor.obj a) where
  toFun := evaluate a X F
  invFun := extend a X F
  left_inv := extend_evaluate a X F
  right_inv := evaluate_extend a X F

omit [BraidedCategory V] [MonoidalClosed V] in
/-- Actual tensor coefficient maps satisfy the full free-action naturality equation. -/
theorem coefficientMap_natural (a : A) {X Y : V} (f : X ⟶ Y) (b c : A) :
    action a X b c ≫ (f ▷ (a ⟶[V] c)) =
      ((f ▷ (a ⟶[V] b)) ▷ (b ⟶[V] c)) ≫ action a Y b c := by
  let P := a ⟶[V] b
  let Q := b ⟶[V] c
  calc
    _ = (α_ X P Q).hom ≫ (f ▷ (P ⊗ Q)) ≫ Y ◁ eComp V a b c := by
      dsimp only [action]
      rw [Category.assoc]
      exact congrArg (fun q => (α_ X P Q).hom ≫ q) (whisker_exchange f (eComp V a b c))
    _ = _ := by
      dsimp only [action]
      have hAssoc := congrArg (fun q => q ≫ Y ◁ eComp V a b c)
        (associator_naturality_left f P Q).symm
      simpa only [P, Q, Category.assoc] using hAssoc

/-- Map a coefficient arrow by its original tensor component at every enriched index. -/
def coefficientMap (a : A) {X Y : V} (f : X ⟶ Y) : object a X ⟶ object a Y :=
  GradedNatTrans.unitOfComponents (fun b => f ▷ (a ⟶[V] b)) (fun b c => by
    simpa only [object, MonoidalClosed.uncurry_curry, tensorHom_id] using
      coefficientMap_natural a f b c)

/-- The coefficient map keeps the complete original tensor morphism. -/
@[simp]
theorem coefficientMap_component (a : A) {X Y : V} (f : X ⟶ Y) (b : A) :
    EnrichedFunctorCat.component (coefficientMap a f) b = f ▷ (a ⟶[V] b) :=
  GradedNatTrans.unitOfComponents_component _ _ b

/-- The actual free enriched functor as an ordinary functor of the coefficient. -/
abbrev functor (a : A) : V ⥤ EnrichedFunctorCat V A where
  obj := object a
  map := coefficientMap a
  map_id X := by
    apply EnrichedFunctorCat.hom_ext
    intro b
    rw [coefficientMap_component, EnrichedFunctorCat.component_id, id_whiskerRight]
  map_comp f g := by
    apply EnrichedFunctorCat.hom_ext
    intro b
    rw [coefficientMap_component, EnrichedFunctorCat.component_comp,
      coefficientMap_component, coefficientMap_component, comp_whiskerRight]

/-- Extension respects coefficient precomposition on the complete original tensor maps. -/
theorem extend_precomp (a : A) {X Y : V} (F : EnrichedFunctorCat V A)
    (f : X ⟶ Y) (g : Y ⟶ F.toEnrichedFunctor.obj a) :
    extend a X F (f ≫ g) = (functor a).map f ≫ extend a Y F g := by
  apply EnrichedFunctorCat.hom_ext
  intro b
  rw [extend_component, EnrichedFunctorCat.component_comp,
    coefficientMap_component, extend_component]
  simp only [extensionComponent, tensorHom_id, comp_whiskerRight, Category.assoc]

/-- Identity evaluation respects the actual target transformation components. -/
theorem evaluate_postcomp (a : A) (X : V) {F G : EnrichedFunctorCat V A}
    (f : object a X ⟶ F) (g : F ⟶ G) :
    evaluate a X G (f ≫ g) = evaluate a X F f ≫
      (EnrichedFunctorCat.evaluation a).map g := by
  let p := (ρ_ X).inv
  let q := X ◁ eId V a
  let r := EnrichedFunctorCat.component f a
  let t := EnrichedFunctorCat.component g a
  have hComp : EnrichedFunctorCat.component (f ≫ g) a = r ≫ t :=
    EnrichedFunctorCat.component_comp f g a
  have hLeft : evaluate a X G (f ≫ g) = p ≫ q ≫ (r ≫ t) :=
    congrArg (fun z => p ≫ q ≫ z) hComp
  change evaluate a X G (f ≫ g) = (p ≫ q ≫ r) ≫ t
  exact hLeft.trans ((Category.assoc p q (r ≫ t)).symm.trans
    ((Category.assoc (p ≫ q) r t).symm.trans
      (congrArg (fun z => z ≫ t) (Category.assoc p q r))))


/-- The actual arbitrary-coefficient free functor is left adjoint to genuine evaluation. -/
def adjunction (a : A) : functor (V := V) a ⊣ EnrichedFunctorCat.evaluation (V := V) a :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv a
      homEquiv_naturality_left_symm := fun f g => extend_precomp a _ f g
      homEquiv_naturality_right := fun f g => evaluate_postcomp a _ f g }

/-- The chosen adjunction uses the original identity-evaluation Hom correspondence. -/
theorem adjunction_homEquiv (a : A) :
    (adjunction (V := V) a).homEquiv = homEquiv (V := V) a :=
  Adjunction.mkOfHomEquiv_homEquiv _

omit [BraidedCategory V] in
/-- The free object uses the actual coefficient-tensor-hom formula at every index. -/
@[simp]
theorem object_obj (a b : A) (X : V) :
    (object a X).toEnrichedFunctor.obj b = X ⊗ (a ⟶[V] b) := rfl

omit [BraidedCategory V] in
/-- Its full uncurried hom map is the original associator/composition action. -/
-- The canonical simp rule is MonoidalClosed.uncurry_curry; duplicating its registration
-- here fails simpNF. FreeEvaluationSimpTests exercises the original public expression.
theorem object_uncurry_map (a b c : A) (X : V) :
    MonoidalClosed.uncurry ((object a X).toEnrichedFunctor.map b c) = action a X b c :=
  MonoidalClosed.uncurry_curry _

end CategoryTheory.EnrichedFunctorCat.Free

namespace CategoryTheory.EnrichedFunctorCat.Free.ValueFunctor
open MonoidalCategory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- The original right tensor functor has its literal complete object value. -/
theorem rightTensor_obj (H X : V) : (tensorRight H).obj X = X ⊗ H := rfl

/-- The original right tensor functor retains its literal complete morphism. -/
theorem rightTensor_map (H : V) {X Y : V} (f : X ⟶ Y) :
    (tensorRight H).map f = f ▷ H := rfl

variable [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

set_option backward.isDefEq.respectTransparency false in
/-- The actual free functor evaluated at any source index is the given right tensor functor. -/
def freeValueIso (a b : A) :
    Free.functor (V := V) a ⋙ EnrichedFunctorCat.evaluation b ≅ tensorRight (a ⟶[V] b) :=
  NatIso.ofComponents (fun X => eqToIso (Free.object_obj a b X)) (fun {_ _} f => by
    change EnrichedFunctorCat.component (Free.coefficientMap a f) b ≫ 𝟙 _ =
      𝟙 _ ≫ (f ▷ (a ⟶[V] b))
    rw [Free.coefficientMap_component, Category.comp_id, Category.id_comp])

end CategoryTheory.EnrichedFunctorCat.Free.ValueFunctor
