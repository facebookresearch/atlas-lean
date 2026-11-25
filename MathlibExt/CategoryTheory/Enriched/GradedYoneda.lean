/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.NaturalTransformation
public import MathlibExt.CategoryTheory.Enriched.Representable

/-!
# Genuine unit-graded enriched Yoneda

For a plain enriched index, actual unit-graded transformations from a covariant
representable are determined by their value on the enriched identity. No index
ordinary category or end-existence hypothesis is required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC uV vV

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]

/-- Uncurrying the actual composition in the closed self-enrichment. -/
theorem uncurry_eComp
    {P Q R H K : V}
    (p : H ⟶ (ihom P).obj Q) (q : K ⟶ (ihom Q).obj R) :
    MonoidalClosed.uncurry
        ((p ⊗ₘ q) ≫ eComp V P Q R) =
      (α_ P H K).inv ≫
        (MonoidalClosed.uncurry p ▷ K) ≫
        MonoidalClosed.uncurry q := by
  simp only [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedCategorySelf_comp,
    MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry,
    MonoidalClosed.compTranspose_eq]
  have hTensor :
      P ◁ (p ⊗ₘ q) ≫
          (α_ P ((ihom P).obj Q) ((ihom Q).obj R)).inv =
        (α_ P H K).inv ≫
          ((P ◁ p) ▷ K) ≫
          (P ⊗ (ihom P).obj Q) ◁ q := by
    simpa only [id_tensorHom, tensorHom_def,
      MonoidalCategory.id_whiskerRight, Category.id_comp,
      comp_whiskerRight] using
      (associator_inv_naturality (𝟙 P) p q)
  rw [← Category.assoc, hTensor]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]
  rw [← comp_whiskerRight_assoc]
  rw [← MonoidalClosed.uncurry_eq]
  dsimp
  rw [← MonoidalClosed.uncurry_eq]

end CategoryTheory.MonoidalClosed

namespace CategoryTheory.GradedYoneda

open MonoidalCategory BraidedCategory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]

/-- The actual covariant enriched representable at the supplied index object. -/
abbrev representable (i : C) : EnrichedFunctor V C V :=
  EnrichedFunctor.covariantRepresentable V C i

omit [BraidedCategory V] in
/-- Its object is the full enriched hom object. -/
@[simp]
theorem representable_obj (i x : C) :
    (representable (V := V) i).obj x = (i ⟶[V] x) := rfl

omit [BraidedCategory V] in
/-- Its full uncurried action is enriched composition. -/
theorem representable_uncurry (i x y : C) :
    MonoidalClosed.uncurry ((representable (V := V) i).map x y) = eComp V i x y := by
  change MonoidalClosed.uncurry (MonoidalClosed.curry (eComp V i x y)) = _
  exact MonoidalClosed.uncurry_curry _

/-- The literal enriched Yoneda component selected by a value at i. -/
def component (i : C) (F : EnrichedFunctor V C V) (e : 𝟙_ V ⟶ F.obj i) (k : C) :
    (i ⟶[V] k) ⟶ F.obj k :=
  (λ_ (i ⟶[V] k)).inv ≫ (e ⊗ₘ 𝟙 (i ⟶[V] k)) ≫ MonoidalClosed.uncurry (F.map i k)

omit [BraidedCategory V] in
/-- These components satisfy naturality on the entire index hom object. -/
theorem component_natural (i : C) (F : EnrichedFunctor V C V)
    (e : 𝟙_ V ⟶ F.obj i) (k k' : C) :
    MonoidalClosed.uncurry ((representable (V := V) i).map k k') ≫ component i F e k' =
      (component i F e k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫ MonoidalClosed.uncurry (F.map k k') := by
  rw [representable_uncurry]
  let A : V := F.obj i
  let W : V := i ⟶[V] k
  let R : V := k ⟶[V] k'
  let W' : V := i ⟶[V] k'
  let c : W ⊗ R ⟶ W' := eComp V i k k'
  have hcomp := congrArg MonoidalClosed.uncurry
    (F.map_comp i k k')
  conv_lhs at hcomp =>
    rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_eComp] at hcomp
  have hLeft :
      (λ_ (W ⊗ R)).inv ≫ (e ⊗ₘ 𝟙 (W ⊗ R)) ≫
            (A ◁ c) =
        c ≫ (λ_ W').inv ≫ (e ⊗ₘ 𝟙 W') := by
    calc
      _ = (λ_ (W ⊗ R)).inv ≫ (e ⊗ₘ c) := by
        rw [tensorHom_comp_whiskerLeft]
        simp only [Category.id_comp]
      _ = c ≫ (λ_ W').inv ≫ (e ▷ W') := by
        rw [leftUnitor_inv_comp_tensorHom]
      _ = _ := by rw [← tensorHom_id]
  have hRight :
      (λ_ (W ⊗ R)).inv ≫ (e ⊗ₘ 𝟙 (W ⊗ R)) ≫
            (α_ A W R).inv =
        ((λ_ W).inv ≫ (e ⊗ₘ 𝟙 W)) ⊗ₘ 𝟙 R := by
    dsimp only [A, W, R]
    monoidal
  change c ≫ component i F e k' =
    (component i F e k ⊗ₘ 𝟙 R) ≫ MonoidalClosed.uncurry (F.map k k')
  calc
    c ≫ component i F e k' =
        (λ_ (W ⊗ R)).inv ≫ (e ⊗ₘ 𝟙 (W ⊗ R)) ≫
          (A ◁ c) ≫
          MonoidalClosed.uncurry (F.map i k') := by
            have h := congrArg
              (fun t => t ≫ MonoidalClosed.uncurry
                (F.map i k')) hLeft.symm
            simpa only [component, Category.assoc] using h
    _ = (λ_ (W ⊗ R)).inv ≫ (e ⊗ₘ 𝟙 (W ⊗ R)) ≫
          (α_ A W R).inv ≫
          (MonoidalClosed.uncurry (F.map i k) ▷ R) ≫
          MonoidalClosed.uncurry (F.map k k') := by
            have h := congrArg
              (fun t =>
                (λ_ (W ⊗ R)).inv ≫
                  (e ⊗ₘ 𝟙 (W ⊗ R)) ≫ t) hcomp
            simpa only [A, W, R, W', c, Category.assoc] using h
    _ = (component i F e k ⊗ₘ 𝟙 R) ≫
          MonoidalClosed.uncurry (F.map k k') := by
            have h := congrArg
              (fun t => t ≫
                (MonoidalClosed.uncurry (F.map i k) ▷ R) ≫
                MonoidalClosed.uncurry (F.map k k')) hRight
            calc
              _ = (((λ_ W).inv ≫ (e ⊗ₘ 𝟙 W)) ⊗ₘ 𝟙 R) ≫
                    (MonoidalClosed.uncurry (F.map i k) ▷ R) ≫
                    MonoidalClosed.uncurry (F.map k k') := by
                  simpa only [Category.assoc] using h
              _ = _ := by
                  rw [← tensorHom_id]
                  rw [← Category.assoc, tensorHom_comp_tensorHom]
                  simp only [component, W, Category.comp_id, Category.assoc]

/-- Extend the supplied value to a genuine unit-graded transformation. -/
abbrev extend (i : C) (F : EnrichedFunctor V C V) (e : 𝟙_ V ⟶ F.obj i) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (representable i) F :=
  GradedNatTrans.unitOfComponents (component i F e) (component_natural i F e)

/-- Extension has the actual literal ordinary component. -/
@[simp]
theorem extend_component (i : C) (F : EnrichedFunctor V C V)
    (e : 𝟙_ V ⟶ F.obj i) (k : C) :
    (eHomEquiv V).symm ((extend i F e).app k) = component i F e k :=
  GradedNatTrans.unitOfComponents_component _ _ k

/-- Evaluate a genuine transformation on the enriched identity at i. -/
def evaluate (i : C) (F : EnrichedFunctor V C V)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (representable i) F) :
    𝟙_ V ⟶ F.obj i :=
  eId V i ≫ (eHomEquiv V).symm (t.app i)

/-- Full hom-object naturality reconstructs each actual component. -/
theorem reconstruct_component (i : C) (F : EnrichedFunctor V C V)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (representable i) F) (k : C) :
    (eHomEquiv V).symm (t.app k) = component i F (evaluate i F t) k := by
  let m : ∀ x : C, (i ⟶[V] x) ⟶ F.obj x := fun x => (eHomEquiv V).symm (t.app x)
  have hn : eComp V i i k ≫ m k =
      (m i ⊗ₘ 𝟙 (i ⟶[V] k)) ≫ MonoidalClosed.uncurry (F.map i k) := by
    simpa only [representable_uncurry, MonoidalClosed.uncurry_curry, m] using
      t.uncurriedNaturality i k
  let H : V := i ⟶[V] k
  have hn' := congrArg (fun q => (λ_ H).inv ≫ (eId V i ▷ H) ≫ q) hn
  have hid := congrArg (fun q => q ≫ m k) (e_id_comp V i k)
  change m k = (λ_ H).inv ≫ ((eId V i ≫ m i) ⊗ₘ 𝟙 H) ≫
    MonoidalClosed.uncurry (F.map i k)
  calc
    _ = (λ_ H).inv ≫ (eId V i ▷ H) ≫ eComp V i i k ≫ m k := by
      simpa only [H, Category.assoc, Category.id_comp] using hid.symm
    _ = (λ_ H).inv ≫ (eId V i ▷ H) ≫ (m i ⊗ₘ 𝟙 H) ≫
        MonoidalClosed.uncurry (F.map i k) := by
      simpa only [H, Category.assoc] using hn'
    _ = _ := by
      rw [← tensorHom_id]
      slice_lhs 2 3 =>
        rw [tensorHom_comp_tensorHom]
        simp only [Category.comp_id]

/-- Evaluation of the extension recovers the supplied value. -/
@[simp]
theorem evaluate_extend (i : C) (F : EnrichedFunctor V C V) (e : 𝟙_ V ⟶ F.obj i) :
    evaluate i F (extend i F e) = e := by
  have hu := congrArg (MonoidalClosed.uncurry (A := F.obj i)) (F.map_id i)
  simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at hu
  calc
    _ = eId V i ≫ component i F e i := by rw [evaluate, extend_component]
    _ = (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ eId V i) ≫ MonoidalClosed.uncurry (F.map i i) := by
      have h := congrArg (fun q => q ≫ MonoidalClosed.uncurry (F.map i i))
        (leftUnitor_inv_comp_tensorHom e (eId V i)).symm
      simpa only [component, tensorHom_id, Category.assoc] using h
    _ = (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ 𝟙 (𝟙_ V)) ≫
        F.obj i ◁ eId V i ≫ MonoidalClosed.uncurry (F.map i i) := by
      have hTensor :
          (e ⊗ₘ 𝟙 (𝟙_ V)) ≫ F.obj i ◁ eId V i = e ⊗ₘ eId V i := by
        simpa only [Category.id_comp] using
          (tensorHom_comp_whiskerLeft e (𝟙 (𝟙_ V)) (eId V i))
      simpa only [Category.assoc] using
        congrArg (fun m =>
          (λ_ (𝟙_ V)).inv ≫ m ≫ MonoidalClosed.uncurry (F.map i i)) hTensor.symm
    _ = (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ 𝟙 (𝟙_ V)) ≫ (ρ_ (F.obj i)).hom := by rw [hu]
    _ = _ := by monoidal

/-- The genuine transformation is recovered from its value on the identity. -/
@[simp]
theorem extend_evaluate (i : C) (F : EnrichedFunctor V C V)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (representable i) F) :
    extend i F (evaluate i F t) = t := by
  apply GradedNatTrans.ext
  funext k
  apply (eHomEquiv V).symm.injective
  rw [extend_component]
  exact (reconstruct_component i F t k).symm

/-- Genuine transformations from the representable are detected at the identity. -/
theorem hom_ext (i : C) (F : EnrichedFunctor V C V)
    {s t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (representable i) F}
    (h : evaluate i F s = evaluate i F t) : s = t := by
  rw [← extend_evaluate i F s, ← extend_evaluate i F t, h]

/-- The actual enriched Yoneda bijection for unit-graded transformations. -/
def equiv (i : C) (F : EnrichedFunctor V C V) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (representable i) F ≃ (𝟙_ V ⟶ F.obj i) where
  toFun := evaluate i F
  invFun := extend i F
  left_inv := extend_evaluate i F
  right_inv := evaluate_extend i F

/-- Evaluation composes source-first with an actual genuine target transformation. -/
theorem evaluate_comp (i : C) {F G : EnrichedFunctor V C V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (representable i) F)
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) :
    evaluate i G (GradedNatTrans.unitComp t a) =
      evaluate i F t ≫ (eHomEquiv V).symm (a.app i) := by
  simpa only [evaluate, Category.assoc] using
    congrArg (fun m => eId V i ≫ m)
      (GradedNatTrans.unitComp_component t a i)

end CategoryTheory.GradedYoneda
