/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Output
public import MathlibExt.CategoryTheory.Enriched.NaturalTransformation

/-!
# Original continuous Day action from a genuine enriched transformation

A genuine transformation from the external input tensor to an output
diagram composed with the original enriched tensor determines the entire
Day generator family. Its full product-Hom balance follows from genuine
graded naturality and the original enriched co-Yoneda action equation.
Descent uses the original selected Day coproducts and coequalizer.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uK

open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ActionFromTransformation

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

private theorem tensorPairSquare {W P Q A B U : V}
    (p : P ⟶ Q) (f : A ⟶ B) (r : W ⊗ Q ⟶ U) :
    (W ◁ (p ⊗ₘ f)) ≫ (α_ W Q B).inv ≫ (r ▷ B) =
      (α_ W P A).inv ≫ ((W ◁ p ≫ r) ▷ A) ≫ (U ◁ f) := by
  rw [tensorHom_def]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]

private theorem tensorDiagramSquare {H W C A B : V}
    (f : A ⟶ B) (s : H ⊗ W ⟶ C) :
    (H ◁ (W ◁ f)) ≫ (α_ H W B).inv ≫ (s ▷ B) =
      (α_ H W A).inv ≫ (s ▷ A) ≫ (C ◁ f) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange]

variable [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  (X : EnrichedFunctor V K V)
  (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (F.externalTensor G) (T.comp V X))

/-- The actual ordinary component of the supplied genuine enriched transformation. -/
def component (a : C × D) : (F.externalTensor G).obj a ⟶ X.obj (T.obj a) :=
  (eHomEquiv V).symm (t.app a)

/-- The whole output-Hom action of the existing enriched output diagram. -/
def targetAction (a b : K) : (a ⟶[V] b) ⊗ X.obj a ⟶ X.obj b :=
  (β_ (a ⟶[V] b) (X.obj a)).hom ≫ MonoidalClosed.uncurry (X.map a b)

/-- The entire original Day generator family, retaining every input and output Hom. -/
def generator (k : K) (a : C × D) : EnrichedDayKernel.objects T F G k a ⟶ X.obj k :=
  (𝟙 (T.obj a ⟶[V] k) ⊗ₘ component T F G X t a) ≫
    targetAction X (T.obj a) k

/-- The literal tensor map in a generator is the canonical left whisker. -/
theorem generator_eq (k : K) (a : C × D) :
    generator T F G X t k a =
      ((T.obj a ⟶[V] k) ◁ component T F G X t a) ≫
        targetAction X (T.obj a) k :=
  congrArg (fun z => z ≫ targetAction X (T.obj a) k)
    (id_tensorHom (T.obj a ⟶[V] k) (component T F G X t a))

private theorem component_full_naturality (a b : C × D) :
    (β_ (a ⟶[V] b) ((F.externalTensor G).obj a)).hom ≫
        MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫ component T F G X t b =
      ((a ⟶[V] b) ◁ component T F G X t a) ≫
        (T.map a b ▷ X.obj (T.obj a)) ≫ targetAction X (T.obj a) (T.obj b) := by
  let P : V := a ⟶[V] b
  let A := (F.externalTensor G).obj a
  let Y := X.obj (T.obj a)
  let H : V := T.obj a ⟶[V] T.obj b
  have hn : MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫
      component T F G X t b =
    (component T F G X t a ⊗ₘ 𝟙 P) ≫
      MonoidalClosed.uncurry ((T.comp V X).map a b) :=
    GradedNatTrans.uncurriedNaturality t a b
  have hTarget : MonoidalClosed.uncurry ((T.comp V X).map a b) =
      (Y ◁ T.map a b) ≫ MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b)) :=
    MonoidalClosed.uncurry_natural_left (T.map a b) (X.map (T.obj a) (T.obj b))
  have hFirst : (β_ P A).hom ≫ (component T F G X t a ▷ P) =
      (P ◁ component T F G X t a) ≫ (β_ P Y).hom :=
    (braiding_naturality_right P (component T F G X t a)).symm
  have hSecond : (β_ P Y).hom ≫ (Y ◁ T.map a b) =
      (T.map a b ▷ Y) ≫ (β_ H Y).hom :=
    (braiding_naturality_left (T.map a b) Y).symm
  have hTargetComposite :
      (β_ P A).hom ≫ (component T F G X t a ⊗ₘ 𝟙 P) ≫
        MonoidalClosed.uncurry ((T.comp V X).map a b) =
      (β_ P A).hom ≫ (component T F G X t a ▷ P) ≫
        (Y ◁ T.map a b) ≫ MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b)) :=
    (congrArg (fun z => (β_ P A).hom ≫ z ≫
      MonoidalClosed.uncurry ((T.comp V X).map a b))
        (tensorHom_id (component T F G X t a) P)).trans
      (congrArg (fun z => (β_ P A).hom ≫ (component T F G X t a ▷ P) ≫ z) hTarget)
  have h : (β_ P A).hom ≫ MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫
      component T F G X t b =
    (β_ P A).hom ≫ (component T F G X t a ▷ P) ≫
      (Y ◁ T.map a b) ≫ MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b)) :=
    (congrArg (fun z => (β_ P A).hom ≫ z) hn).trans hTargetComposite
  calc
    _ = (β_ P A).hom ≫ (component T F G X t a ▷ P) ≫
        (Y ◁ T.map a b) ≫ MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b)) := h
    _ = (((β_ P A).hom ≫ (component T F G X t a ▷ P)) ≫
        (Y ◁ T.map a b)) ≫ MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b)) := by
      simp only [Category.assoc]
    _ = (((P ◁ component T F G X t a) ≫ (β_ P Y).hom) ≫
        (Y ◁ T.map a b)) ≫ MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b)) :=
      congrArg (fun z => (z ≫ (Y ◁ T.map a b)) ≫
        MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b))) hFirst
    _ = (P ◁ component T F G X t a) ≫
        (((β_ P Y).hom ≫ (Y ◁ T.map a b)) ≫
          MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b))) := by
      simp only [Category.assoc]
    _ = (P ◁ component T F G X t a) ≫
        (((T.map a b ▷ Y) ≫ (β_ H Y).hom) ≫
          MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b))) :=
      congrArg (fun z => (P ◁ component T F G X t a) ≫
        (z ≫ MonoidalClosed.uncurry (X.map (T.obj a) (T.obj b)))) hSecond
    _ = _ := by
      simp only [P, Y, H, targetAction, Category.assoc]

/-- The family satisfies the entire original product-enriched Day relation. -/
theorem generator_balanced (k : K) :
    EnrichedDayKernel.Balanced T F G k (generator T F G X t k) := by
  intro a b
  let W : V := T.obj b ⟶[V] k
  let P : V := a ⟶[V] b
  let H : V := T.obj a ⟶[V] T.obj b
  let A := (F.externalTensor G).obj a
  let Y := X.obj (T.obj a)
  let r : W ⊗ H ⟶ (T.obj a ⟶[V] k) :=
    (β_ W H).hom ≫ eComp V (T.obj a) (T.obj b) k
  let pre : W ⊗ (P ⊗ A) ⟶ W ⊗ (H ⊗ Y) :=
    W ◁ (T.map a b ⊗ₘ component T F G X t a)
  let weightAction := W ◁ T.map a b ≫ r
  have hTensor := tensorPairSquare (T.map a b) (component T F G X t a) r
  have hYoneda :
      (α_ W H Y).inv ≫ (r ▷ Y) ≫ targetAction X (T.obj a) k =
        (W ◁ targetAction X (T.obj a) (T.obj b)) ≫ targetAction X (T.obj b) k := by
    simpa only [W, H, Y, r, targetAction, tensorHom_id, Category.assoc] using
      Enriched.weightedCoend.coyonedaCondition X k (T.obj a) (T.obj b)
  have hNature := congrArg (fun q => (W ◁ q) ≫ targetAction X (T.obj b) k)
    (component_full_naturality T F G X t a b)
  have hPair := tensorHom_def' (T.map a b) (component T F G X t a)
  have hWeight : MonoidalClosed.uncurry
      ((EnrichedDayKernel.weight T k).map (Opposite.op b) (Opposite.op a)) =
        weightAction := EnrichedDayKernel.weight_uncurry_map T k a b
  have hLeft :
      (((α_ W P A).inv ≫
          (MonoidalClosed.uncurry
            ((EnrichedDayKernel.weight T k).map (Opposite.op b) (Opposite.op a)) ⊗ₘ 𝟙 A)) ≫
        generator T F G X t k a) =
      (α_ W P A).inv ≫ (weightAction ▷ A) ≫ generator T F G X t k a :=
    (congrArg (fun z => ((α_ W P A).inv ≫ (z ⊗ₘ 𝟙 A)) ≫
      generator T F G X t k a) hWeight).trans
        ((congrArg (fun z => ((α_ W P A).inv ≫ z) ≫ generator T F G X t k a)
          (tensorHom_id weightAction A)).trans (Category.assoc _ _ _))
  apply hLeft.trans
  change (α_ W P A).inv ≫ (weightAction ▷ A) ≫ generator T F G X t k a =
    (W ◁ ((β_ P A).hom ≫ MonoidalClosed.uncurry ((F.externalTensor G).map a b))) ≫
      generator T F G X t k b
  rw [generator_eq T F G X t k a, generator_eq T F G X t k b]
  calc
    _ = pre ≫ (α_ W H Y).inv ≫ (r ▷ Y) ≫ targetAction X (T.obj a) k := by
      simpa only [pre, W, P, H, A, Y, weightAction, Category.assoc] using
        (congrArg (fun q => q ≫ targetAction X (T.obj a) k) hTensor).symm
    _ = pre ≫ (W ◁ targetAction X (T.obj a) (T.obj b)) ≫
        targetAction X (T.obj b) k := by
      simpa only [Category.assoc] using congrArg (fun q => pre ≫ q) hYoneda
    _ = _ := by
      simpa only [pre, W, P, H, A, Y, targetAction, hPair,
        whiskerLeft_comp, Category.assoc] using hNature.symm

/-- The entire output Hom acts naturally on the original Day generator family. -/
theorem generator_output_naturality (k l : K) (a : C × D) :
    EnrichedDayKernel.Output.outputAction (T.obj a) k l ((F.externalTensor G).obj a) ≫
        generator T F G X t l a =
      ((k ⟶[V] l) ◁ generator T F G X t k a) ≫ targetAction X k l := by
  let H : V := k ⟶[V] l
  let W : V := T.obj a ⟶[V] k
  let A := (F.externalTensor G).obj a
  let Y := X.obj (T.obj a)
  let p : H ⊗ (W ⊗ A) ⟶ H ⊗ (W ⊗ Y) := H ◁ (W ◁ component T F G X t a)
  let c : H ⊗ W ⟶ (T.obj a ⟶[V] l) :=
    (β_ H W).hom ≫ eComp V (T.obj a) k l
  have hTensorOutput :
      ((β_ H W).hom ⊗ₘ 𝟙 A) ≫ (eComp V (T.obj a) k l ⊗ₘ 𝟙 A) = c ▷ A := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, tensorHom_id]
  have hOutput :
      EnrichedDayKernel.Output.outputAction (T.obj a) k l A =
        (α_ H W A).inv ≫ (c ▷ A) :=
    congrArg (fun z => (α_ H W A).inv ≫ z) hTensorOutput
  have hTensor := tensorDiagramSquare (component T F G X t a) c
  have hYoneda : (α_ H W Y).inv ≫ (c ▷ Y) ≫ targetAction X (T.obj a) l =
      (H ◁ targetAction X (T.obj a) k) ≫ targetAction X k l := by
    simpa only [H, W, Y, c, targetAction, tensorHom_id, Category.assoc] using
      Enriched.weightedCoend.coyonedaCondition X l (T.obj a) k
  rw [hOutput, generator_eq T F G X t l a, generator_eq T F G X t k a]
  change ((α_ H W A).inv ≫ (c ▷ A)) ≫
      (((T.obj a ⟶[V] l) ◁ component T F G X t a) ≫ targetAction X (T.obj a) l) =
    (H ◁ ((W ◁ component T F G X t a) ≫ targetAction X (T.obj a) k)) ≫
      targetAction X k l
  calc
    _ = p ≫ (α_ H W Y).inv ≫ (c ▷ Y) ≫ targetAction X (T.obj a) l := by
      simpa only [p, H, W, A, Y, Category.assoc] using
        (congrArg (fun q => q ≫ targetAction X (T.obj a) l) hTensor).symm
    _ = p ≫ (H ◁ targetAction X (T.obj a) k) ≫ targetAction X k l := by
      simpa only [Category.assoc] using congrArg (fun q => p ≫ q) hYoneda
    _ = _ := by
      simpa only [p, H, W, A, Y, Category.assoc] using congrArg (fun z => z ≫ targetAction X k l)
        (whiskerLeft_comp H (W ◁ component T F G X t a)
          (targetAction X (T.obj a) k)).symm

variable (k : K)
  [HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]

/-- Descend through the entire original continuous Day coend. -/
def desc : EnrichedDayKernel.obj T F G k ⟶ X.obj k :=
  EnrichedDayKernel.desc T F G k (generator T F G X t k) (generator_balanced T F G X t k)

/-- The descended map agrees with the entire original generator family. -/
theorem gen_desc (a : C × D) :
    EnrichedDayKernel.gen T F G k a ≫ desc T F G X t k = generator T F G X t k a :=
  EnrichedDayKernel.gen_desc T F G k (generator T F G X t k)
    (generator_balanced T F G X t k) a

end CategoryTheory.EnrichedDayKernel.ActionFromTransformation
