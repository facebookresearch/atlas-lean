/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Tensor

/-!
# Genuine naturality of the canonical Day kernel generators

For any enriched binary functor, inserting the actual enriched identity into
its kernel yields the genuine unit-graded transformation from the external
input tensor to the output functor composed with that binary functor.
Individual generator maps use only their particular presentations. Full hom
naturality uses the two endpoint presentations. Only the transformation record
requires these selected presentations at every output object.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uC uD uK

namespace CategoryTheory.EnrichedDayKernel.Generators

open MonoidalCategory BraidedCategory Limits
open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

section IdentityLaws

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {K : Type uK} [EnrichedCategory V K]

private theorem insertion_natural (x : K) {Q Q' : V} (f : Q ⟶ Q') :
    ((λ_ Q).inv ≫ (eId V x ⊗ₘ 𝟙 Q)) ≫ ((x ⟶[V] x) ◁ f) =
      f ≫ (λ_ Q').inv ≫ (eId V x ⊗ₘ 𝟙 Q') := by
  rw [Category.assoc, tensorHom_comp_whiskerLeft]
  simp only [Category.id_comp]
  rw [leftUnitor_inv_comp_tensorHom]
  simp only [tensorHom_id]

variable [BraidedCategory V]

private theorem after_identity {P : V} (x y : K) (s : P ⟶ (x ⟶[V] y)) :
    (ρ_ P).inv ≫ (s ⊗ₘ eId V x) ≫
        (β_ (x ⟶[V] y) (x ⟶[V] x)).hom ≫ eComp V x x y = s := by
  calc
    _ = (ρ_ P).inv ≫ (β_ P (𝟙_ V)).hom ≫
        (eId V x ⊗ₘ s) ≫ eComp V x x y := by
      simpa only [Category.assoc] using congrArg
        (fun q => (ρ_ P).inv ≫ q ≫ eComp V x x y)
        (braiding_naturality s (eId V x))
    _ = (λ_ P).inv ≫ (eId V x ⊗ₘ s) ≫ eComp V x x y := by
      rw [braiding_tensorUnit_right]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = s ≫ (λ_ (x ⟶[V] y)).inv ≫
        (eId V x ▷ (x ⟶[V] y)) ≫ eComp V x x y :=
      leftUnitor_inv_comp_tensorHom_assoc (eId V x) s (eComp V x x y)
    _ = s := by rw [e_id_comp, Category.comp_id]

private theorem before_identity {P : V} (x y : K) (s : P ⟶ (x ⟶[V] y)) :
    (λ_ P).inv ≫ (eId V y ⊗ₘ s) ≫
        (β_ (y ⟶[V] y) (x ⟶[V] y)).hom ≫ eComp V x y y = s := by
  calc
    _ = (λ_ P).inv ≫ (β_ (𝟙_ V) P).hom ≫
        (s ⊗ₘ eId V y) ≫ eComp V x y y := by
      simpa only [Category.assoc] using congrArg
        (fun q => (λ_ P).inv ≫ q ≫ eComp V x y y)
        (braiding_naturality (eId V y) s)
    _ = (ρ_ P).inv ≫ (s ⊗ₘ eId V y) ≫ eComp V x y y := by
      rw [braiding_tensorUnit_left]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = s ≫ (ρ_ (x ⟶[V] y)).inv ≫
        ((x ⟶[V] y) ◁ eId V y) ≫ eComp V x y y :=
      rightUnitor_inv_comp_tensorHom_assoc s (eId V y) (eComp V x y y)
    _ = s := by rw [e_comp_id, Category.comp_id]

private theorem outputAction_insert {P Q : V} (x y : K)
    (s : P ⟶ (x ⟶[V] y)) :
    (s ⊗ₘ ((λ_ Q).inv ≫ (eId V x ⊗ₘ 𝟙 Q))) ≫
        Output.outputAction x x y Q = s ⊗ₘ 𝟙 Q := by
  have hLift :
      (s ⊗ₘ ((λ_ Q).inv ≫ (eId V x ⊗ₘ 𝟙 Q))) ≫
          Output.outputAction x x y Q =
        ((ρ_ P).inv ≫ (s ⊗ₘ eId V x) ≫
          (β_ (x ⟶[V] y) (x ⟶[V] x)).hom ≫ eComp V x x y) ⊗ₘ 𝟙 Q := by
    dsimp only [Output.outputAction]
    monoidal
  exact hLift.trans (congrArg (fun q => q ⊗ₘ 𝟙 Q) (after_identity x y s))

end IdentityLaws

section GeneratorData

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)

/-- The original kernel generator with its actual identity weight inserted. -/
def point (a : C × D)
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))] :
    (F.externalTensor G).obj a ⟶ EnrichedDayKernel.obj T F G (T.obj a) :=
  (λ_ ((F.externalTensor G).obj a)).inv ≫
    (eId V (T.obj a) ⊗ₘ 𝟙 ((F.externalTensor G).obj a)) ≫
    EnrichedDayKernel.gen T F G (T.obj a) a

theorem point_output (a : C × D) (k : K) {P : V}
    (s : P ⟶ (T.obj a ⟶[V] k))
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)] :
    (point T F G a ⊗ₘ 𝟙 P) ≫
        (EnrichedDayKernel.obj T F G (T.obj a) ◁ s) ≫
        MonoidalClosed.uncurry (Output.map T F G (T.obj a) k) =
      (β_ P ((F.externalTensor G).obj a)).inv ≫
        (s ⊗ₘ 𝟙 ((F.externalTensor G).obj a)) ≫
        EnrichedDayKernel.gen T F G k a := by
  let x : K := T.obj a
  let Q : V := (F.externalTensor G).obj a
  let W : V := x ⟶[V] x
  let R : V := x ⟶[V] k
  let t : P ⟶ R := s
  let X : V := W ⊗ Q
  let E : V := EnrichedDayKernel.obj T F G x
  let u : Q ⟶ X := (λ_ Q).inv ≫ (eId V x ⊗ₘ 𝟙 Q)
  let γx : X ⟶ E := EnrichedDayKernel.gen T F G x a
  let γy : R ⊗ Q ⟶ EnrichedDayKernel.obj T F G k := EnrichedDayKernel.gen T F G k a
  let m : R ⟶ (ihom E).obj (EnrichedDayKernel.obj T F G k) := Output.map T F G x k
  have hγ : (γx ⊗ₘ 𝟙 R) ≫ MonoidalClosed.uncurry m =
      (β_ R X).inv ≫ Output.outputAction x x k Q ≫ γy := by
    have h := congrArg (fun q => (β_ R X).inv ≫ q)
      (Output.gen_naturality T F G x k a)
    simpa only [x, Q, W, R, X, E, γx, γy, m, Output.actionGenerator,
      EnrichedDayKernel.objects, Enriched.weightedCoend.objects,
      EnrichedDayKernel.weight_obj, Category.assoc, Iso.inv_hom_id_assoc] using h
  have hNatural : (t ⊗ₘ u) ≫ (β_ R X).hom =
      (β_ P Q).hom ≫ (u ⊗ₘ t) := braiding_naturality t u
  have hBraid : (u ⊗ₘ t) ≫ (β_ R X).inv =
      (β_ P Q).inv ≫ (t ⊗ₘ u) := by
    have h := congrArg (fun q => (β_ P Q).inv ≫ q ≫ (β_ R X).inv) hNatural
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h.symm
  have hStart : ((u ≫ γx) ⊗ₘ 𝟙 P) ≫ (E ◁ t) ≫ MonoidalClosed.uncurry m =
      (u ⊗ₘ t) ≫ (γx ⊗ₘ 𝟙 R) ≫ MonoidalClosed.uncurry m := by
    have hLeft : ((u ≫ γx) ⊗ₘ 𝟙 P) ≫ (E ◁ t) = (u ≫ γx) ⊗ₘ t := by
      simpa only [Category.id_comp] using
        (tensorHom_comp_whiskerLeft (u ≫ γx) (𝟙 P) t)
    have hRight : (u ⊗ₘ t) ≫ (γx ⊗ₘ 𝟙 R) = (u ≫ γx) ⊗ₘ t := by
      simpa only [Category.comp_id] using (tensorHom_comp_tensorHom u t γx (𝟙 R))
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ MonoidalClosed.uncurry m) (hLeft.trans hRight.symm)
  have hWord : ((u ≫ γx) ⊗ₘ 𝟙 P) ≫ (E ◁ t) ≫ MonoidalClosed.uncurry m =
      (β_ P Q).inv ≫ (t ⊗ₘ 𝟙 Q) ≫ γy := by
    calc
      _ = (u ⊗ₘ t) ≫ (γx ⊗ₘ 𝟙 R) ≫ MonoidalClosed.uncurry m := hStart
      _ = (u ⊗ₘ t) ≫ (β_ R X).inv ≫ Output.outputAction x x k Q ≫ γy := by
        rw [hγ]
      _ = (β_ P Q).inv ≫ (t ⊗ₘ u) ≫ Output.outputAction x x k Q ≫ γy := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ Output.outputAction x x k Q ≫ γy) hBraid
      _ = (β_ P Q).inv ≫ (t ⊗ₘ 𝟙 Q) ≫ γy := by
        have hAct : (t ⊗ₘ u) ≫ Output.outputAction x x k Q = t ⊗ₘ 𝟙 Q := by
          simpa only [u] using outputAction_insert (P := P) (Q := Q) x k t
        simpa only [Category.assoc] using
          congrArg (fun q => (β_ P Q).inv ≫ q ≫ γy) hAct
  have hPoint : point T F G a = u ≫ γx := by
    exact (Category.assoc (λ_ Q).inv (eId V x ⊗ₘ 𝟙 Q) γx).symm
  have hPointWord := congrArg
    (fun q => (q ⊗ₘ 𝟙 P) ≫ (E ◁ t) ≫ MonoidalClosed.uncurry m) hPoint
  exact hPointWord.trans hWord

private theorem point_relation (a b : C × D)
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj b))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj b))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj b))
      (EnrichedDayKernel.rightMap T F G (T.obj b))] :
    (T.map a b ⊗ₘ 𝟙 ((F.externalTensor G).obj a)) ≫
        EnrichedDayKernel.gen T F G (T.obj b) a =
      (β_ (a ⟶[V] b) ((F.externalTensor G).obj a)).hom ≫
        MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫ point T F G b := by
  let x : K := T.obj a
  let y : K := T.obj b
  let P : V := a ⟶[V] b
  let Q : V := (F.externalTensor G).obj a
  let Q' : V := (F.externalTensor G).obj b
  let W : V := y ⟶[V] y
  let R : V := x ⟶[V] y
  let s : P ⟶ R := T.map a b
  let v : Q ⊗ P ⟶ Q' := MonoidalClosed.uncurry ((F.externalTensor G).map a b)
  let r : P ⊗ Q ⟶ W ⊗ (P ⊗ Q) :=
    (λ_ (P ⊗ Q)).inv ≫ (eId V y ⊗ₘ 𝟙 (P ⊗ Q))
  let γa : R ⊗ Q ⟶ EnrichedDayKernel.obj T F G y := EnrichedDayKernel.gen T F G y a
  let γb : W ⊗ Q' ⟶ EnrichedDayKernel.obj T F G y := EnrichedDayKernel.gen T F G y b
  have hRel :
      ((α_ W P Q).inv ≫
        (((W ◁ s) ≫ (β_ W R).hom ≫ eComp V x y y) ⊗ₘ 𝟙 Q)) ≫ γa =
      (W ◁ ((β_ P Q).hom ≫ v)) ≫ γb := by
    have h := EnrichedDayKernel.gen_balanced T F G y a b
    rw [EnrichedDayKernel.weight_uncurry_map] at h
    simpa only [x, y, P, Q, Q', W, R, s, v, γa, γb,
      EnrichedDayKernel.weight_obj, Category.assoc] using h
  have hWeight : r ≫ (α_ W P Q).inv ≫
      (((W ◁ s) ≫ (β_ W R).hom ≫ eComp V x y y) ⊗ₘ 𝟙 Q) =
        s ⊗ₘ 𝟙 Q := by
    have hStructural (A B C : V) (e : 𝟙_ V ⟶ A) :
        ((λ_ (B ⊗ C)).inv ≫ (e ⊗ₘ 𝟙 (B ⊗ C))) ≫ (α_ A B C).inv =
          ((λ_ B).inv ≫ (e ⊗ₘ 𝟙 B)) ⊗ₘ 𝟙 C := by
      simp only [tensorHom_id]
      rw [leftUnitor_tensor_inv]
      simp only [Category.assoc]
      rw [associator_inv_naturality_left]
      simp only [Iso.hom_inv_id_assoc, comp_whiskerRight]
    let e : 𝟙_ V ⟶ W := eId V y
    let i : P ⟶ W ⊗ P := (λ_ P).inv ≫ (e ⊗ₘ 𝟙 P)
    let c : R ⊗ W ⟶ R := eComp V x y y
    let f : W ⊗ P ⟶ R := (W ◁ s) ≫ (β_ W R).hom ≫ c
    have hPad : r ≫ (α_ W P Q).inv = i ⊗ₘ 𝟙 Q := by
      simpa only [r, i, e] using hStructural W P Q e
    have hInsert : i ≫ (W ◁ s) = (λ_ P).inv ≫ (e ⊗ₘ s) := by
      dsimp only [i]
      rw [Category.assoc, tensorHom_comp_whiskerLeft]
      simp only [Category.id_comp]
    have hContract : i ≫ f = s := by
      have h := congrArg (fun q => q ≫ (β_ W R).hom ≫ c) hInsert
      have hPrefix : i ≫ f = (λ_ P).inv ≫ (e ⊗ₘ s) ≫ (β_ W R).hom ≫ c := by
        simpa only [f, Category.assoc] using h
      exact hPrefix.trans (before_identity x y s)
    change r ≫ (α_ W P Q).inv ≫ (f ⊗ₘ 𝟙 Q) = s ⊗ₘ 𝟙 Q
    calc
      _ = (i ⊗ₘ 𝟙 Q) ≫ (f ⊗ₘ 𝟙 Q) := by
        simpa only [Category.assoc] using congrArg (fun q => q ≫ (f ⊗ₘ 𝟙 Q)) hPad
      _ = (i ≫ f) ⊗ₘ 𝟙 Q := by
        simpa only [Category.id_comp] using tensorHom_comp_tensorHom i (𝟙 Q) f (𝟙 Q)
      _ = _ := congrArg (fun q => q ⊗ₘ 𝟙 Q) hContract
  have hDiagram : r ≫ (W ◁ ((β_ P Q).hom ≫ v)) ≫ γb =
      (β_ P Q).hom ≫ v ≫ (λ_ Q').inv ≫ (eId V y ⊗ₘ 𝟙 Q') ≫ γb := by
    simpa only [r, W, Category.assoc] using congrArg (fun q => q ≫ γb)
      (insertion_natural y ((β_ P Q).hom ≫ v))
  have h := congrArg (fun q => r ≫ q) hRel
  change (s ⊗ₘ 𝟙 Q) ≫ γa =
    (β_ P Q).hom ≫ v ≫ ((λ_ Q').inv ≫ (eId V y ⊗ₘ 𝟙 Q') ≫ γb)
  calc
    _ = r ≫ (α_ W P Q).inv ≫
        (((W ◁ s) ≫ (β_ W R).hom ≫ eComp V x y y) ⊗ₘ 𝟙 Q) ≫ γa := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ γa) hWeight.symm
    _ = r ≫ (W ◁ ((β_ P Q).hom ≫ v)) ≫ γb := by
      simpa only [Category.assoc] using h
    _ = _ := by simpa only [Category.assoc] using hDiagram

/-- Full product-hom naturality uses exactly the two original endpoint coends. -/
theorem point_natural (a b : C × D)
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj b))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj b))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj b))
      (EnrichedDayKernel.rightMap T F G (T.obj b))] :
    MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫ point T F G b =
      (point T F G a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        (EnrichedDayKernel.obj T F G (T.obj a) ◁ T.map a b) ≫
        MonoidalClosed.uncurry (Output.map T F G (T.obj a) (T.obj b)) := by
  have hRel := congrArg
    (fun q => (β_ (a ⟶[V] b) ((F.externalTensor G).obj a)).inv ≫ q)
    (point_relation T F G a b)
  have hOut := point_output T F G a (T.obj b) (T.map a b)
  calc
    _ = (β_ (a ⟶[V] b) ((F.externalTensor G).obj a)).inv ≫
        (T.map a b ⊗ₘ 𝟙 ((F.externalTensor G).obj a)) ≫
        EnrichedDayKernel.gen T F G (T.obj b) a := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hRel.symm
    _ = _ := hOut.symm

variable
  [∀ k, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

/-- The original generators form a genuine unit-graded transformation. -/
def transformation :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (F.externalTensor G) (T.comp V (Output.functor T F G)) :=
  GradedNatTrans.unitOfComponents (fun a => point T F G a) (fun a b => by
    change MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫ point T F G b =
      (point T F G a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (T.map a b ≫ Output.map T F G (T.obj a) (T.obj b))
    rw [MonoidalClosed.uncurry_natural_left]
    exact point_natural T F G a b)

/-- The genuine transformation retains the literal identity-insertion component. -/
theorem transformation_component (a : C × D) :
    (eHomEquiv V).symm ((transformation T F G).app a) = point T F G a := by
  exact GradedNatTrans.unitOfComponents_component (V := V)
    (F' := F.externalTensor G) (G' := T.comp V (Output.functor T F G))
    (fun a => point T F G a) (fun a b => by
      change MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫ point T F G b =
        (point T F G a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (T.map a b ≫ Output.map T F G (T.obj a) (T.obj b))
      rw [MonoidalClosed.uncurry_natural_left]
      exact point_natural T F G a b) a

end GeneratorData

section InputNaturality

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  {F F' : EnrichedFunctor V C V} {G G' : EnrichedFunctor V D V}

/-- Input maps act on the canonical points by the two actual input components. -/
@[reassoc]
theorem point_input_natural
    (p : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
    (q : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G') (a : C × D)
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.relations T F' G' (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F' G' (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F' G' (T.obj a))
      (EnrichedDayKernel.rightMap T F' G' (T.obj a))] :
    point T F G a ≫ Input.mapAt T p q (T.obj a) =
      ((eHomEquiv V).symm (p.app a.1) ⊗ₘ (eHomEquiv V).symm (q.app a.2)) ≫
        point T F' G' a := by
  let x : K := T.obj a
  let Q : V := (F.externalTensor G).obj a
  let Q' : V := (F'.externalTensor G').obj a
  let W : V := x ⟶[V] x
  let c : Q ⟶ Q' :=
    (eHomEquiv V).symm (p.app a.1) ⊗ₘ (eHomEquiv V).symm (q.app a.2)
  let u : Q ⟶ W ⊗ Q := (λ_ Q).inv ≫ (eId V x ⊗ₘ 𝟙 Q)
  let u' : Q' ⟶ W ⊗ Q' := (λ_ Q').inv ≫ (eId V x ⊗ₘ 𝟙 Q')
  let γ : W ⊗ Q ⟶ EnrichedDayKernel.obj T F G x := EnrichedDayKernel.gen T F G x a
  let γ' : W ⊗ Q' ⟶ EnrichedDayKernel.obj T F' G' x := EnrichedDayKernel.gen T F' G' x a
  let m : EnrichedDayKernel.obj T F G x ⟶ EnrichedDayKernel.obj T F' G' x :=
    Input.mapAt T p q x
  have hGen : γ ≫ m = (𝟙 W ⊗ₘ c) ≫ γ' := Input.gen_mapAt T p q x a
  have hInsert : u ≫ (𝟙 W ⊗ₘ c) = c ≫ u' := by
    simpa only [u, u', W, id_tensorHom] using insertion_natural x c
  have hPoint : point T F G a = u ≫ γ := by
    exact (Category.assoc (λ_ Q).inv (eId V x ⊗ₘ 𝟙 Q) γ).symm
  have hPoint' : point T F' G' a = u' ≫ γ' := by
    exact (Category.assoc (λ_ Q').inv (eId V x ⊗ₘ 𝟙 Q') γ').symm
  calc
    _ = (u ≫ γ) ≫ m := congrArg (fun v => v ≫ m) hPoint
    _ = u ≫ (𝟙 W ⊗ₘ c) ≫ γ' := by
      simpa only [Category.assoc] using congrArg (fun v => u ≫ v) hGen
    _ = (c ≫ u') ≫ γ' := by
      simpa only [Category.assoc] using congrArg (fun v => v ≫ γ') hInsert
    _ = c ≫ point T F' G' a := by
      simpa only [Category.assoc] using congrArg (fun v => c ≫ v) hPoint'.symm

end InputNaturality

end CategoryTheory.EnrichedDayKernel.Generators
