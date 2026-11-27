/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparison

/-!
# Associator Right General

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uE uK uM
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorRightGeneral
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]
  {K : Type uK} [EnrichedCategory V K]
  {M : Type uM} [EnrichedCategory V M]
attribute [local instance] Enriched.prodCategory
variable (T : EnrichedFunctor V (D × E) K) (U : EnrichedFunctor V (C × K) M)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (H : EnrichedFunctor V E V) (m : M)

/-- The literal original heterogeneous right triple index, with its entire product Hom map. -/
abbrev flatIndex : EnrichedFunctor V ((C × D) × E) M :=
  (AssociatorRightTensor.product (C := C) T).comp V U

/-- The original heterogeneous right triple representable weight at the unchanged output. -/
abbrev flatWeight : EnrichedFunctor V ((C × D) × E)ᵒᵖ V := weight (flatIndex T U) m

/-- The unchanged ordered three-input coefficient functor and full product Hom associator. -/
abbrev coefficients : EnrichedFunctor V ((C × D) × E) V := Associator.rightCoefficients F G H

/-- The object summands of the flat right weighted coend. -/
abbrev objects : (C × D) × E → V := Enriched.weightedCoend.objects (flatWeight T U m) (coefficients
  F G H)
/-- The relation summands of the flat right weighted coend, indexed by pairs of triples. -/
abbrev relations : ((C × D) × E) × ((C × D) × E) → V :=
  Enriched.weightedCoend.relations (flatWeight T U m) (coefficients F G H)

section Flat
variable [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
/-- The flat right coend relation map induced by the contravariant weight action. -/
abbrev map0 := Enriched.weightedCoend.leftMap (flatWeight T U m) (coefficients F G H)
/-- The flat right coend relation map induced by the covariant coefficient action. -/
abbrev map1 := Enriched.weightedCoend.rightMap (flatWeight T U m) (coefficients F G H)
variable [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]
/-- The chosen weighted coend of the composite right weight and external coefficients. -/
abbrev point : V := Enriched.weightedCoend (flatWeight T U m) (coefficients F G H)
/-- The canonical map from a flat right object summand to its chosen weighted coend. -/
abbrev generator (X : (C × D) × E) : objects T U F G H m X ⟶ point T U F G H m :=
  Enriched.weightedCoend.ι (flatWeight T U m) (coefficients F G H) X
end Flat

/-- The identity comparison between the composite right weight and the outer weight
  pulled back along the partial index functor. -/
abbrev weightMap (X : (C × D) × E) :
    (flatWeight T U m).obj (op X) ⟶
      (weight U m).obj (op ((AssociatorRightTensor.product (C := C) T).obj X)) := 𝟙 _

/-- The whole original heterogeneous relative weight Hom square. -/
@[reassoc]
theorem weightMap_naturality (X Y : (C × D) × E) :
    MonoidalClosed.uncurry ((flatWeight T U m).map (op Y) (op X)) ≫ weightMap T U m X =
      (weightMap T U m Y ⊗ₘ (AssociatorRightTensor.product (C := C) T).map X Y) ≫
        MonoidalClosed.uncurry ((weight U m).map
          (op ((AssociatorRightTensor.product (C := C) T).obj Y))
          (op ((AssociatorRightTensor.product (C := C) T).obj X))) := by
  let P := AssociatorRightTensor.product (C := C) T
  let x : M := U.obj (P.obj X)
  let y : M := U.obj (P.obj Y)
  let Wx : V := x ⟶[V] m
  let Wy : V := y ⟶[V] m
  let R : V := x ⟶[V] y
  let l : (X ⟶[V] Y) ⟶ R := (flatIndex T U).map X Y
  let s : (X ⟶[V] Y) ⟶ (P.obj X ⟶[V] P.obj Y) := P.map X Y
  let u : (P.obj X ⟶[V] P.obj Y) ⟶ R := U.map (P.obj X) (P.obj Y)
  let w0 : Wy ⊗ (X ⟶[V] Y) ⟶ Wx := MonoidalClosed.uncurry ((flatWeight T U m).map (op Y) (op X))
  let w1 : Wy ⊗ (P.obj X ⟶[V] P.obj Y) ⟶ Wx := MonoidalClosed.uncurry ((weight U m).map (op (P.obj
    Y)) (op (P.obj X)))
  have hl : l = s ≫ u := rfl
  have hw0 : w0 = Wy ◁ l ≫ (β_ Wy R).hom ≫ eComp V x y m := weight_uncurry_map (flatIndex T U) m X Y
  have hw1 : w1 = Wy ◁ u ≫ (β_ Wy R).hom ≫ eComp V x y m := weight_uncurry_map U m (P.obj X) (P.obj
    Y)
  change w0 ≫ 𝟙 Wx = (𝟙 Wy ⊗ₘ s) ≫ w1
  rw [hw0, hw1]
  simp only [id_tensorHom, ← whiskerLeft_comp_assoc]
  rw [hl]
  exact Category.comp_id _

section Forward
variable [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T G H k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T G H k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T G H k) (EnrichedDayKernel.rightMap T G H k)]
  [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects U F (Output.functor T G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations U F (Output.functor T G H) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U F (Output.functor T G H) m)
    (EnrichedDayKernel.rightMap U F (Output.functor T G H) m)]

/-- Actual heterogeneous right flattening into the original chosen nested Day value. -/
def flatToNested : point T U F G H m ⟶ EnrichedDayKernel.obj U F (Output.functor T G H) m :=
  Enriched.weightedCoend.Transport.map (AssociatorRightTensor.product (C := C) T)
    (flatWeight T U m) (weight U m) (coefficients F G H) (F.externalTensor (Output.functor T G H))
    (weightMap T U m) (fun X => AssociatorRightTensor.coefficientMap T F G H X)
    (weightMap_naturality T U m) (AssociatorRightTensor.coefficientMap_naturality T F G H)

/-- Original flat generators retain the actual unchanged U weight and T identity-generator
  coefficient map. -/
@[reassoc]
theorem generator_flatToNested (X : (C × D) × E) :
    generator T U F G H m X ≫ flatToNested T U F G H m =
      (𝟙 (U.obj (X.1.1, T.obj (X.1.2, X.2)) ⟶[V] m) ⊗ₘ
        (𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator T G H (X.1.2, X.2))) ≫
          EnrichedDayKernel.gen U F (Output.functor T G H) m (X.1.1, T.obj (X.1.2, X.2)) :=
  Enriched.weightedCoend.Transport.ι_map (AssociatorRightTensor.product (C := C) T)
    (flatWeight T U m) (weight U m) (coefficients F G H) (F.externalTensor (Output.functor T G H))
    (weightMap T U m) (fun X => AssociatorRightTensor.coefficientMap T F G H X)
    (weightMap_naturality T U m) (AssociatorRightTensor.coefficientMap_naturality T F G H) X
end Forward

/-- The unchanged ordered heterogeneous triple of an original right nested generator. -/
abbrev triple (p : C × K) (a : D × E) : (C × D) × E := ((p.1, a.1), a.2)

/-- Original full U-weight precomposition at a fixed actual first index. -/
abbrev sliceBase (p : C × K) (a : D × E) :
    (weight U m).obj (op p) ⊗ (T.obj a ⟶[V] p.2) ⟶
      (weight U m).obj (op (p.1, T.obj a)) :=
  (weight U m).obj (op p) ◁
    (EnrichedFunctor.prodRightInclusion (V := V) (B := K) p.1).map (T.obj a) p.2 ≫
    MonoidalClosed.uncurry ((weight U m).map (op p) (op (p.1, T.obj a)))

/-- Contract the actual complete original T/U right word into its exact unchanged flat summand. -/
abbrev contractWord (p : C × K) (a : D × E) :
    AssociatorFaces.Right.objects T U G H F m p a ⟶ objects T U F G H m (triple p a) :=
  (weight U m).obj (op p) ◁
    (AssociatorRightContraction.frontHomIso (T.obj a ⟶[V] p.2) (F.obj p.1) (G.obj a.1 ⊗ H.obj
      a.2)).hom ≫
    (α_ ((weight U m).obj (op p)) (T.obj a ⟶[V] p.2) (F.obj p.1 ⊗ (G.obj a.1 ⊗ H.obj a.2))).inv ≫
    (sliceBase T U m p a ⊗ₘ 𝟙 (F.obj p.1 ⊗ (G.obj a.1 ⊗ H.obj a.2)))

section Factorization
variable [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T G H k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T G H k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T G H k) (EnrichedDayKernel.rightMap T G H k)]
  [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects U F (Output.functor T G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations U F (Output.functor T G H) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U F (Output.functor T G H) m)
    (EnrichedDayKernel.rightMap U F (Output.functor T G H) m)]

/-- The actual original heterogeneous nested generator factors through the actual flat contraction.
-/
@[reassoc]
theorem contractWord_generator_factorization (p : C × K) (a : D × E) :
    contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) ≫ flatToNested T U F G H m =
      AssociatorFaces.Right.nestedGenerator T U G H F m p a := by
  let x := T.obj a
  let B := F.obj p.1
  let A := G.obj a.1 ⊗ H.obj a.2
  let R : V := x ⟶[V] p.2
  let Y := EnrichedDayKernel.obj T G H p.2
  let X := EnrichedDayKernel.obj T G H x
  let u : A ⟶ X := AssociatorUnit.unitGenerator T G H a
  let g : R ⊗ A ⟶ Y := EnrichedDayKernel.gen T G H p.2 a
  let o : X ⊗ R ⟶ Y := MonoidalClosed.uncurry (Output.map T G H x p.2)
  have hd : R ◁ u ≫ (β_ R X).hom ≫ o = g := by
    have hm := Output.map_uncurry T G H x p.2
    change o = (β_ R X).inv ≫ MonoidalClosed.uncurry (Output.actionDesc T G H x p.2) at hm
    rw [hm]
    simp only [Iso.hom_inv_id_assoc]
    exact AssociatorUnit.unitGenerator_action T G H a p.2
  have hc := AssociatorRightContraction.leftSlice_condition (weight U m) F (Output.functor T G H)
    p.1 x p.2 u
  rw [generator_flatToNested]
  let Wb := (weight U m).obj (op p)
  let Wa := (weight U m).obj (op (p.1, x))
  let k : Wb ⊗ R ⟶ Wa := sliceBase T U m p a
  let N := EnrichedDayKernel.obj U F (Output.functor T G H) m
  let ga : Wa ⊗ (B ⊗ X) ⟶ N := EnrichedDayKernel.gen U F (Output.functor T G H) m (p.1, x)
  let gb : Wb ⊗ (B ⊗ Y) ⟶ N := EnrichedDayKernel.gen U F (Output.functor T G H) m p
  change (Wb ◁ (AssociatorRightContraction.frontHomIso R B A).hom ≫
      (α_ Wb R (B ⊗ A)).inv ≫ (k ⊗ₘ 𝟙 (B ⊗ A))) ≫ (𝟙 Wa ⊗ₘ (𝟙 B ⊗ₘ u)) ≫ ga = Wb ◁ (B ◁ g) ≫ gb
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  change Wb ◁ (AssociatorRightContraction.frontHomIso R B A).hom ≫
      (α_ Wb R (B ⊗ A)).inv ≫ (k ⊗ₘ (𝟙 B ⊗ₘ u)) ≫ ga =
        Wb ◁ (B ◁ (R ◁ u ≫ (β_ R X).hom ≫ o)) ≫ gb at hc
  rw [hd] at hc
  exact hc
end Factorization

omit [MonoidalClosed V] in
/-- The full fixed-first inclusion retains the literal original T/U flat index action. -/
@[reassoc]
theorem innerInclusion_flatIndex_map (e : C) (a b : D × E) :
    (AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e).map a b ≫
      (flatIndex T U).map ((e, a.1), a.2) ((e, b.1), b.2) =
    T.map a b ≫ (EnrichedFunctor.prodRightInclusion (V := V) (B := K) e).map (T.obj a) (T.obj b) ≫
      U.map (e, T.obj a) (e, T.obj b) := by
  let J := AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e
  let P := Associator.productAssociator (V := V) (A := C) (B := D) (C := E)
  let Q := prodEnrichedFunctor (EnrichedFunctor.id V C) T
  let r : (a ⟶[V] b) ⟶ (J.obj a ⟶[V] J.obj b) := J.map a b
  let f : (J.obj a ⟶[V] J.obj b) ⟶ ((e, a) ⟶[V] (e, b)) := P.map (J.obj a) (J.obj b)
  let g : ((e, a) ⟶[V] (e, b)) ⟶ ((e, T.obj a) ⟶[V] (e, T.obj b)) := Q.map (e, a) (e, b)
  let u : ((e, T.obj a) ⟶[V] (e, T.obj b)) ⟶ (U.obj (e, T.obj a) ⟶[V] U.obj (e, T.obj b)) :=
    U.map (e, T.obj a) (e, T.obj b)
  let i : (a ⟶[V] b) ⟶ ((e, a) ⟶[V] (e, b)) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := D × E) e).map a b
  let j : (T.obj a ⟶[V] T.obj b) ⟶ ((e, T.obj a) ⟶[V] (e, T.obj b)) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := K) e).map (T.obj a) (T.obj b)
  have hf : r ≫ f = i := AssociatorRightTensor.innerInclusion_product_map e a b
  have hg : i ≫ g = T.map a b ≫ j := AssociatorInclusion.leftInclusion_product_map T e a b
  change r ≫ ((f ≫ g) ≫ u) = T.map a b ≫ j ≫ u
  have h : r ≫ (f ≫ g) = T.map a b ≫ j := by rw [← Category.assoc, hf, hg]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ u) h

omit [MonoidalClosed V] in
/-- The full fixed-inner inclusion contracts the actual T identity before the original U map. -/
@[reassoc]
theorem outerInclusion_flatIndex_map (a : D × E) (e f : C) :
    (AssociatorRightTensor.outerInclusion (V := V) (C := C) a).map e f ≫
      (flatIndex T U).map ((e, a.1), a.2) ((f, a.1), a.2) =
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) (T.obj a)).map e f ≫
      U.map (e, T.obj a) (f, T.obj a) := by
  let R : V := e ⟶[V] f
  let P : V := a ⟶[V] a
  let x := T.obj a
  let Q : V := x ⟶[V] x
  let r := α_ R (a.1 ⟶[V] a.1) (a.2 ⟶[V] a.2)
  let i : 𝟙_ V ⟶ P := eId V a
  let t : P ⟶ Q := T.map a a
  let j : 𝟙_ V ⟶ Q := eId V x
  let u : R ⊗ Q ⟶ (U.obj (e, x) ⟶[V] U.obj (f, x)) := U.map (e, x) (f, x)
  change (((ρ_ R).inv ≫ (𝟙 R ⊗ₘ i)) ≫ r.inv) ≫ ((r.hom ≫ (𝟙 R ⊗ₘ t)) ≫ u) =
    ((ρ_ R).inv ≫ (𝟙 R ⊗ₘ j)) ≫ u
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id]
  have ht : i ≫ t = j := T.map_id a
  rw [ht]

/-- The entire original heterogeneous flat weight action on the fixed-first slice. -/
@[reassoc]
theorem innerInclusion_weight_action (e : C) (a b : D × E) :
    (flatWeight T U m).obj (op ((e, b.1), b.2)) ◁
      (AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e).map a b ≫
      MonoidalClosed.uncurry ((flatWeight T U m).map (op ((e, b.1), b.2)) (op ((e, a.1), a.2))) =
    (weight U m).obj (op (e, T.obj b)) ◁
      (T.map a b ≫ (EnrichedFunctor.prodRightInclusion (V := V) (B := K) e).map (T.obj a) (T.obj b))
        ≫
      MonoidalClosed.uncurry ((weight U m).map (op (e, T.obj b)) (op (e, T.obj a))) := by
  let Xa : (C × D) × E := ((e, a.1), a.2)
  let Xb : (C × D) × E := ((e, b.1), b.2)
  let x : M := U.obj (e, T.obj a)
  let y : M := U.obj (e, T.obj b)
  let Wb : V := y ⟶[V] m
  let R : V := x ⟶[V] y
  let j : (a ⟶[V] b) ⟶ (Xa ⟶[V] Xb) :=
    (AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e).map a b
  let l : (Xa ⟶[V] Xb) ⟶ R := (flatIndex T U).map Xa Xb
  let t : (a ⟶[V] b) ⟶ ((e, T.obj a) ⟶[V] (e, T.obj b)) :=
    T.map a b ≫ (EnrichedFunctor.prodRightInclusion (V := V) (B := K) e).map (T.obj a) (T.obj b)
  let u : ((e, T.obj a) ⟶[V] (e, T.obj b)) ⟶ (U.obj (e, T.obj a) ⟶[V] U.obj (e, T.obj b)) :=
    U.map (e, T.obj a) (e, T.obj b)
  have hm : j ≫ l = t ≫ u := by
    have h := innerInclusion_flatIndex_map T U e a b
    change j ≫ l = T.map a b ≫ (EnrichedFunctor.prodRightInclusion (V := V) (B := K) e).map
      (T.obj a) (T.obj b) ≫ u at h
    exact h.trans (Category.assoc _ _ _).symm
  let wl : Wb ⊗ (Xa ⟶[V] Xb) ⟶ (x ⟶[V] m) := MonoidalClosed.uncurry ((flatWeight T U m).map (op Xb)
    (op Xa))
  let wr : Wb ⊗ ((e, T.obj a) ⟶[V] (e, T.obj b)) ⟶ (x ⟶[V] m) :=
    MonoidalClosed.uncurry ((weight U m).map (op (e, T.obj b)) (op (e, T.obj a)))
  have hl : wl = Wb ◁ l ≫ (β_ Wb R).hom ≫ eComp V x y m := weight_uncurry_map (flatIndex T U) m Xa
    Xb
  have hr : wr = Wb ◁ u ≫ (β_ Wb R).hom ≫ eComp V x y m := weight_uncurry_map U m (e, T.obj a) (e,
    T.obj b)
  change Wb ◁ j ≫ wl = Wb ◁ t ≫ wr
  rw [hl, hr, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, hm]

/-- The entire original heterogeneous flat weight action with the last two index inputs fixed. -/
@[reassoc]
theorem outerInclusion_weight_action (a : D × E) (e f : C) :
    (flatWeight T U m).obj (op ((f, a.1), a.2)) ◁
      (AssociatorRightTensor.outerInclusion (V := V) (C := C) a).map e f ≫
      MonoidalClosed.uncurry ((flatWeight T U m).map (op ((f, a.1), a.2)) (op ((e, a.1), a.2))) =
    (weight U m).obj (op (f, T.obj a)) ◁
      (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) (T.obj a)).map e f ≫
      MonoidalClosed.uncurry ((weight U m).map (op (f, T.obj a)) (op (e, T.obj a))) := by
  let Xe : (C × D) × E := ((e, a.1), a.2)
  let Xf : (C × D) × E := ((f, a.1), a.2)
  let x := T.obj a
  let s : M := U.obj (e, x)
  let t : M := U.obj (f, x)
  let Wf : V := t ⟶[V] m
  let R : V := s ⟶[V] t
  let j : (e ⟶[V] f) ⟶ (Xe ⟶[V] Xf) := (AssociatorRightTensor.outerInclusion (V := V) (C := C)
    a).map e f
  let l : (Xe ⟶[V] Xf) ⟶ R := (flatIndex T U).map Xe Xf
  let k : (e ⟶[V] f) ⟶ ((e, x) ⟶[V] (f, x)) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) x).map e f
  let u : ((e, x) ⟶[V] (f, x)) ⟶ R := U.map (e, x) (f, x)
  have hm : j ≫ l = k ≫ u := outerInclusion_flatIndex_map T U a e f
  let wl : Wf ⊗ (Xe ⟶[V] Xf) ⟶ (s ⟶[V] m) := MonoidalClosed.uncurry ((flatWeight T U m).map (op Xf)
    (op Xe))
  let wr : Wf ⊗ ((e, x) ⟶[V] (f, x)) ⟶ (s ⟶[V] m) := MonoidalClosed.uncurry ((weight U m).map (op
    (f, x)) (op (e, x)))
  have hl : wl = Wf ◁ l ≫ (β_ Wf R).hom ≫ eComp V s t m := weight_uncurry_map (flatIndex T U) m Xe
    Xf
  have hr : wr = Wf ◁ u ≫ (β_ Wf R).hom ≫ eComp V s t m := weight_uncurry_map U m (e, x) (f, x)
  change Wf ◁ j ≫ wl = Wf ◁ k ≫ wr
  rw [hl, hr, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, hm]

/-- The original complete last-two-input action through the true fixed-first product inclusion. -/
@[reassoc]
theorem innerInclusion_coefficient_action (e : C) (a b : D × E) :
    ((AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e).map a b ⊗ₘ
      𝟙 (F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2))) ≫
      (β_ (((e, a.1), a.2) ⟶[V] ((e, b.1), b.2)) (F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2))).hom ≫
      MonoidalClosed.uncurry ((coefficients F G H).map ((e, a.1), a.2) ((e, b.1), b.2)) =
    (AssociatorRightContraction.frontHomIso (a ⟶[V] b) (F.obj e) (G.obj a.1 ⊗ H.obj a.2)).inv ≫
      F.obj e ◁
      ((β_ (a ⟶[V] b) (G.obj a.1 ⊗ H.obj a.2)).hom ≫ MonoidalClosed.uncurry ((G.externalTensor
        H).map a b)) := by
  let J := AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e
  let P := Associator.productAssociator (V := V) (A := C) (B := D) (C := E)
  let Q := F.externalTensor (G.externalTensor H)
  let R : V := a ⟶[V] b
  let S : V := J.obj a ⟶[V] J.obj b
  let S' : V := (e, a) ⟶[V] (e, b)
  let X := F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2)
  let Y := F.obj e ⊗ (G.obj b.1 ⊗ H.obj b.2)
  let j : R ⟶ S := J.map a b
  let p : S ⟶ S' := P.map (J.obj a) (J.obj b)
  let i : R ⟶ S' := (EnrichedFunctor.prodRightInclusion (V := V) (B := D × E) e).map a b
  let r : S' ⟶ (ihom X).obj Y := Q.map (e, a) (e, b)
  let l : S ⟶ (ihom X).obj Y := (coefficients F G H).map ((e, a.1), a.2) ((e, b.1), b.2)
  let q : X ⊗ S' ⟶ Y := MonoidalClosed.uncurry r
  have hm : j ≫ p = i := AssociatorRightTensor.innerInclusion_product_map e a b
  have hl : l = p ≫ r := rfl
  have hu : MonoidalClosed.uncurry l = X ◁ p ≫ q := by
    rw [hl]
    exact MonoidalClosed.uncurry_natural_left p r
  change (j ⊗ₘ 𝟙 X) ≫ (β_ S X).hom ≫ MonoidalClosed.uncurry l = _
  rw [hu]
  have hb := BraidedCategory.braiding_naturality_assoc j (𝟙 X) (X ◁ p ≫ q)
  rw [hb]
  simp only [id_tensorHom]
  rw [← whiskerLeft_comp_assoc, hm]
  have hc := AssociatorRightContraction.leftSlice_action F (G.externalTensor H) e a b (𝟙 (G.obj a.1
    ⊗ H.obj a.2))
  change (i ⊗ₘ (𝟙 (F.obj e) ⊗ₘ 𝟙 (G.obj a.1 ⊗ H.obj a.2))) ≫ (β_ S' X).hom ≫ q =
    (AssociatorRightContraction.frontHomIso R (F.obj e) (G.obj a.1 ⊗ H.obj a.2)).inv ≫ F.obj e ◁
      (R ◁ 𝟙 (G.obj a.1 ⊗ H.obj a.2) ≫ (β_ R (G.obj a.1 ⊗ H.obj a.2)).hom ≫ MonoidalClosed.uncurry
        ((G.externalTensor H).map a b)) at hc
  simp only [id_tensorHom_id, whiskerLeft_id, Category.id_comp] at hc
  have hn := BraidedCategory.braiding_naturality_assoc i (𝟙 X) q
  have hn' : (i ⊗ₘ 𝟙 X) ≫ (β_ S' X).hom ≫ q = (β_ R X).hom ≫ X ◁ i ≫ q := by simpa only
    [id_tensorHom] using hn
  exact hn'.symm.trans hc

/-- The original full first-input action through the true fixed-last-two product inclusion. -/
@[reassoc]
theorem outerInclusion_coefficient_action (a : D × E) (e f : C) :
    ((AssociatorRightTensor.outerInclusion (V := V) (C := C) a).map e f ⊗ₘ 𝟙 (F.obj e ⊗ (G.obj a.1 ⊗
      H.obj a.2))) ≫
      (β_ (((e, a.1), a.2) ⟶[V] ((f, a.1), a.2)) (F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2))).hom ≫
      MonoidalClosed.uncurry ((coefficients F G H).map ((e, a.1), a.2) ((f, a.1), a.2)) =
    (α_ (e ⟶[V] f) (F.obj e) (G.obj a.1 ⊗ H.obj a.2)).inv ≫
      (((β_ (e ⟶[V] f) (F.obj e)).hom ≫ MonoidalClosed.uncurry (F.map e f)) ⊗ₘ 𝟙 (G.obj a.1 ⊗ H.obj
        a.2)) := by
  let J := AssociatorRightTensor.outerInclusion (V := V) (C := C) a
  let P := Associator.productAssociator (V := V) (A := C) (B := D) (C := E)
  let Q := F.externalTensor (G.externalTensor H)
  let R : V := e ⟶[V] f
  let S : V := J.obj e ⟶[V] J.obj f
  let S' : V := (e, a) ⟶[V] (f, a)
  let X := F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2)
  let Y := F.obj f ⊗ (G.obj a.1 ⊗ H.obj a.2)
  let j : R ⟶ S := J.map e f
  let p : S ⟶ S' := P.map (J.obj e) (J.obj f)
  let i : R ⟶ S' := (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) a).map e f
  let r : S' ⟶ (ihom X).obj Y := Q.map (e, a) (f, a)
  let l : S ⟶ (ihom X).obj Y := (coefficients F G H).map ((e, a.1), a.2) ((f, a.1), a.2)
  let q : X ⊗ S' ⟶ Y := MonoidalClosed.uncurry r
  have hm : j ≫ p = i := AssociatorRightTensor.outerInclusion_product_map a e f
  have hl : l = p ≫ r := rfl
  have hu : MonoidalClosed.uncurry l = X ◁ p ≫ q := by
    rw [hl]
    exact MonoidalClosed.uncurry_natural_left p r
  change (j ⊗ₘ 𝟙 X) ≫ (β_ S X).hom ≫ MonoidalClosed.uncurry l = _
  rw [hu]
  have hb := BraidedCategory.braiding_naturality_assoc j (𝟙 X) (X ◁ p ≫ q)
  rw [hb]
  simp only [id_tensorHom]
  rw [← whiskerLeft_comp_assoc, hm]
  have hc := AssociatorContraction.rightSlice_action F (G.externalTensor H) a e f (𝟙 (F.obj e))
  change (i ⊗ₘ (𝟙 (F.obj e) ⊗ₘ 𝟙 (G.obj a.1 ⊗ H.obj a.2))) ≫ (β_ S' X).hom ≫ q =
    (α_ R (F.obj e) (G.obj a.1 ⊗ H.obj a.2)).inv ≫
      ((R ◁ 𝟙 (F.obj e) ≫ (β_ R (F.obj e)).hom ≫ MonoidalClosed.uncurry (F.map e f)) ⊗ₘ 𝟙 (G.obj a.1
        ⊗ H.obj a.2)) at hc
  simp only [id_tensorHom_id, whiskerLeft_id, Category.id_comp] at hc
  have hn := BraidedCategory.braiding_naturality_assoc i (𝟙 X) q
  have hn' : (i ⊗ₘ 𝟙 X) ≫ (β_ S' X).hom ≫ q = (β_ R X).hom ≫ X ◁ i ≫ q := by simpa only
    [id_tensorHom] using hn
  exact hn'.symm.trans hc

@[reassoc]
theorem sliceBase_inner (p : C × K) (a b : D × E) :
    (weight U m).obj (op p) ◁
        MonoidalClosed.uncurry ((weight T p.2).map (op b) (op a)) ≫
      sliceBase T U m p a =
    (α_ ((weight U m).obj (op p))
        (T.obj b ⟶[V] p.2) (a ⟶[V] b)).inv ≫
      (sliceBase T U m p b ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      ((flatWeight T U m).obj
          (op ((AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) p.1).obj
            b)) ◁
        (AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) p.1).map a b ≫
        MonoidalClosed.uncurry ((flatWeight T U m).map
          (op ((AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) p.1).obj
            b))
          (op ((AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) p.1).obj
            a)))) := by
  let W := weight U m
  let e := p.1
  let x := T.obj a
  let y := T.obj b
  let k := p.2
  let J := EnrichedFunctor.prodRightInclusion (V := V) (B := K) e
  let Z := W.obj (op p)
  let Wa := W.obj (op (e, x))
  let Wb := W.obj (op (e, y))
  let P : V := a ⟶[V] b
  let R : V := y ⟶[V] k
  let S : V := x ⟶[V] k
  let t : P ⟶ (x ⟶[V] y) := T.map a b
  let f : R ⟶ ((e, y) ⟶[V] p) := J.map y k
  let g : P ⟶ ((e, x) ⟶[V] (e, y)) := t ≫ J.map x y
  let j : S ⟶ ((e, x) ⟶[V] p) := J.map x k
  let wa : Z ⊗ ((e, x) ⟶[V] p) ⟶ Wa := MonoidalClosed.uncurry (W.map (op p) (op (e, x)))
  let wb : Z ⊗ ((e, y) ⟶[V] p) ⟶ Wb := MonoidalClosed.uncurry (W.map (op p) (op (e, y)))
  let w : Wb ⊗ ((e, x) ⟶[V] (e, y)) ⟶ Wa :=
    MonoidalClosed.uncurry (W.map (op (e, y)) (op (e, x)))
  let ka : Z ⊗ S ⟶ Wa := sliceBase T U m p a
  let kb : Z ⊗ R ⟶ Wb := sliceBase T U m p b
  let v : Wb ⊗ P ⟶ Wa := (flatWeight T U m).obj
      (op ((AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e).obj b)) ◁
      (AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e).map a b ≫
      MonoidalClosed.uncurry ((flatWeight T U m).map
        (op ((AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e).obj b))
        (op ((AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) e).obj a)))
  let tau : R ⊗ P ⟶ S :=
    MonoidalClosed.uncurry ((weight T k).map (op b) (op a))
  have htau : tau = R ◁ t ≫ (β_ R (x ⟶[V] y)).hom ≫ eComp V x y k :=
    weight_uncurry_map T k a b
  let c : R ⊗ P ⟶ ((e, x) ⟶[V] p) :=
    (f ⊗ₘ g) ≫ (β_ ((e, y) ⟶[V] p) ((e, x) ⟶[V] (e, y))).hom ≫
      eComp V (e, x) (e, y) p
  have hc : c = tau ≫ j := by
    have h := AssociatorInclusion.leftInclusion_precomposition e x y k t
    change c = R ◁ t ≫ (β_ R (x ⟶[V] y)).hom ≫ eComp V x y k ≫ j at h
    have h' : c = (R ◁ t ≫ (β_ R (x ⟶[V] y)).hom ≫ eComp V x y k) ≫ j := by
      simpa only [Category.assoc] using h
    exact h'.trans (congrArg (fun z => z ≫ j) htau.symm)
  have hv : v = Wb ◁ g ≫ w := innerInclusion_weight_action T U m e a b
  have hl : (α_ Z R P).inv ≫ (kb ⊗ₘ 𝟙 P) ≫ v =
      (α_ Z R P).inv ≫ (kb ⊗ₘ g) ≫ w := by
    rw [hv]
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  have hcomp := AssociatorContraction.weightAction_comp_maps W (e, x) (e, y) p f g
  change (α_ Z R P).inv ≫ (kb ⊗ₘ g) ≫ w = Z ◁ c ≫ wa at hcomp
  rw [hc] at hcomp
  have hr : Z ◁ (tau ≫ j) ≫ wa = Z ◁ tau ≫ ka := by
    change Z ◁ (tau ≫ j) ≫ wa = Z ◁ tau ≫ (Z ◁ j ≫ wa)
    simp only [whiskerLeft_comp, Category.assoc]
  change Z ◁ tau ≫ ka = (α_ Z R P).inv ≫ (kb ⊗ₘ 𝟙 P) ≫ v
  exact (hl.trans (hcomp.trans hr)).symm

variable [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]

@[reassoc]
theorem inner_balanced (p : C × K) (a b : D × E) :
    AssociatorFaces.Right.b0 T U G H F m p a b ≫
      contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) =
    AssociatorFaces.Right.b1 T U G H F m p a b ≫
      contractWord T U F G H m p b ≫ generator T U F G H m (triple p b) := by
  let J := AssociatorRightTensor.innerInclusion (V := V) (C := C) (D := D) (E := E) p.1
  let W := flatWeight T U m
  let Q := coefficients F G H
  let Z := (weight U m).obj (op p)
  let B := F.obj p.1
  let Aa := G.obj a.1 ⊗ H.obj a.2
  let Ab := G.obj b.1 ⊗ H.obj b.2
  let P : V := a ⟶[V] b
  let Ra : V := T.obj a ⟶[V] p.2
  let Rb : V := T.obj b ⟶[V] p.2
  let Wa := W.obj (op (J.obj a))
  let Wb := W.obj (op (J.obj b))
  let ka : Z ⊗ Ra ⟶ Wa := sliceBase T U m p a
  let kb : Z ⊗ Rb ⟶ Wb := sliceBase T U m p b
  let f : Rb ⊗ P ⟶ Ra := MonoidalClosed.uncurry ((weight T p.2).map (op b) (op a))
  let c : P ⊗ Aa ⟶ Ab := (β_ P Aa).hom ≫ MonoidalClosed.uncurry ((G.externalTensor H).map a b)
  let v : Wb ⊗ P ⟶ Wa := Wb ◁ J.map a b ≫ MonoidalClosed.uncurry (W.map (op (J.obj b)) (op (J.obj
    a)))
  let q : P ⊗ (B ⊗ Aa) ⟶ B ⊗ Ab :=
    (J.map a b ⊗ₘ 𝟙 (B ⊗ Aa)) ≫ (β_ (J.obj a ⟶[V] J.obj b) (B ⊗ Aa)).hom ≫
      MonoidalClosed.uncurry (Q.map (J.obj a) (J.obj b))
  let ga : Wa ⊗ (B ⊗ Aa) ⟶ point T U F G H m := generator T U F G H m (triple p a)
  let gb : Wb ⊗ (B ⊗ Ab) ⟶ point T U F G H m := generator T U F G H m (triple p b)
  let l : Wb ⊗ (P ⊗ (B ⊗ Aa)) ⟶ Wa ⊗ (B ⊗ Aa) := (α_ Wb P (B ⊗ Aa)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ Aa))
  let r : Wb ⊗ (P ⊗ (B ⊗ Aa)) ⟶ Wb ⊗ (B ⊗ Ab) := Wb ◁ q
  let pre := AssociatorRightContraction.frontRelationMap kb B P Aa
  have hweight : (α_ Z Rb P).inv ≫ (kb ⊗ₘ 𝟙 P) ≫ v = Z ◁ f ≫ ka :=
    (sliceBase_inner T U m p a b).symm
  have hq : q = (AssociatorRightContraction.frontHomIso P B Aa).inv ≫ B ◁ c :=
    innerInclusion_coefficient_action F G H p.1 a b
  have h0 := AssociatorRightContraction.frontMap_face0 f ka kb v hweight B Aa
  have h1 := AssociatorRightContraction.frontMap_face1 kb c B
  have hc := AssociatorRightContraction.index_condition J W Q a b
  change (α_ Wb P (B ⊗ Aa)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ Aa)) ≫ ga = r ≫ gb at hc
  have hc' : l ≫ ga = r ≫ gb := by simpa only [l, Category.assoc] using hc
  change Z ◁ (B ◁ ((α_ Rb P Aa).inv ≫ (f ⊗ₘ 𝟙 Aa))) ≫
      AssociatorRightContraction.frontMap ka B Aa = pre ≫ l at h0
  have h1' : Z ◁ (B ◁ (Rb ◁ c)) ≫ AssociatorRightContraction.frontMap kb B Ab = pre ≫ r := by
    change _ = pre ≫ Wb ◁ q
    rw [hq]
    exact h1
  change (Z ◁ (B ◁ ((α_ Rb P Aa).inv ≫ (f ⊗ₘ 𝟙 Aa)))) ≫
      AssociatorRightContraction.frontMap ka B Aa ≫ ga =
    Z ◁ (B ◁ (Rb ◁ c)) ≫ AssociatorRightContraction.frontMap kb B Ab ≫ gb
  have h0' := congrArg (fun z => z ≫ ga) h0
  have h1'' := congrArg (fun z => z ≫ gb) h1'
  have hb := congrArg (fun z => pre ≫ z) hc'
  simp only [Category.assoc] at h0' h1'' hb
  simpa only [AssociatorRightContraction.frontMap, Category.assoc] using
    h0'.trans (hb.trans h1''.symm)

/-- Compose the varying outer right Hom with the inner represented Hom, using the
  braiding to place the unchanged outer left Hom last. -/
abbrev outerInputBase (p q : C × K) (a : D × E) :
    (p ⟶[V] q) ⊗ (T.obj a ⟶[V] p.2) ⟶
      (T.obj a ⟶[V] q.2) ⊗ (p.1 ⟶[V] q.1) :=
  (α_ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2) (T.obj a ⟶[V] p.2)).hom ≫
    (p.1 ⟶[V] q.1) ◁ ((β_ (p.2 ⟶[V] q.2) (T.obj a ⟶[V] p.2)).hom ≫
      eComp V (T.obj a) p.2 q.2) ≫
    (β_ (p.1 ⟶[V] q.1) (T.obj a ⟶[V] q.2)).hom

@[reassoc]
theorem sliceBase_outer (p q : C × K) (a : D × E) :
    (α_ ((weight U m).obj (op q)) (p ⟶[V] q)
        (T.obj a ⟶[V] p.2)).inv ≫
      (MonoidalClosed.uncurry ((weight U m).map (op q) (op p)) ⊗ₘ
        𝟙 (T.obj a ⟶[V] p.2)) ≫ sliceBase T U m p a =
    (weight U m).obj (op q) ◁ outerInputBase T p q a ≫
      (α_ ((weight U m).obj (op q))
        (T.obj a ⟶[V] q.2) (p.1 ⟶[V] q.1)).inv ≫
      (sliceBase T U m q a ⊗ₘ 𝟙 (p.1 ⟶[V] q.1)) ≫
      ((flatWeight T U m).obj
          (op ((AssociatorRightTensor.outerInclusion (V := V) (C := C) a).obj q.1)) ◁
        (AssociatorRightTensor.outerInclusion (V := V) (C := C) a).map p.1 q.1 ≫
        MonoidalClosed.uncurry ((flatWeight T U m).map
          (op ((AssociatorRightTensor.outerInclusion (V := V) (C := C) a).obj q.1))
          (op ((AssociatorRightTensor.outerInclusion (V := V) (C := C) a).obj p.1)))) := by
  let W := weight U m
  let x := T.obj a
  let Z := W.obj (op q)
  let Wp := W.obj (op p)
  let Wa := W.obj (op (p.1, x))
  let Wb := W.obj (op (q.1, x))
  let E : V := p.1 ⟶[V] q.1
  let S : V := p.2 ⟶[V] q.2
  let R : V := x ⟶[V] p.2
  let R' : V := x ⟶[V] q.2
  let P : V := p ⟶[V] q
  let jp : R ⟶ ((p.1, x) ⟶[V] p) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := K) p.1).map x p.2
  let jq : R' ⟶ ((q.1, x) ⟶[V] q) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := K) q.1).map x q.2
  let je : E ⟶ ((p.1, x) ⟶[V] (q.1, x)) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) x).map p.1 q.1
  let wp : Z ⊗ P ⟶ Wp := MonoidalClosed.uncurry (W.map (op q) (op p))
  let wpa : Wp ⊗ ((p.1, x) ⟶[V] p) ⟶ Wa :=
    MonoidalClosed.uncurry (W.map (op p) (op (p.1, x)))
  let wqa : Z ⊗ ((p.1, x) ⟶[V] q) ⟶ Wa :=
    MonoidalClosed.uncurry (W.map (op q) (op (p.1, x)))
  let wqb : Z ⊗ ((q.1, x) ⟶[V] q) ⟶ Wb :=
    MonoidalClosed.uncurry (W.map (op q) (op (q.1, x)))
  let wba : Wb ⊗ ((p.1, x) ⟶[V] (q.1, x)) ⟶ Wa :=
    MonoidalClosed.uncurry (W.map (op (q.1, x)) (op (p.1, x)))
  let kp : Wp ⊗ R ⟶ Wa := sliceBase T U m p a
  let kq : Z ⊗ R' ⟶ Wb := sliceBase T U m q a
  let v : Wb ⊗ E ⟶ Wa := (flatWeight T U m).obj
      (op ((AssociatorRightTensor.outerInclusion (V := V) (C := C) a).obj q.1)) ◁
      (AssociatorRightTensor.outerInclusion (V := V) (C := C) a).map p.1 q.1 ≫
      MonoidalClosed.uncurry ((flatWeight T U m).map
        (op ((AssociatorRightTensor.outerInclusion (V := V) (C := C) a).obj q.1))
        (op ((AssociatorRightTensor.outerInclusion (V := V) (C := C) a).obj p.1)))
  let h : S ⊗ R ⟶ R' := (β_ S R).hom ≫ eComp V x p.2 q.2
  let s : P ⊗ R ⟶ R' ⊗ E := outerInputBase T p q a
  change (α_ Z P R).inv ≫ (wp ⊗ₘ 𝟙 R) ≫ kp =
    Z ◁ s ≫ (α_ Z R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v
  let c1 : P ⊗ R ⟶ E ⊗ R' := (α_ E S R).hom ≫ E ◁ h
  let c0 : P ⊗ R ⟶ ((p.1, x) ⟶[V] q) :=
    (𝟙 P ⊗ₘ jp) ≫ (β_ P ((p.1, x) ⟶[V] p)).hom ≫ eComp V (p.1, x) p q
  have hc0 : c0 = c1 := by
    have hf := AssociatorRightContraction.leftInclusion_full_comp (V := V) p.1 q.1 x p.2 q.2
    change (jp ⊗ₘ 𝟙 P) ≫ eComp V (p.1, x) p q =
      (AssociatorRightContraction.frontHomIso R E S).inv ≫ E ◁ eComp V x p.2 q.2 at hf
    have hn := BraidedCategory.braiding_naturality_assoc (𝟙 P) jp (eComp V (p.1, x) p q)
    change (𝟙 P ⊗ₘ jp) ≫ (β_ P ((p.1, x) ⟶[V] p)).hom ≫ eComp V (p.1, x) p q =
      (β_ P R).hom ≫ (jp ⊗ₘ 𝟙 P) ≫ eComp V (p.1, x) p q at hn
    change c0 = _ at hn
    rw [hf] at hn
    have hw := AssociatorRightContraction.productWeightWord E S R
    change (β_ P R).hom ≫ (AssociatorRightContraction.frontHomIso R E S).inv =
      (α_ E S R).hom ≫ E ◁ (β_ S R).hom at hw
    have hn' : c0 = ((β_ P R).hom ≫ (AssociatorRightContraction.frontHomIso R E S).inv) ≫
        E ◁ eComp V x p.2 q.2 := by simpa only [Category.assoc] using hn
    rw [hw] at hn'
    simpa only [c1, h, whiskerLeft_comp, Category.assoc] using hn'
  have h0 := AssociatorContraction.weightAction_comp_maps W (p.1, x) p q (𝟙 P) jp
  simp only [whiskerLeft_id, Category.id_comp] at h0
  change (α_ Z P R).inv ≫ (wp ⊗ₘ jp) ≫ wpa = Z ◁ c0 ≫ wqa at h0
  have h0' : (α_ Z P R).inv ≫ (wp ⊗ₘ 𝟙 R) ≫ kp = Z ◁ c1 ≫ wqa := by
    rw [← hc0]
    change (α_ Z P R).inv ≫ (wp ⊗ₘ 𝟙 R) ≫ (Wp ◁ jp ≫ wpa) = Z ◁ c0 ≫ wqa
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
    simpa only [id_tensorHom] using h0
  have hv : v = Wb ◁ je ≫ wba := outerInclusion_weight_action T U m a p.1 q.1
  let c2 : R' ⊗ E ⟶ ((p.1, x) ⟶[V] q) :=
    (jq ⊗ₘ je) ≫ (β_ ((q.1, x) ⟶[V] q) ((p.1, x) ⟶[V] (q.1, x))).hom ≫
      eComp V (p.1, x) (q.1, x) q
  have hc2 : c2 = (β_ R' E).hom := by
    have hn := BraidedCategory.braiding_naturality_assoc jq je (eComp V (p.1, x) (q.1, x) q)
    change c2 = (β_ R' E).hom ≫ (je ⊗ₘ jq) ≫ eComp V (p.1, x) (q.1, x) q at hn
    have hc := AssociatorContraction.rightThenLeft_comp (V := V) p.1 q.1 x q.2
    change (je ⊗ₘ jq) ≫ eComp V (p.1, x) (q.1, x) q = 𝟙 (E ⊗ R') at hc
    rw [hc, Category.comp_id] at hn
    exact hn
  have h1 := AssociatorContraction.weightAction_comp_maps W (p.1, x) (q.1, x) q jq je
  change (α_ Z R' E).inv ≫ (kq ⊗ₘ je) ≫ wba = Z ◁ c2 ≫ wqa at h1
  have h1' : (α_ Z R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v = Z ◁ (β_ R' E).hom ≫ wqa := by
    rw [hv]
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
    rw [hc2] at h1
    simpa only [id_tensorHom] using h1
  have hs : s = c1 ≫ (β_ E R').hom := by
    change (α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom =
      ((α_ E S R).hom ≫ E ◁ h) ≫ (β_ E R').hom
    exact (Category.assoc _ _ _).symm
  have hh := congrArg (fun z => Z ◁ s ≫ z) h1'
  have hc : Z ◁ s ≫ Z ◁ (β_ R' E).hom ≫ wqa = Z ◁ c1 ≫ wqa := by
    rw [← whiskerLeft_comp_assoc, hs]
    simp only [Category.assoc, SymmetricCategory.symmetry, Category.comp_id]
  change (α_ Z P R).inv ≫ (wp ⊗ₘ 𝟙 R) ≫ kp =
    Z ◁ s ≫ (α_ Z R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v
  exact h0'.trans (hc.symm.trans hh.symm)

@[reassoc]
theorem outer_balanced (p q : C × K) (a : D × E) :
    AssociatorFaces.Right.a0 T U G H F m p q a ≫
      contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) =
    AssociatorFaces.Right.a1 T U G H F m p q a ≫
      contractWord T U F G H m q a ≫ generator T U F G H m (triple q a) := by
  let J := AssociatorRightTensor.outerInclusion (V := V) (C := C) a
  let W := flatWeight T U m
  let Q := coefficients F G H
  let Z := (weight U m).obj (op q)
  let Wold := (weight U m).obj (op p)
  let x := T.obj a
  let E : V := p.1 ⟶[V] q.1
  let S : V := p.2 ⟶[V] q.2
  let R : V := x ⟶[V] p.2
  let R' : V := x ⟶[V] q.2
  let B := F.obj p.1
  let B' := F.obj q.1
  let A := G.obj a.1 ⊗ H.obj a.2
  let Wa := W.obj (op (J.obj p.1))
  let Wb := W.obj (op (J.obj q.1))
  let w : Z ⊗ (E ⊗ S) ⟶ Wold := MonoidalClosed.uncurry ((weight U m).map (op q) (op p))
  let kp : Wold ⊗ R ⟶ Wa := sliceBase T U m p a
  let kq : Z ⊗ R' ⟶ Wb := sliceBase T U m q a
  let h : S ⊗ R ⟶ R' := (β_ S R).hom ≫ eComp V x p.2 q.2
  let b : E ⊗ B ⟶ B' := AssociatorFaces.Right.coefficientAction F p q
  let v : Wb ⊗ E ⟶ Wa := Wb ◁ J.map p.1 q.1 ≫ MonoidalClosed.uncurry (W.map (op (J.obj q.1)) (op
    (J.obj p.1)))
  let c : E ⊗ (B ⊗ A) ⟶ B' ⊗ A := (J.map p.1 q.1 ⊗ₘ 𝟙 (B ⊗ A)) ≫
    (β_ (J.obj p.1 ⟶[V] J.obj q.1) (B ⊗ A)).hom ≫ MonoidalClosed.uncurry (Q.map (J.obj p.1) (J.obj
      q.1))
  let ga : Wa ⊗ (B ⊗ A) ⟶ point T U F G H m :=
    generator T U F G H m (triple p a)
  let gb : Wb ⊗ (B' ⊗ A) ⟶ point T U F G H m :=
    generator T U F G H m (triple q a)
  let l : Wb ⊗ (E ⊗ (B ⊗ A)) ⟶ Wa ⊗ (B ⊗ A) := (α_ Wb E (B ⊗ A)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ A))
  let r : Wb ⊗ (E ⊗ (B ⊗ A)) ⟶ Wb ⊗ (B' ⊗ A) := Wb ◁ c
  let pre := AssociatorRightContraction.outerRelationMap kq h E B A
  have hw : (α_ Z (E ⊗ S) R).inv ≫ (w ⊗ₘ 𝟙 R) ≫ kp =
      Z ◁ ((α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom) ≫
        (α_ Z R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v := sliceBase_outer T U m p q a
  have hc : c = (α_ E B A).inv ≫ (b ⊗ₘ 𝟙 A) := outerInclusion_coefficient_action F G H a p.1 q.1
  have h0 := AssociatorRightContraction.frontMap_outerWeight_balance w kp kq h v hw B A
  have h1 := AssociatorRightContraction.frontMap_outerCoefficient (A := A) kq h b
  have hout := AssociatorRightContraction.outputAction_tensor x p.2 q.2 A
  have hb := AssociatorRightContraction.index_condition J W Q p.1 q.1
  change (α_ Wb E (B ⊗ A)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ A)) ≫ ga = r ≫ gb at hb
  have hb' : l ≫ ga = r ≫ gb := by simpa only [l, Category.assoc] using hb
  have h0' : (α_ Z (E ⊗ S) (B ⊗ (R ⊗ A))).inv ≫
      (w ⊗ₘ 𝟙 (B ⊗ (R ⊗ A))) ≫ AssociatorRightContraction.frontMap kp B A = pre ≫ l := by
    simpa only [pre, AssociatorRightContraction.outerRelationMap,
      AssociatorRightContraction.frontMap, l, Category.assoc] using h0
  have h1' : Z ◁ (tensorμ E S B (R ⊗ A) ≫ (b ⊗ₘ Output.outputAction x p.2 q.2 A)) ≫
      AssociatorRightContraction.frontMap kq B' A = pre ≫ r := by
    rw [hout]
    change _ = pre ≫ Wb ◁ c
    rw [hc]
    exact h1
  change ((α_ Z (E ⊗ S) (B ⊗ (R ⊗ A))).inv ≫
      (w ⊗ₘ 𝟙 (B ⊗ (R ⊗ A)))) ≫ (AssociatorRightContraction.frontMap kp B A ≫ ga) =
    Z ◁ (tensorμ E S B (R ⊗ A) ≫ (b ⊗ₘ Output.outputAction x p.2 q.2 A)) ≫
      (AssociatorRightContraction.frontMap kq B' A ≫ gb)
  simp only [Category.assoc]
  have hh0 := congrArg (fun z => z ≫ ga) h0'
  have hh1 := congrArg (fun z => z ≫ gb) h1'
  have hh := congrArg (fun z => pre ≫ z) hb'
  simp only [Category.assoc] at hh0 hh1 hh
  simpa only [AssociatorRightContraction.frontMap, Category.assoc] using
    hh0.trans (hh.trans hh1.symm)

/-- The actual K identity is sent to the original C×K identity before the full U-weight action. -/
@[reassoc]
theorem sliceBase_identity (e : C) (a : D × E) :
    (ρ_ ((weight U m).obj (op (e, T.obj a)))).inv ≫
      (𝟙 ((weight U m).obj (op (e, T.obj a))) ⊗ₘ eId V (T.obj a)) ≫
      sliceBase T U m (e, T.obj a) a = 𝟙 ((weight U m).obj (op (e, T.obj a))) := by
  let x := T.obj a
  let p : C × K := (e, x)
  let W := weight U m
  let Z := W.obj (op p)
  let j : (x ⟶[V] x) ⟶ (p ⟶[V] p) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := K) e).map x x
  let w : Z ⊗ (p ⟶[V] p) ⟶ Z := MonoidalClosed.uncurry (W.map (op p) (op p))
  have hj : eId V x ≫ j = eId V p := (EnrichedFunctor.prodRightInclusion (V := V) (B := K) e).map_id
    x
  have hi := AssociatorRightContraction.action_identity W (op p)
  change (ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ eId V p) ≫ w = 𝟙 Z at hi
  change (ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ eId V x) ≫ (Z ◁ j ≫ w) = 𝟙 Z
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  rw [hj]
  exact hi

/-- Insert the original inner K identity into the exact original heterogeneous nested word. -/
abbrev identityWord (X : (C × D) × E) : objects T U F G H m X ⟶
    AssociatorFaces.Right.objects T U G H F m (X.1.1, T.obj (X.1.2, X.2)) (X.1.2, X.2) :=
  ((weight U m).obj (op (X.1.1, T.obj (X.1.2, X.2)))) ◁
    (F.obj X.1.1 ◁ AssociatorUnit.identityInsert (T.obj (X.1.2, X.2)) (G.obj X.1.2 ⊗ H.obj X.2))

omit [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)] in
/-- Original identity insertion and contraction are the full identity on the unchanged flat summand.
-/
@[reassoc]
theorem identityWord_contractWord (X : (C × D) × E) :
    identityWord T U F G H m X ≫ contractWord T U F G H m
        (X.1.1, T.obj (X.1.2, X.2)) (X.1.2, X.2) = 𝟙 (objects T U F G H m X) := by
  let a : D × E := (X.1.2, X.2)
  let x := T.obj a
  let p : C × K := (X.1.1, x)
  let Z := (weight U m).obj (op p)
  let B := F.obj X.1.1
  let A := G.obj X.1.2 ⊗ H.obj X.2
  let k : Z ⊗ (x ⟶[V] x) ⟶ Z := sliceBase T U m p a
  change Z ◁ (B ◁ AssociatorUnit.identityInsert x A) ≫ AssociatorRightContraction.frontMap k B A = 𝟙
    (Z ⊗ (B ⊗ A))
  exact AssociatorRightContraction.frontMap_identity (eId V x) k (sliceBase_identity T U m X.1.1 a)
    B A


variable
  [HasCoproduct (AssociatorPresentation.Right.simultaneousObjects T U G H F m)]
  [HasCoproduct (AssociatorPresentation.Right.simultaneousRelations T U G H F m)]
  [HasCoequalizer (AssociatorPresentation.Right.simultaneousLeftMap T U G H F m)
    (AssociatorPresentation.Right.simultaneousRightMap T U G H F m)]

/-- Actual descent through the literal original heterogeneous outer and inner relation Sum. -/
def simultaneousDesc : AssociatorPresentation.Right.simultaneousPoint T U G H F m ⟶ point T U F G H
  m := by
  let objs : (C × K) × (D × E) → V := AssociatorPresentation.Right.simultaneousObjects T U G H F m
  let family : ∀ pi, objs pi ⟶ point T U F G H m := fun pi =>
    contractWord T U F G H m pi.1 pi.2 ≫ generator T U F G H m (triple pi.1 pi.2)
  refine coequalizer.desc (Sigma.desc (f := objs) family) ?_
  apply Sigma.hom_ext
  intro r
  cases r with
  | inl pqi =>
    simp only [AssociatorPresentation.Right.simultaneousLeftMap,
      AssociatorPresentation.Right.simultaneousRightMap, Sigma.ι_comp_desc_assoc]
    change ((AssociatorFaces.Right.a0 T U G H F m pqi.1.1 pqi.1.2 pqi.2 ≫
      Sigma.ι objs (pqi.1.1, pqi.2)) ≫ Sigma.desc (f := objs) family) =
      ((AssociatorFaces.Right.a1 T U G H F m pqi.1.1 pqi.1.2 pqi.2 ≫
        Sigma.ι objs (pqi.1.2, pqi.2)) ≫ Sigma.desc (f := objs) family)
    let l := AssociatorFaces.Right.a0 T U G H F m pqi.1.1 pqi.1.2 pqi.2
    let r := AssociatorFaces.Right.a1 T U G H F m pqi.1.1 pqi.1.2 pqi.2
    have hl : (l ≫ Sigma.ι objs (pqi.1.1, pqi.2)) ≫ Sigma.desc (f := objs) family = l ≫ family
      (pqi.1.1, pqi.2) :=
      (Category.assoc l (Sigma.ι objs (pqi.1.1, pqi.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => l ≫ z) (Sigma.ι_comp_desc (f := objs) family (pqi.1.1, pqi.2)))
    have hr : (r ≫ Sigma.ι objs (pqi.1.2, pqi.2)) ≫ Sigma.desc (f := objs) family = r ≫ family
      (pqi.1.2, pqi.2) :=
      (Category.assoc r (Sigma.ι objs (pqi.1.2, pqi.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => r ≫ z) (Sigma.ι_comp_desc (f := objs) family (pqi.1.2, pqi.2)))
    have hb : l ≫ family (pqi.1.1, pqi.2) = r ≫ family (pqi.1.2, pqi.2) := outer_balanced T U F G H
      m pqi.1.1 pqi.1.2 pqi.2
    exact hl.trans (hb.trans hr.symm)
  | inr pij =>
    simp only [AssociatorPresentation.Right.simultaneousLeftMap,
      AssociatorPresentation.Right.simultaneousRightMap, Sigma.ι_comp_desc_assoc]
    change ((AssociatorFaces.Right.b0 T U G H F m pij.1 pij.2.1 pij.2.2 ≫ Sigma.ι objs (pij.1,
      pij.2.1)) ≫
      Sigma.desc (f := objs) family) = ((AssociatorFaces.Right.b1 T U G H F m pij.1 pij.2.1 pij.2.2
        ≫
        Sigma.ι objs (pij.1, pij.2.2)) ≫ Sigma.desc (f := objs) family)
    let l := AssociatorFaces.Right.b0 T U G H F m pij.1 pij.2.1 pij.2.2
    let r := AssociatorFaces.Right.b1 T U G H F m pij.1 pij.2.1 pij.2.2
    have hl : (l ≫ Sigma.ι objs (pij.1, pij.2.1)) ≫ Sigma.desc (f := objs) family = l ≫ family
      (pij.1, pij.2.1) :=
      (Category.assoc l (Sigma.ι objs (pij.1, pij.2.1)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => l ≫ z) (Sigma.ι_comp_desc (f := objs) family (pij.1, pij.2.1)))
    have hr : (r ≫ Sigma.ι objs (pij.1, pij.2.2)) ≫ Sigma.desc (f := objs) family = r ≫ family
      (pij.1, pij.2.2) :=
      (Category.assoc r (Sigma.ι objs (pij.1, pij.2.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => r ≫ z) (Sigma.ι_comp_desc (f := objs) family (pij.1, pij.2.2)))
    have hb : l ≫ family (pij.1, pij.2.1) = r ≫ family (pij.1, pij.2.2) := inner_balanced T U F G H
      m pij.1 pij.2.1 pij.2.2
    exact hl.trans (hb.trans hr.symm)

@[reassoc]
theorem simultaneousProjection_simultaneousDesc (p : C × K) (a : D × E) :
    AssociatorPresentation.Right.simultaneousProjection T U G H F m p a ≫ simultaneousDesc T U F G H
      m =
      contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) := by
  simp only [AssociatorPresentation.Right.simultaneousProjection, simultaneousDesc,
    Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

section Comparison
variable
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T G H k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T G H k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T G H k) (EnrichedDayKernel.rightMap T G H k)]
  [HasCoproduct (EnrichedDayKernel.objects U F (Output.functor T G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations U F (Output.functor T G H) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U F (Output.functor T G H) m)
    (EnrichedDayKernel.rightMap U F (Output.functor T G H) m)]

omit [HasCoproduct (AssociatorPresentation.Right.simultaneousObjects T U G H F m)]
  [HasCoproduct (AssociatorPresentation.Right.simultaneousRelations T U G H F m)]
  [HasCoequalizer (AssociatorPresentation.Right.simultaneousLeftMap T U G H F m)
    (AssociatorPresentation.Right.simultaneousRightMap T U G H F m)] in
/-- The actual forward map is precisely the original nested generator after original identity
  insertion. -/
@[reassoc]
theorem generator_flatToNested_identity (X : (C × D) × E) :
    generator T U F G H m X ≫ flatToNested T U F G H m = identityWord T U F G H m X ≫
      AssociatorFaces.Right.nestedGenerator T U G H F m (X.1.1, T.obj (X.1.2, X.2)) (X.1.2, X.2) :=
        by
  rw [generator_flatToNested]
  let p : C × K := (X.1.1, T.obj (X.1.2, X.2))
  let a : D × E := (X.1.2, X.2)
  let Z := (weight U m).obj (op p)
  let B := F.obj X.1.1
  let A := G.obj X.1.2 ⊗ H.obj X.2
  let x := T.obj a
  let i : A ⟶ (x ⟶[V] x) ⊗ A := AssociatorUnit.identityInsert x A
  let Y := EnrichedDayKernel.obj T G H x
  let N := EnrichedDayKernel.obj U F (Output.functor T G H) m
  let g : (x ⟶[V] x) ⊗ A ⟶ Y := EnrichedDayKernel.gen T G H x a
  let h : Z ⊗ (B ⊗ Y) ⟶ N := EnrichedDayKernel.gen U F (Output.functor T G H) m p
  change (𝟙 Z ⊗ₘ (𝟙 B ⊗ₘ (i ≫ g))) ≫ h = Z ◁ (B ◁ i) ≫ (Z ◁ (B ◁ g) ≫ h)
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]

variable
  [∀ p : C × K, HasCoproduct (AssociatorFaces.Right.objects T U G H F m p)]
  [∀ p : C × K, HasCoproduct (AssociatorFaces.Right.innerRelations T U G H F m p)]
  [∀ p : C × K, HasCoequalizer (AssociatorFaces.Right.innerLeftMap T U G H F m p)
    (AssociatorFaces.Right.innerRightMap T U G H F m p)]
  [∀ pq : (C × K) × (C × K), HasCoproduct (AssociatorPresentation.Right.relationObjects T U G H F m
    pq)]
  [∀ pq : (C × K) × (C × K), HasCoproduct (AssociatorPresentation.Right.relationRelations T U G H F
    m pq)]
  [∀ pq : (C × K) × (C × K), HasCoequalizer (AssociatorPresentation.Right.relationLeftMap T U G H F
    m pq)
    (AssociatorPresentation.Right.relationRightMap T U G H F m pq)]
  [HasCoproduct (AssociatorPresentation.Right.innerObjects T U G H F m)]
  [HasCoproduct (AssociatorPresentation.Right.outerRelations T U G H F m)]
  [HasCoequalizer (AssociatorPresentation.Right.outerLeftMap T U G H F m)
    (AssociatorPresentation.Right.outerRightMap T U G H F m)]

/-- Actual original heterogeneous right nested Day value to its unchanged selected composite-index
  flat coend. -/
def nestedToFlat : EnrichedDayKernel.obj U F (Output.functor T G H) m ⟶ point T U F G H m :=
  (AssociatorNested.Right.simultaneousIso T U G H F m).hom ≫ simultaneousDesc T U F G H m

@[reassoc]
theorem nestedGenerator_nestedToFlat (p : C × K) (a : D × E) :
    AssociatorFaces.Right.nestedGenerator T U G H F m p a ≫ nestedToFlat T U F G H m =
      contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) := by
  simp only [nestedToFlat, ← Category.assoc]
  rw [AssociatorNested.Right.nestedGenerator_simultaneousIso_hom,
    simultaneousProjection_simultaneousDesc]
  simp only [contractWord, Category.assoc]

@[reassoc]
theorem nestedToFlat_flatToNested : nestedToFlat T U F G H m ≫ flatToNested T U F G H m =
    𝟙 (EnrichedDayKernel.obj U F (Output.functor T G H) m) := by
  apply AssociatorNested.Right.hom_ext T U G H F m
  intro p a
  rw [← Category.assoc, nestedGenerator_nestedToFlat]
  simpa only [Category.assoc, Category.comp_id] using contractWord_generator_factorization T U F G H
    m p a

@[reassoc]
theorem flatToNested_nestedToFlat : flatToNested T U F G H m ≫ nestedToFlat T U F G H m = 𝟙 (point T
  U F G H m) := by
  apply Enriched.weightedCoend.hom_ext (flatWeight T U m) (coefficients F G H)
  intro X
  rcases X with ⟨⟨e, g⟩, h⟩
  have hx := generator_flatToNested_identity T U F G H m ((e, g), h)
  have hn := nestedGenerator_nestedToFlat T U F G H m (e, T.obj (g, h)) (g, h)
  have hi := identityWord_contractWord T U F G H m ((e, g), h)
  rw [← Category.assoc, hx, Category.assoc, hn, ← Category.assoc, hi]
  simp only [Category.id_comp, Category.comp_id]

/-- Actual heterogeneous right comparison, with both true maps and proved inverse equations. -/
def iso : point T U F G H m ≅ EnrichedDayKernel.obj U F (Output.functor T G H) m where
  hom := flatToNested T U F G H m
  inv := nestedToFlat T U F G H m
  hom_inv_id := flatToNested_nestedToFlat T U F G H m
  inv_hom_id := nestedToFlat_flatToNested T U F G H m

@[reassoc]
theorem generator_iso_hom (X : (C × D) × E) :
    generator T U F G H m X ≫ (iso T U F G H m).hom =
      (𝟙 (U.obj (X.1.1, T.obj (X.1.2, X.2)) ⟶[V] m) ⊗ₘ
        (𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator T G H (X.1.2, X.2))) ≫
          EnrichedDayKernel.gen U F (Output.functor T G H) m (X.1.1, T.obj (X.1.2, X.2)) :=
            generator_flatToNested T U F G H m X

@[reassoc]
theorem nestedGenerator_iso_inv (p : C × K) (a : D × E) :
    AssociatorFaces.Right.nestedGenerator T U G H F m p a ≫ (iso T U F G H m).inv =
      contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) :=
        nestedGenerator_nestedToFlat T U F G H m p a
end Comparison
end CategoryTheory.EnrichedDayKernel.AssociatorRightGeneral
