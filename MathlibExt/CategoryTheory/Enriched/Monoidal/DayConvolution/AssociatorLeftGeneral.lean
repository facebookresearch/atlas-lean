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
# Associator Left General

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uE uK uM
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorLeftGeneral
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C] {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E] {K : Type uK} [EnrichedCategory V K]
  {M : Type uM} [EnrichedCategory V M]
attribute [local instance] Enriched.prodCategory
variable (T : EnrichedFunctor V (C × D) K) (U : EnrichedFunctor V (K × E) M)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (H : EnrichedFunctor V E V) (m : M)

/-- The literal original left triple index, with the full unaltered product Hom. -/
abbrev product : EnrichedFunctor V ((C × D) × E) (K × E) :=
  prodEnrichedFunctor T (EnrichedFunctor.id V E)
/-- The enriched composite `(c, d, e) ↦ U(T(c, d), e)`. -/
abbrev flatIndex : EnrichedFunctor V ((C × D) × E) M := (product T).comp V U
/-- The represented weight at `m` for the composite left index functor. -/
abbrev flatWeight : EnrichedFunctor V ((C × D) × E)ᵒᵖ V := weight (flatIndex T U) m
/-- The left-associated external coefficient tensor `(F ⊗ G) ⊗ H`. -/
abbrev coefficients : EnrichedFunctor V ((C × D) × E) V := (F.externalTensor G).externalTensor H
/-- The object summands of the flat left weighted coend. -/
abbrev objects : (C × D) × E → V := Enriched.weightedCoend.objects (flatWeight T U m) (coefficients
  F G H)
/-- The relation summands of the flat left weighted coend, indexed by pairs of triples. -/
abbrev relations : ((C × D) × E) × ((C × D) × E) → V :=
  Enriched.weightedCoend.relations (flatWeight T U m) (coefficients F G H)
section Flat
variable [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
/-- The flat left coend relation map induced by the contravariant weight action. -/
abbrev map0 := Enriched.weightedCoend.leftMap (flatWeight T U m) (coefficients F G H)
/-- The flat left coend relation map induced by the covariant coefficient action. -/
abbrev map1 := Enriched.weightedCoend.rightMap (flatWeight T U m) (coefficients F G H)
variable [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]
/-- The chosen weighted coend of the composite left weight and external coefficients. -/
abbrev point : V := Enriched.weightedCoend (flatWeight T U m) (coefficients F G H)
/-- The canonical map from a flat left object summand to its chosen weighted coend. -/
abbrev generator (X : (C × D) × E) : objects T U F G H m X ⟶ point T U F G H m :=
  Enriched.weightedCoend.ι (flatWeight T U m) (coefficients F G H) X
end Flat
/-- The identity comparison between the composite left weight and the outer weight
  pulled back along the partial index functor. -/
abbrev weightMap (X : (C × D) × E) : (flatWeight T U m).obj (op X) ⟶
    (weight U m).obj (op ((product T).obj X)) := 𝟙 _

/-- Both original relative full weight maps agree on every three-input Hom. -/
@[reassoc]
theorem weightMap_naturality (X Y : (C × D) × E) :
    MonoidalClosed.uncurry ((flatWeight T U m).map (op Y) (op X)) ≫ weightMap T U m X =
      (weightMap T U m Y ⊗ₘ (product T).map X Y) ≫
        MonoidalClosed.uncurry ((weight U m).map (op ((product T).obj Y)) (op ((product T).obj X)))
          := by
  let P : EnrichedFunctor V ((C × D) × E) (K × E) := product T
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
variable [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects U (Output.functor T F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations U (Output.functor T F G) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U (Output.functor T F G) H m)
    (EnrichedDayKernel.rightMap U (Output.functor T F G) H m)]
/-- Actual original heterogeneous left flattening into its chosen nested Day value. -/
def flatToNested : point T U F G H m ⟶ EnrichedDayKernel.obj U (Output.functor T F G) H m :=
  Enriched.weightedCoend.Transport.map (product T) (flatWeight T U m) (weight U m)
    (coefficients F G H)
    ((Output.functor T F G).externalTensor H) (weightMap T U m)
    (fun X => AssociatorTensor.leftCoefficientMap T F G H X)
    (weightMap_naturality T U m) (AssociatorTensor.leftCoefficientMap_naturality T F G H)
@[reassoc]
theorem generator_flatToNested (X : (C × D) × E) :
    generator T U F G H m X ≫ flatToNested T U F G H m =
      (𝟙 (U.obj (T.obj X.1, X.2) ⟶[V] m) ⊗ₘ
        (AssociatorUnit.unitGenerator T F G X.1 ⊗ₘ 𝟙 (H.obj X.2))) ≫
        EnrichedDayKernel.gen U (Output.functor T F G) H m (T.obj X.1, X.2) :=
  Enriched.weightedCoend.Transport.ι_map (product T) (flatWeight T U m) (weight U m)
    (coefficients F G H)
    ((Output.functor T F G).externalTensor H) (weightMap T U m)
    (fun X => AssociatorTensor.leftCoefficientMap T F G H X)
    (weightMap_naturality T U m) (AssociatorTensor.leftCoefficientMap_naturality T F G H) X
end Forward
/-- Recover the flat triple `(a, p.2)` from an inner pair and an outer pair. -/
abbrev triple (p : K × E) (a : C × D) : (C × D) × E := (a, p.2)
/-- Contract the represented inner Hom into the outer left weight at the fixed final
  index. -/
abbrev sliceBase (p : K × E) (a : C × D) : (weight U m).obj (op p) ⊗ (T.obj a ⟶[V] p.1) ⟶
    (weight U m).obj (op (T.obj a, p.2)) :=
  AssociatorContraction.rightSliceWeight (weight U m) p.2 (T.obj a) p.1
/-- Contract a left nested object summand into the corresponding flat object summand. -/
abbrev contractWord (p : K × E) (a : C × D) : AssociatorFaces.Left.objects T U F G H m p a ⟶
    objects T U F G H m (triple p a) :=
  AssociatorContraction.contract (sliceBase T U m p a) (F.obj a.1 ⊗ G.obj a.2) (H.obj p.2)

section Factorization
variable [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects U (Output.functor T F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations U (Output.functor T F G) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U (Output.functor T F G) H m)
    (EnrichedDayKernel.rightMap U (Output.functor T F G) H m)]
@[reassoc]
theorem contractWord_generator_factorization (p : K × E) (a : C × D) :
    contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) ≫ flatToNested T U F G H m =
      AssociatorFaces.Left.nestedGenerator T U F G H m p a := by
  let x := T.obj a
  let B := H.obj p.2
  let A := F.obj a.1 ⊗ G.obj a.2
  let R : V := x ⟶[V] p.1
  let Y := EnrichedDayKernel.obj T F G p.1
  let X := EnrichedDayKernel.obj T F G x
  let u : A ⟶ X := AssociatorUnit.unitGenerator T F G a
  let g : R ⊗ A ⟶ Y := EnrichedDayKernel.gen T F G p.1 a
  let o : X ⊗ R ⟶ Y := MonoidalClosed.uncurry (Output.map T F G x p.1)
  have hd : R ◁ u ≫ (β_ R X).hom ≫ o = g := by
    have hm := Output.map_uncurry T F G x p.1
    change o = (β_ R X).inv ≫ MonoidalClosed.uncurry (Output.actionDesc T F G x p.1) at hm
    rw [hm]
    simp only [Iso.hom_inv_id_assoc]
    exact AssociatorUnit.unitGenerator_action T F G a p.1
  have hc := AssociatorContraction.rightSlice_condition (weight U m) (Output.functor T F G) H p.2 x
    p.1 u
  rw [generator_flatToNested]
  let Wb := (weight U m).obj (op p)
  let Wa := (weight U m).obj (op (x, p.2))
  let k : Wb ⊗ R ⟶ Wa := sliceBase T U m p a
  let N := EnrichedDayKernel.obj U (Output.functor T F G) H m
  let ga : Wa ⊗ (X ⊗ B) ⟶ N := EnrichedDayKernel.gen U (Output.functor T F G) H m (x, p.2)
  let gb : Wb ⊗ (Y ⊗ B) ⟶ N := EnrichedDayKernel.gen U (Output.functor T F G) H m p
  change (Wb ◁ (α_ R A B).hom ≫ (α_ Wb R (A ⊗ B)).inv ≫ (k ⊗ₘ 𝟙 (A ⊗ B))) ≫
      (𝟙 Wa ⊗ₘ (u ⊗ₘ 𝟙 B)) ≫ ga = Wb ◁ (g ▷ B) ≫ gb
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  have h := hc
  change Wb ◁ (α_ R A B).hom ≫ (α_ Wb R (A ⊗ B)).inv ≫ (k ⊗ₘ (u ⊗ₘ 𝟙 B)) ≫ ga =
      Wb ◁ ((R ◁ u ≫ (β_ R X).hom ≫ o) ⊗ₘ 𝟙 B) ≫ gb at h
  rw [hd] at h
  simpa only [tensorHom_id] using h
end Factorization

/-- The full flat weight action along the original fixed-second triple inclusion. -/
abbrev flatInnerSlice (e : E) (a b : C × D) :
    (flatWeight T U m).obj (op (b, e)) ⊗ (a ⟶[V] b) ⟶
      (flatWeight T U m).obj (op (a, e)) :=
  (flatWeight T U m).obj (op (b, e)) ◁
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C × D) e).map a b ≫
      MonoidalClosed.uncurry ((flatWeight T U m).map (op (b, e)) (op (a, e)))

/-- The complete flat Hom action is precisely the original tensor map followed by the slice. -/
theorem flatInnerSlice_original (e : E) (a b : C × D) :
    flatInnerSlice T U m e a b =
      (flatWeight T U m).obj (op (b, e)) ◁ T.map a b ≫
        AssociatorContraction.rightSliceWeight (weight U m) e
          (T.obj a) (T.obj b) := by
  let W := weight U m
  let Q := flatWeight T U m
  let S : EnrichedFunctor V ((C × D) × E) (K × E) := product T
  let U0 := Q.obj (op (b, e))
  let P : V := a ⟶[V] b
  let R : V := T.obj a ⟶[V] T.obj b
  let j : P ⟶ ((a, e) ⟶[V] (b, e)) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C × D) e).map a b
  let k : R ⟶ ((T.obj a, e) ⟶[V] (T.obj b, e)) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := K) e).map (T.obj a) (T.obj b)
  let t : P ⟶ R := T.map a b
  let s : ((a, e) ⟶[V] (b, e)) ⟶ ((T.obj a, e) ⟶[V] (T.obj b, e)) :=
    S.map (a, e) (b, e)
  let v : U0 ⊗ ((a, e) ⟶[V] (b, e)) ⟶ Q.obj (op (a, e)) :=
    MonoidalClosed.uncurry (Q.map (op (b, e)) (op (a, e)))
  let w : U0 ⊗ ((T.obj a, e) ⟶[V] (T.obj b, e)) ⟶ Q.obj (op (a, e)) :=
    MonoidalClosed.uncurry (W.map (op (T.obj b, e)) (op (T.obj a, e)))
  have hv : v = U0 ◁ s ≫ w := by
    have h := weightMap_naturality T U m (a, e) (b, e)
    change v ≫ 𝟙 (Q.obj (op (a, e))) = (𝟙 U0 ⊗ₘ s) ≫ w at h
    simpa only [Category.comp_id, id_tensorHom] using h
  have hj : j ≫ s = t ≫ k := AssociatorInclusion.rightInclusion_product_map T e a b
  change U0 ◁ j ≫ v = U0 ◁ t ≫ U0 ◁ k ≫ w
  calc
    _ = U0 ◁ (j ≫ s) ≫ w := by
      rw [hv]
      exact (whiskerLeft_comp_assoc U0 j s w).symm
    _ = U0 ◁ (t ≫ k) ≫ w := congrArg (fun z => U0 ◁ z ≫ w) hj
    _ = _ := whiskerLeft_comp_assoc U0 t k w

/-- Both original inner weight legs contract to the full flat inner Hom action. -/
@[reassoc]
theorem sliceBase_inner (p : K × E) (a b : C × D) :
    (α_ ((weight U m).obj (op p))
        (T.obj b ⟶[V] p.1) (a ⟶[V] b)).inv ≫
      (sliceBase T U m p b ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ flatInnerSlice T U m p.2 a b =
    (weight U m).obj (op p) ◁
      MonoidalClosed.uncurry ((weight T p.1).map (op b) (op a)) ≫
      sliceBase T U m p a := by
  let W := weight U m
  let U0 := W.obj (op p)
  let Y := W.obj (op (T.obj b, p.2))
  let R : V := T.obj b ⟶[V] p.1
  let P : V := a ⟶[V] b
  let S : V := T.obj a ⟶[V] T.obj b
  let t : P ⟶ S := T.map a b
  let k : U0 ⊗ R ⟶ Y := AssociatorContraction.rightSliceWeight W p.2 (T.obj b) p.1
  let l : Y ⊗ S ⟶ W.obj (op (T.obj a, p.2)) :=
    AssociatorContraction.rightSliceWeight W p.2 (T.obj a) (T.obj b)
  let z : U0 ⊗ (T.obj a ⟶[V] p.1) ⟶ W.obj (op (T.obj a, p.2)) :=
    AssociatorContraction.rightSliceWeight W p.2 (T.obj a) p.1
  have hf : (k ⊗ₘ 𝟙 P) ≫ Y ◁ t = k ⊗ₘ t := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom]
    exact congrArg₂ (fun f g => f ⊗ₘ g) (Category.comp_id k) (Category.id_comp t)
  have h := AssociatorContraction.rightSliceWeight_comp W p.2 (T.obj a) (T.obj b) p.1 t
  change (α_ U0 R P).inv ≫ (k ⊗ₘ t) ≫ l =
    U0 ◁ (R ◁ t ≫ (β_ R S).hom ≫ eComp V (T.obj a) (T.obj b) p.1) ≫ z at h
  rw [flatInnerSlice_original, weight_uncurry_map]
  change (α_ U0 R P).inv ≫ (k ⊗ₘ 𝟙 P) ≫ Y ◁ t ≫ l =
    U0 ◁ (R ◁ t ≫ (β_ R S).hom ≫ eComp V (T.obj a) (T.obj b) p.1) ≫ z
  have hf' : (k ⊗ₘ 𝟙 P) ≫ Y ◁ t ≫ l = (k ⊗ₘ t) ≫ l := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ l) hf
  rw [hf']
  exact h


/-- The full flat weight action along the actual fixed-first triple inclusion. -/
abbrev flatOuterSlice (a : C × D) (e f : E) :
    (flatWeight T U m).obj (op (a, f)) ⊗ (e ⟶[V] f) ⟶
      (flatWeight T U m).obj (op (a, e)) :=
  (flatWeight T U m).obj (op (a, f)) ◁
    (EnrichedFunctor.prodRightInclusion (V := V) (B := E) a).map e f ≫
      MonoidalClosed.uncurry ((flatWeight T U m).map (op (a, f)) (op (a, e)))

/-- The full flat outer action is the actual outer slice after preservation of the inner identity.
-/
theorem flatOuterSlice_original (a : C × D) (e f : E) :
    flatOuterSlice T U m a e f =
      AssociatorContraction.leftSliceWeight (weight U m)
        (T.obj a) e f := by
  let W := weight U m
  let Q := flatWeight T U m
  let P : EnrichedFunctor V ((C × D) × E) (K × E) := product T
  let U0 := Q.obj (op (a, f))
  let M0 : V := e ⟶[V] f
  let R : V := a ⟶[V] a
  let S : V := T.obj a ⟶[V] T.obj a
  let j : M0 ⟶ R ⊗ M0 := (EnrichedFunctor.prodRightInclusion (V := V) (B := E) a).map e f
  let k : M0 ⟶ S ⊗ M0 :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := E) (T.obj a)).map e f
  let t : R ⊗ M0 ⟶ S ⊗ M0 := P.map (a, e) (a, f)
  let v : U0 ⊗ (R ⊗ M0) ⟶ Q.obj (op (a, e)) :=
    MonoidalClosed.uncurry (Q.map (op (a, f)) (op (a, e)))
  let w : U0 ⊗ (S ⊗ M0) ⟶ Q.obj (op (a, e)) :=
    MonoidalClosed.uncurry (W.map (op (T.obj a, f)) (op (T.obj a, e)))
  have hv : v = U0 ◁ t ≫ w := by
    have h := weightMap_naturality T U m (a, e) (a, f)
    change v ≫ 𝟙 (Q.obj (op (a, e))) = (𝟙 U0 ⊗ₘ t) ≫ w at h
    simpa only [Category.comp_id, id_tensorHom] using h
  have hj : j ≫ t = k := AssociatorInclusion.leftInclusion_fixed_product T a e f
  change U0 ◁ j ≫ v = U0 ◁ k ≫ w
  rw [hv]
  exact (whiskerLeft_comp_assoc U0 j t w).symm.trans (congrArg (fun z => U0 ◁ z ≫ w) hj)

/-- Both full original outer weight legs contract to the actual flat outer Hom action. -/
@[reassoc]
theorem sliceBase_outer (a : C × D) (p q : K × E) :
    (weight U m).obj (op q) ◁
      AssociatorContraction.outerHomComposition (V := V) (T.obj a)
        p.1 q.1 p.2 q.2 ≫
      (α_ ((weight U m).obj (op q))
        (T.obj a ⟶[V] q.1) (p.2 ⟶[V] q.2)).inv ≫
      (sliceBase T U m q a ⊗ₘ 𝟙 (p.2 ⟶[V] q.2)) ≫ flatOuterSlice T U m a p.2 q.2 =
    (α_ ((weight U m).obj (op q)) (p ⟶[V] q)
        (T.obj a ⟶[V] p.1)).inv ≫
      (MonoidalClosed.uncurry ((weight U m).map (op q) (op p)) ⊗ₘ
        𝟙 (T.obj a ⟶[V] p.1)) ≫ sliceBase T U m p a := by
  let W := weight U m
  let x := T.obj a
  let U0 := W.obj (op q)
  let δ := AssociatorContraction.outerHomComposition (V := V) x p.1 q.1 p.2 q.2
  have h0 := AssociatorContraction.outerWeight_comp W x p.1 q.1 p.2 q.2
  have h1 := AssociatorContraction.sliceWeight_product W x q.1 p.2 q.2
  have h2 := congrArg (fun z => U0 ◁ δ ≫ z) h1
  rw [flatOuterSlice_original]
  change U0 ◁ δ ≫
      (α_ (W.obj (op (q.1, q.2))) (x ⟶[V] q.1) (p.2 ⟶[V] q.2)).inv ≫
      (AssociatorContraction.rightSliceWeight W q.2 x q.1 ⊗ₘ 𝟙 (p.2 ⟶[V] q.2)) ≫
      AssociatorContraction.leftSliceWeight W x p.2 q.2 =
    (α_ (W.obj (op (q.1, q.2))) (((p.1, p.2) : K × E) ⟶[V] (q.1, q.2))
      (x ⟶[V] p.1)).inv ≫
      (MonoidalClosed.uncurry (W.map (op (q.1, q.2)) (op (p.1, p.2))) ⊗ₘ 𝟙 (x ⟶[V] p.1)) ≫
      AssociatorContraction.rightSliceWeight W p.2 x p.1
  simpa only [Category.assoc] using h2.trans h0.symm


section Balances
variable [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]

/-- Contraction identifies both complete original inner relation faces after the flat projection. -/
@[reassoc]
theorem contractWord_inner (p : K × E) (a b : C × D) :
    AssociatorFaces.Left.b0 T U F G H m p a b ≫
      contractWord T U F G H m p a ≫ generator T U F G H m (a, p.2) =
    AssociatorFaces.Left.b1 T U F G H m p a b ≫
      contractWord T U F G H m p b ≫ generator T U F G H m (b, p.2) := by
  let W := weight U m
  let Q := flatWeight T U m
  let U0 := W.obj (op p)
  let A := F.obj a.1 ⊗ G.obj a.2
  let A' := F.obj b.1 ⊗ G.obj b.2
  let B := H.obj p.2
  let R : V := T.obj b ⟶[V] p.1
  let S : V := T.obj a ⟶[V] p.1
  let P : V := a ⟶[V] b
  let X := Q.obj (op (a, p.2))
  let Y := Q.obj (op (b, p.2))
  let v : R ⊗ P ⟶ S := MonoidalClosed.uncurry ((weight T p.1).map (op b) (op a))
  let k : U0 ⊗ S ⟶ X := sliceBase T U m p a
  let l : U0 ⊗ R ⟶ Y := sliceBase T U m p b
  let q : Y ⊗ P ⟶ X := flatInnerSlice T U m p.2 a b
  let f : P ⊗ A ⟶ A' := (β_ P A).hom ≫ MonoidalClosed.uncurry ((F.externalTensor G).map a b)
  let Z := point T U F G H m
  let ga : X ⊗ (A ⊗ B) ⟶ Z := generator T U F G H m (a, p.2)
  let gb : Y ⊗ (A' ⊗ B) ⟶ Z := generator T U F G H m (b, p.2)
  let pre := AssociatorContraction.contract l (P ⊗ A) B
  have h0 := AssociatorContraction.contract_inner_weight (A := A) (B := B)
    v k l q (sliceBase_inner T U m p a b)
  have h0' : U0 ◁ (((α_ R P A).inv ≫ (v ⊗ₘ 𝟙 A)) ▷ B) ≫
      AssociatorContraction.contract k A B ≫ ga =
    pre ≫ Y ◁ (α_ P A B).hom ≫ (α_ Y P (A ⊗ B)).inv ≫
      (q ⊗ₘ 𝟙 (A ⊗ B)) ≫ ga := by
    simpa only [pre, AssociatorContraction.contract, Category.assoc] using
      congrArg (fun z => z ≫ ga) h0
  have hb := AssociatorContraction.rightSlice_condition Q (F.externalTensor G) H p.2 a b (𝟙 A)
  change Y ◁ (α_ P A B).hom ≫ (α_ Y P (A ⊗ B)).inv ≫
      (q ⊗ₘ (𝟙 A ⊗ₘ 𝟙 B)) ≫ ga =
    Y ◁ ((P ◁ 𝟙 A ≫ f) ⊗ₘ 𝟙 B) ≫ gb at hb
  rw [id_tensorHom_id, whiskerLeft_id, Category.id_comp] at hb
  have hb' : pre ≫ Y ◁ (α_ P A B).hom ≫ (α_ Y P (A ⊗ B)).inv ≫
      (q ⊗ₘ 𝟙 (A ⊗ B)) ≫ ga = pre ≫ Y ◁ (f ⊗ₘ 𝟙 B) ≫ gb := by
    simpa only [Category.assoc] using congrArg (fun z => pre ≫ z) hb
  have h1 := AssociatorContraction.contract_naturality l f (𝟙 B)
  have h1' : U0 ◁ ((R ◁ f) ▷ B) ≫ AssociatorContraction.contract l A' B ≫ gb =
      pre ≫ Y ◁ (f ⊗ₘ 𝟙 B) ≫ gb := by
    simpa only [pre, AssociatorContraction.contract, Category.assoc, tensorHom_id] using
      congrArg (fun z => z ≫ gb) h1
  change U0 ◁ (((α_ R P A).inv ≫ (v ⊗ₘ 𝟙 A)) ▷ B) ≫
      AssociatorContraction.contract k A B ≫ ga =
    U0 ◁ ((R ◁ f) ▷ B) ≫ AssociatorContraction.contract l A' B ≫ gb
  simpa only [Category.assoc] using h0'.trans (hb'.trans h1'.symm)


/-- Contraction identifies both complete original outer relation faces after the flat projection. -/
@[reassoc]
theorem contractWord_outer (p q : K × E) (a : C × D) :
    AssociatorFaces.Left.a0 T U F G H m p q a ≫
      contractWord T U F G H m p a ≫ generator T U F G H m (a, p.2) =
    AssociatorFaces.Left.a1 T U F G H m p q a ≫
      contractWord T U F G H m q a ≫ generator T U F G H m (a, q.2) := by
  let W := weight U m
  let Q := flatWeight T U m
  let x := T.obj a
  let U0 := W.obj (op q)
  let K0 := W.obj (op p)
  let X := W.obj (op (x, p.2))
  let Y := W.obj (op (x, q.2))
  let L : V := p.1 ⟶[V] q.1
  let M0 : V := p.2 ⟶[V] q.2
  let R : V := x ⟶[V] p.1
  let S : V := x ⟶[V] q.1
  let A := F.obj a.1 ⊗ G.obj a.2
  let B := H.obj p.2
  let B' := H.obj q.2
  let f : L ⊗ R ⟶ S := (β_ L R).hom ≫ eComp V x p.1 q.1
  let out : L ⊗ (R ⊗ A) ⟶ S ⊗ A := Output.outputAction x p.1 q.1 A
  let b : M0 ⊗ B ⟶ B' := (β_ M0 B).hom ≫ MonoidalClosed.uncurry (H.map p.2 q.2)
  let v : U0 ⊗ (L ⊗ M0) ⟶ K0 := MonoidalClosed.uncurry (W.map (op q) (op p))
  let k : K0 ⊗ R ⟶ X := sliceBase T U m p a
  let l : U0 ⊗ S ⟶ Y := sliceBase T U m q a
  let t : Y ⊗ M0 ⟶ X := flatOuterSlice T U m a p.2 q.2
  let Z := point T U F G H m
  let ga : X ⊗ (A ⊗ B) ⟶ Z := generator T U F G H m (a, p.2)
  let gb : Y ⊗ (A ⊗ B') ⟶ Z := generator T U F G H m (a, q.2)
  let pre : U0 ⊗ ((L ⊗ M0) ⊗ ((R ⊗ A) ⊗ B)) ⟶ Y ⊗ (A ⊗ (M0 ⊗ B)) :=
    U0 ◁ (tensorμ L M0 (R ⊗ A) B ≫ (out ⊗ₘ 𝟙 (M0 ⊗ B))) ≫
      AssociatorContraction.contract l A (M0 ⊗ B)
  have hout : out = (α_ L R A).inv ≫ (f ⊗ₘ 𝟙 A) := by
    change (α_ L R A).inv ≫ ((β_ L R).hom ⊗ₘ 𝟙 A) ≫
        (eComp V x p.1 q.1 ⊗ₘ 𝟙 A) = (α_ L R A).inv ≫ (f ⊗ₘ 𝟙 A)
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hd : AssociatorContraction.outerAction f M0 =
      AssociatorContraction.outerHomComposition (V := V) x p.1 q.1 p.2 q.2 :=
    AssociatorContraction.outerAction_comp (V := V) x p.1 q.1 p.2 q.2
  have hw := sliceBase_outer T U m a p q
  change U0 ◁ AssociatorContraction.outerHomComposition (V := V) x p.1 q.1 p.2 q.2 ≫
      (α_ U0 S M0).inv ≫ (l ⊗ₘ 𝟙 M0) ≫ t =
    (α_ U0 (L ⊗ M0) R).inv ≫ (v ⊗ₘ 𝟙 R) ≫ k at hw
  rw [← hd] at hw
  have h0 := AssociatorContraction.contract_outer_weight f M0 A B v k l t hw
  have h0' : (α_ U0 (L ⊗ M0) ((R ⊗ A) ⊗ B)).inv ≫
      (v ⊗ₘ 𝟙 ((R ⊗ A) ⊗ B)) ≫ AssociatorContraction.contract k A B ≫ ga =
    pre ≫ Y ◁ (AssociatorRightContraction.frontHomIso M0 A B).hom ≫
      (α_ Y M0 (A ⊗ B)).inv ≫ (t ⊗ₘ 𝟙 (A ⊗ B)) ≫ ga := by
    simpa only [pre, hout, AssociatorContraction.contract, Category.assoc] using
      congrArg (fun z => z ≫ ga) h0
  have hb := AssociatorRightContraction.leftSlice_condition Q (F.externalTensor G) H a p.2 q.2 (𝟙 B)
  change Y ◁ (AssociatorRightContraction.frontHomIso M0 A B).hom ≫
      (α_ Y M0 (A ⊗ B)).inv ≫ (t ⊗ₘ (𝟙 A ⊗ₘ 𝟙 B)) ≫ ga =
    Y ◁ (A ◁ (M0 ◁ 𝟙 B ≫ b)) ≫ gb at hb
  rw [id_tensorHom_id, whiskerLeft_id, Category.id_comp] at hb
  have hb' : pre ≫ Y ◁ (AssociatorRightContraction.frontHomIso M0 A B).hom ≫
      (α_ Y M0 (A ⊗ B)).inv ≫ (t ⊗ₘ 𝟙 (A ⊗ B)) ≫ ga =
    pre ≫ Y ◁ A ◁ b ≫ gb := by
    simpa only [Category.assoc] using congrArg (fun z => pre ≫ z) hb
  have hf : (out ⊗ₘ 𝟙 (M0 ⊗ B)) ≫ (𝟙 (S ⊗ A) ⊗ₘ b) = out ⊗ₘ b := by
    rw [tensorHom_comp_tensorHom]
    exact congrArg₂ (fun f g => f ⊗ₘ g) (Category.comp_id out) (Category.id_comp b)
  have hn : U0 ◁ (𝟙 (S ⊗ A) ⊗ₘ b) ≫ AssociatorContraction.contract l A B' =
      AssociatorContraction.contract l A (M0 ⊗ B) ≫ Y ◁ A ◁ b := by
    simpa only [whiskerLeft_id, id_tensorHom] using
      AssociatorContraction.contract_naturality l (𝟙 A) b
  have hng : U0 ◁ (𝟙 (S ⊗ A) ⊗ₘ b) ≫ AssociatorContraction.contract l A B' ≫ gb =
      AssociatorContraction.contract l A (M0 ⊗ B) ≫ Y ◁ A ◁ b ≫ gb := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ gb) hn
  have h1' : U0 ◁ (tensorμ L M0 (R ⊗ A) B ≫ (out ⊗ₘ b)) ≫
      AssociatorContraction.contract l A B' ≫ gb = pre ≫ Y ◁ A ◁ b ≫ gb := by
    rw [whiskerLeft_comp, Category.assoc, ← hf, whiskerLeft_comp, Category.assoc, hng]
    simp only [pre, whiskerLeft_comp, Category.assoc]
  change ((α_ U0 (L ⊗ M0) ((R ⊗ A) ⊗ B)).inv ≫ (v ⊗ₘ 𝟙 ((R ⊗ A) ⊗ B))) ≫
      AssociatorContraction.contract k A B ≫ ga =
    U0 ◁ (tensorμ L M0 (R ⊗ A) B ≫ (out ⊗ₘ b)) ≫
      AssociatorContraction.contract l A B' ≫ gb
  simpa only [Category.assoc] using h0'.trans (hb'.trans h1'.symm)

end Balances

/-- The original full inner identity becomes the actual outer product identity. -/
@[reassoc]
theorem sliceBase_identity (a : C × D) (e : E) :
    (ρ_ ((weight U m).obj (op (T.obj a, e)))).inv ≫
      (𝟙 ((weight U m).obj (op (T.obj a, e))) ⊗ₘ
        eId V (T.obj a)) ≫
      sliceBase T U m (T.obj a, e) a =
    𝟙 ((weight U m).obj (op (T.obj a, e))) := by
  let x := T.obj a
  let p : K × E := (x, e)
  let W := weight U m
  let U0 := W.obj (op p)
  let j : (x ⟶[V] x) ⟶ (p ⟶[V] p) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := K) e).map x x
  let w : U0 ⊗ (p ⟶[V] p) ⟶ U0 := MonoidalClosed.uncurry (W.map (op p) (op p))
  have hj : eId V x ≫ j = eId V p :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := K) e).map_id x
  have hi := AssociatorRightContraction.action_identity W (op p)
  change (ρ_ U0).inv ≫ (𝟙 U0 ⊗ₘ eId V p) ≫ w = 𝟙 U0 at hi
  change (ρ_ U0).inv ≫ (𝟙 U0 ⊗ₘ eId V x) ≫ (U0 ◁ j ≫ w) = 𝟙 U0
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  rw [hj]
  exact hi

/-- Insert the actual inner identity into the unchanged original left nested generator word. -/
abbrev identityWord (X : (C × D) × E) :
    objects T U F G H m X ⟶
      AssociatorFaces.Left.objects T U F G H m
        (T.obj X.1, X.2) X.1 :=
  (weight U m).obj (op (T.obj X.1, X.2)) ◁
    (AssociatorUnit.identityInsert (T.obj X.1) (F.obj X.1.1 ⊗ G.obj X.1.2) ▷ H.obj X.2)

/-- Identity insertion followed by original contraction is the full original flat summand identity.
-/
@[reassoc]
theorem identityWord_contractWord (X : (C × D) × E) :
    identityWord T U F G H m X ≫
      contractWord T U F G H m (T.obj X.1, X.2) X.1 =
    𝟙 (objects T U F G H m X) := by
  let x := T.obj X.1
  let p : K × E := (x, X.2)
  let U0 := (weight U m).obj (op p)
  let A := F.obj X.1.1 ⊗ G.obj X.1.2
  let B := H.obj X.2
  let k : U0 ⊗ (x ⟶[V] x) ⟶ U0 := sliceBase T U m p X.1
  change U0 ◁ (AssociatorUnit.identityInsert x A ▷ B) ≫
    AssociatorContraction.contract k A B = 𝟙 (U0 ⊗ (A ⊗ B))
  exact AssociatorContraction.contract_identity (eId V x) k (sliceBase_identity T U m X.1 X.2) A B

section UnitForward
variable [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [HasCoproduct (objects T U F G H m)] [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects U (Output.functor T F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations U (Output.functor T F G) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U (Output.functor T F G) H m)
    (EnrichedDayKernel.rightMap U (Output.functor T F G) H m)]
/-- The actual flat-to-nested generator is the original nested generator after identity insertion.
-/
@[reassoc]
theorem generator_flatToNested_identity (X : (C × D) × E) :
    generator T U F G H m X ≫ flatToNested T U F G H m =
      identityWord T U F G H m X ≫
        AssociatorFaces.Left.nestedGenerator T U F G H m
          (T.obj X.1, X.2) X.1 := by
  rw [generator_flatToNested]
  let x := T.obj X.1
  let p : K × E := (x, X.2)
  let U0 := (weight U m).obj (op p)
  let A := F.obj X.1.1 ⊗ G.obj X.1.2
  let B := H.obj X.2
  let Y := EnrichedDayKernel.obj T F G x
  let i : A ⟶ (x ⟶[V] x) ⊗ A := AssociatorUnit.identityInsert x A
  let g : (x ⟶[V] x) ⊗ A ⟶ Y := EnrichedDayKernel.gen T F G x X.1
  let N := EnrichedDayKernel.obj U (Output.functor T F G) H m
  let j : U0 ⊗ (Y ⊗ B) ⟶ N :=
    EnrichedDayKernel.gen U (Output.functor T F G) H m p
  change (𝟙 U0 ⊗ₘ ((i ≫ g) ⊗ₘ 𝟙 B)) ≫ j = U0 ◁ (i ▷ B) ≫ U0 ◁ (g ▷ B) ≫ j
  simp only [id_tensorHom, tensorHom_id, comp_whiskerRight, whiskerLeft_comp, Category.assoc]

end UnitForward

section Comparison
variable [HasCoproduct (objects T U F G H m)]
  [HasCoproduct (relations T U F G H m)]
  [HasCoequalizer (map0 T U F G H m) (map1 T U F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousObjects T U F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousRelations T U F G H m)]
  [HasCoequalizer
    (AssociatorPresentation.Left.simultaneousLeftMap T U F G H m)
    (AssociatorPresentation.Left.simultaneousRightMap T U F G H m)]

/-- Descend the original left contraction through both full original relation families. -/
def simultaneousDesc :
    AssociatorPresentation.Left.simultaneousPoint T U F G H m ⟶
      point T U F G H m := by
  let objs : (K × E) × (C × D) → V :=
    AssociatorPresentation.Left.simultaneousObjects T U F G H m
  let family : ∀ pi, objs pi ⟶ point T U F G H m := fun pi =>
    contractWord T U F G H m pi.1 pi.2 ≫ generator T U F G H m (triple pi.1 pi.2)
  refine coequalizer.desc (Sigma.desc (f := objs) family) ?_
  apply Sigma.hom_ext
  intro r
  cases r with
  | inl pqi =>
    simp only [AssociatorPresentation.Left.simultaneousLeftMap,
      AssociatorPresentation.Left.simultaneousRightMap, Sigma.ι_comp_desc_assoc]
    change ((AssociatorFaces.Left.a0 T U F G H m
        pqi.1.1 pqi.1.2 pqi.2 ≫ Sigma.ι objs (pqi.1.1, pqi.2)) ≫ Sigma.desc (f := objs) family) =
      ((AssociatorFaces.Left.a1 T U F G H m
        pqi.1.1 pqi.1.2 pqi.2 ≫ Sigma.ι objs (pqi.1.2, pqi.2)) ≫ Sigma.desc (f := objs) family)
    let l := AssociatorFaces.Left.a0 T U F G H m
      pqi.1.1 pqi.1.2 pqi.2
    let r := AssociatorFaces.Left.a1 T U F G H m
      pqi.1.1 pqi.1.2 pqi.2
    have hl : (l ≫ Sigma.ι objs (pqi.1.1, pqi.2)) ≫ Sigma.desc (f := objs) family =
        l ≫ family (pqi.1.1, pqi.2) :=
      (Category.assoc l (Sigma.ι objs (pqi.1.1, pqi.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => l ≫ z) (Sigma.ι_comp_desc (f := objs) family (pqi.1.1, pqi.2)))
    have hr : (r ≫ Sigma.ι objs (pqi.1.2, pqi.2)) ≫ Sigma.desc (f := objs) family =
        r ≫ family (pqi.1.2, pqi.2) :=
      (Category.assoc r (Sigma.ι objs (pqi.1.2, pqi.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => r ≫ z) (Sigma.ι_comp_desc (f := objs) family (pqi.1.2, pqi.2)))
    have hb : l ≫ family (pqi.1.1, pqi.2) = r ≫ family (pqi.1.2, pqi.2) :=
      contractWord_outer T U F G H m pqi.1.1 pqi.1.2 pqi.2
    exact hl.trans (hb.trans hr.symm)
  | inr pij =>
    simp only [AssociatorPresentation.Left.simultaneousLeftMap,
      AssociatorPresentation.Left.simultaneousRightMap, Sigma.ι_comp_desc_assoc]
    change ((AssociatorFaces.Left.b0 T U F G H m
        pij.1 pij.2.1 pij.2.2 ≫ Sigma.ι objs (pij.1, pij.2.1)) ≫ Sigma.desc (f := objs) family) =
      ((AssociatorFaces.Left.b1 T U F G H m
        pij.1 pij.2.1 pij.2.2 ≫ Sigma.ι objs (pij.1, pij.2.2)) ≫ Sigma.desc (f := objs) family)
    let l := AssociatorFaces.Left.b0 T U F G H m
      pij.1 pij.2.1 pij.2.2
    let r := AssociatorFaces.Left.b1 T U F G H m
      pij.1 pij.2.1 pij.2.2
    have hl : (l ≫ Sigma.ι objs (pij.1, pij.2.1)) ≫ Sigma.desc (f := objs) family =
        l ≫ family (pij.1, pij.2.1) :=
      (Category.assoc l (Sigma.ι objs (pij.1, pij.2.1)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => l ≫ z) (Sigma.ι_comp_desc (f := objs) family (pij.1, pij.2.1)))
    have hr : (r ≫ Sigma.ι objs (pij.1, pij.2.2)) ≫ Sigma.desc (f := objs) family =
        r ≫ family (pij.1, pij.2.2) :=
      (Category.assoc r (Sigma.ι objs (pij.1, pij.2.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => r ≫ z) (Sigma.ι_comp_desc (f := objs) family (pij.1, pij.2.2)))
    have hb : l ≫ family (pij.1, pij.2.1) = r ≫ family (pij.1, pij.2.2) :=
      contractWord_inner T U F G H m pij.1 pij.2.1 pij.2.2
    exact hl.trans (hb.trans hr.symm)

/-- The simultaneous descent retains the actual original contraction on every raw left word. -/
@[reassoc]
theorem simultaneousProjection_simultaneousDesc (p : K × E) (a : C × D) :
    AssociatorPresentation.Left.simultaneousProjection T U F G H m p a ≫
        simultaneousDesc T U F G H m =
      contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) := by
  simp only [AssociatorPresentation.Left.simultaneousProjection, simultaneousDesc,
    Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

variable
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.objects T U F G H m p)]
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.innerRelations T U F G H m p)]
  [∀ p : K × E, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap T U F G H m p)
    (AssociatorFaces.Left.innerRightMap T U F G H m p)]
  [∀ pq : (K × E) × (K × E), HasCoproduct
    (AssociatorPresentation.Left.relationObjects T U F G H m pq)]
  [∀ pq : (K × E) × (K × E), HasCoproduct
    (AssociatorPresentation.Left.relationRelations T U F G H m pq)]
  [∀ pq : (K × E) × (K × E), HasCoequalizer
    (AssociatorPresentation.Left.relationLeftMap T U F G H m pq)
    (AssociatorPresentation.Left.relationRightMap T U F G H m pq)]
  [HasCoproduct (AssociatorPresentation.Left.innerObjects T U F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.outerRelations T U F G H m)]
  [HasCoequalizer
    (AssociatorPresentation.Left.outerLeftMap T U F G H m)
    (AssociatorPresentation.Left.outerRightMap T U F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects U (Output.functor T F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations U (Output.functor T F G) H m)]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap U (Output.functor T F G) H m)
    (EnrichedDayKernel.rightMap U (Output.functor T F G) H m)]

/-- The actual original left nested Day value descends to its unchanged selected flat triple coend.
-/
def nestedToFlat :
    EnrichedDayKernel.obj U (Output.functor T F G) H m ⟶
      point T U F G H m :=
  (AssociatorNested.Left.simultaneousIso T U F G H m).hom ≫
    simultaneousDesc T U F G H m

/-- Both original left generator legs contract to the exact original left flat summand. -/
@[reassoc]
theorem nestedGenerator_nestedToFlat (p : K × E) (a : C × D) :
    AssociatorFaces.Left.nestedGenerator T U F G H m p a ≫
        nestedToFlat T U F G H m =
      contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) := by
  simp only [nestedToFlat, ← Category.assoc]
  rw [AssociatorNested.Left.nestedGenerator_simultaneousIso_hom,
    simultaneousProjection_simultaneousDesc]
  simp only [contractWord, Category.assoc]

/-- The original nested generators prove the left comparison's nested inverse equation. -/
@[reassoc]
theorem nestedToFlat_flatToNested :
    nestedToFlat T U F G H m ≫ flatToNested T U F G H m =
      𝟙 (EnrichedDayKernel.obj U (Output.functor T F G) H m) := by
  apply AssociatorNested.Left.hom_ext T U F G H m
  intro p a
  rw [← Category.assoc, nestedGenerator_nestedToFlat]
  simpa only [Category.assoc, Category.comp_id] using contractWord_generator_factorization T U F G H
    m p a

/-- Actual identity insertion proves the left comparison's flat inverse equation. -/
@[reassoc]
theorem flatToNested_nestedToFlat :
    flatToNested T U F G H m ≫ nestedToFlat T U F G H m = 𝟙 (point T U F G H m) := by
  apply Enriched.weightedCoend.hom_ext (flatWeight T U m) (coefficients F G H)
  intro X
  rcases X with ⟨⟨e, g⟩, h⟩
  have hx := generator_flatToNested_identity T U F G H m ((e, g), h)
  have hn := nestedGenerator_nestedToFlat T U F G H m (T.obj (e, g), h) (e, g)
  have hi := identityWord_contractWord T U F G H m ((e, g), h)
  rw [← Category.assoc, hx, Category.assoc, hn]
  rw [← Category.assoc, hi]
  simp only [Category.id_comp, Category.comp_id]

/-- The genuine left flattening comparison on the original nested Day value and chosen coends. -/
def iso : point T U F G H m ≅
    EnrichedDayKernel.obj U (Output.functor T F G) H m where
  hom := flatToNested T U F G H m
  inv := nestedToFlat T U F G H m
  hom_inv_id := flatToNested_nestedToFlat T U F G H m
  inv_hom_id := nestedToFlat_flatToNested T U F G H m


/-- The actual heterogeneous comparison retains every original flat generator. -/
@[reassoc]
theorem generator_iso_hom (X : (C × D) × E) :
    generator T U F G H m X ≫ (iso T U F G H m).hom =
      (𝟙 (U.obj (T.obj X.1, X.2) ⟶[V] m) ⊗ₘ
        (AssociatorUnit.unitGenerator T F G X.1 ⊗ₘ 𝟙 (H.obj X.2))) ≫
        EnrichedDayKernel.gen U (Output.functor T F G) H m (T.obj X.1, X.2) :=
  generator_flatToNested T U F G H m X

/-- The inverse retains every original nested generator and its complete weight contraction. -/
@[reassoc]
theorem nestedGenerator_iso_inv (p : K × E) (a : C × D) :
    AssociatorFaces.Left.nestedGenerator T U F G H m p a ≫ (iso T U F G H m).inv =
      contractWord T U F G H m p a ≫ generator T U F G H m (triple p a) :=
  nestedGenerator_nestedToFlat T U F G H m p a
end Comparison
end CategoryTheory.EnrichedDayKernel.AssociatorLeftGeneral
