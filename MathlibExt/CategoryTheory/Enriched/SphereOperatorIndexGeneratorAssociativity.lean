/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorComposition
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexAssociator

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {I : Type uI} [Category.{vI} I] [EnrichedOrdinaryCategory V I]

/-- An actual enriched functor commutes with precomposition on the complete
Hom object. Its ordinary arrow is computed by the given enriched comparison. -/
private theorem enrichedFunctorFullPrecompositionForProof
    (F : EnrichedFunctor V I I) (X Y Z : I) (f : X ⟶ Y) :
    eHomWhiskerRight V f Z ≫ F.map X Z =
      F.map Y Z ≫ eHomWhiskerRight V
        ((eHomEquiv V).symm (eHomEquiv V f ≫ F.map X Y)) (F.obj Z) := by
  let H : V := Y ⟶[V] Z
  let K : V := F.obj Y ⟶[V] F.obj Z
  let p : (𝟙_ V) ⟶ (F.obj X ⟶[V] F.obj Y) :=
    eHomEquiv V f ≫ F.map X Y
  let r : F.obj X ⟶ F.obj Y := (eHomEquiv V).symm p
  have hPoint : eHomEquiv V r = p := (eHomEquiv V).apply_symm_apply p
  have hPair :
      (eHomEquiv V f ▷ H) ≫ (F.map X Y ⊗ₘ F.map Y Z) =
        p ⊗ₘ F.map Y Z := by
    simpa only [p, Category.id_comp, tensorHom_id] using
      tensorHom_comp_tensorHom (eHomEquiv V f) (𝟙 H)
        (F.map X Y) (F.map Y Z)
  have hUnit : (λ_ H).inv ≫ (p ⊗ₘ F.map Y Z) =
      F.map Y Z ≫ (λ_ K).inv ≫ (p ▷ K) :=
    leftUnitor_inv_comp_tensorHom p (F.map Y Z)
  change ((λ_ H).inv ≫ eHomEquiv V f ▷ H ≫ eComp V X Y Z) ≫
      F.map X Z = F.map Y Z ≫ eHomWhiskerRight V r (F.obj Z)
  calc
    _ = (λ_ H).inv ≫ (eHomEquiv V f ▷ H) ≫
        (F.map X Y ⊗ₘ F.map Y Z) ≫
        eComp V (F.obj X) (F.obj Y) (F.obj Z) := by
      simp only [Category.assoc]
      rw [F.map_comp X Y Z]
    _ = (λ_ H).inv ≫ (p ⊗ₘ F.map Y Z) ≫
        eComp V (F.obj X) (F.obj Y) (F.obj Z) := by
      simpa only [Category.assoc] using congrArg
        (fun z : (𝟙_ V) ⊗ H ⟶
            (F.obj X ⟶[V] F.obj Y) ⊗ (F.obj Y ⟶[V] F.obj Z) =>
          (λ_ H).inv ≫ z ≫
            eComp V (F.obj X) (F.obj Y) (F.obj Z)) hPair
    _ = F.map Y Z ≫ (λ_ K).inv ≫ (p ▷ K) ≫
        eComp V (F.obj X) (F.obj Y) (F.obj Z) := by
      simpa only [Category.assoc] using congrArg
        (fun z : H ⟶ (F.obj X ⟶[V] F.obj Y) ⊗ K =>
          z ≫ eComp V (F.obj X) (F.obj Y) (F.obj Z)) hUnit
    _ = F.map Y Z ≫ eHomWhiskerRight V r (F.obj Z) := by
      simp only [eHomWhiskerRight, hPoint, K]

/-- The actual enriched functor commutes with complete Hom precomposition.
This is the original proved compatibility, exposed without changing its algorithm. -/
public theorem enrichedFunctorFullPrecomposition
    (F : EnrichedFunctor V I I) (X Y Z : I) (f : X ⟶ Y) :
    eHomWhiskerRight V f Z ≫ F.map X Z =
      F.map Y Z ≫ eHomWhiskerRight V
        ((eHomEquiv V).symm (eHomEquiv V f ≫ F.map X Y)) (F.obj Z) :=
  enrichedFunctorFullPrecompositionForProof F X Y Z f

/-- The complete original enriched precomposition functions agree before
an index object or a native coefficient is substituted. -/
public theorem enrichedFunctorFullPrecomposition_function
    (F : EnrichedFunctor V I I) :
    (fun (X Y Z : I) (f : X ⟶ Y) =>
      eHomWhiskerRight V f Z ≫ F.map X Z) =
      fun (X Y Z : I) (f : X ⟶ Y) =>
        F.map Y Z ≫ eHomWhiskerRight V
          ((eHomEquiv V).symm (eHomEquiv V f ≫ F.map X Y)) (F.obj Z) := by
  funext X Y Z f
  exact enrichedFunctorFullPrecompositionForProof F X Y Z f

variable [BraidedCategory V] [MonoidalCategory I]

/-- The identity-fixed left tensor map carries the actual ordinary arrow to
the point of that same left tensor arrow. No braiding on I is used. -/
private theorem fixedLeftTensorPointForAssociativity
    (d : EnrichedMonoidalCategoryData V I) (c x y : I) (f : x ⟶ y) :
    eHomEquiv V f ≫ (λ_ (x ⟶[V] y)).inv ≫
        (eId V c ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap c c x y =
      eHomEquiv V (c ◁ f) := by
  let H : V := x ⟶[V] y
  let e : (𝟙_ V) ⟶ H := eHomEquiv V f
  have hUnit : e ≫ (λ_ H).inv =
      (λ_ (𝟙_ V)).inv ≫ (𝟙_ V ◁ e) :=
    leftUnitor_inv_naturality e
  have hPair : (𝟙_ V ◁ e) ≫ (eId V c ⊗ₘ 𝟙 H) =
      eId V c ⊗ₘ e := by
    simpa only [Category.id_comp, Category.comp_id, id_tensorHom] using
      tensorHom_comp_tensorHom (𝟙 (𝟙_ V)) e (eId V c) (𝟙 H)
  change e ≫ (λ_ H).inv ≫ (eId V c ⊗ₘ 𝟙 H) ≫
      d.tensorMap c c x y = eHomEquiv V (c ◁ f)
  calc
    _ = (λ_ (𝟙_ V)).inv ≫ (𝟙_ V ◁ e) ≫
        (eId V c ⊗ₘ 𝟙 H) ≫ d.tensorMap c c x y := by
      simpa only [Category.assoc] using congrArg
        (fun z : (𝟙_ V) ⟶ (𝟙_ V) ⊗ H =>
          z ≫ (eId V c ⊗ₘ 𝟙 H) ≫ d.tensorMap c c x y) hUnit
    _ = (λ_ (𝟙_ V)).inv ≫ (eId V c ⊗ₘ e) ≫
        d.tensorMap c c x y := by
      simpa only [Category.assoc] using congrArg
        (fun z : (𝟙_ V) ⊗ (𝟙_ V) ⟶ (c ⟶[V] c) ⊗ H =>
          (λ_ (𝟙_ V)).inv ≫ z ≫ d.tensorMap c c x y) hPair
    _ = eHomEquiv V ((𝟙 c) ⊗ₘ f) := by
      simpa only [e, eHomEquiv_id] using d.tensorMap_eHomEquiv (𝟙 c) f
    _ = eHomEquiv V (c ◁ f) := by
      rw [id_tensorHom]

/-- Left tensoring preserves the original full enriched composition. The
proof-local product insertion is derived from identities and the given tensor
functor; no functor law or operator composition is received as an input. -/
private theorem fixedLeftTensorCompForAssociativity
    (d : EnrichedMonoidalCategoryData V I) (c x y z : I) :
    eComp V x y z ≫ (λ_ (x ⟶[V] z)).inv ≫
        (eId V c ⊗ₘ 𝟙 (x ⟶[V] z)) ≫ d.tensorMap c c x z =
      (((λ_ (x ⟶[V] y)).inv ≫
          (eId V c ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap c c x y) ⊗ₘ
        ((λ_ (y ⟶[V] z)).inv ≫
          (eId V c ⊗ₘ 𝟙 (y ⟶[V] z)) ≫ d.tensorMap c c y z)) ≫
        eComp V (c ⊗ x) (c ⊗ y) (c ⊗ z) := by
  let : EnrichedCategory V (I × I) := Enriched.prodCategory V I I
  let G : EnrichedFunctor V I (I × I) :=
    { obj := fun x => (c, x)
      map := fun x y => (λ_ (x ⟶[V] y)).inv ≫
        (eId V c ⊗ₘ 𝟙 (x ⟶[V] y))
      map_id := fun x => by
        change eId V x ≫ (λ_ (x ⟶[V] x)).inv ≫
            (eId V c ⊗ₘ 𝟙 (x ⟶[V] x)) =
          (λ_ (𝟙_ V)).inv ≫ (eId V c ⊗ₘ eId V x)
        rw [leftUnitor_inv_naturality_assoc]
        slice_lhs 2 3 =>
          rw [← id_tensorHom, tensorHom_comp_tensorHom]
          simp
      map_comp := fun x y z => by
        have hIdentity : (eId V c ⊗ₘ eId V c) ≫ eComp V c c c =
            (λ_ (𝟙_ V)).hom ≫ eId V c := by
          rw [← cancel_epi (λ_ (𝟙_ V)).inv]
          simp only [Iso.inv_hom_id_assoc]
          rw [leftUnitor_inv_comp_tensorHom_assoc, e_id_comp,
            Category.comp_id]
        have hTensorUnit {X Y Z : V} (f : (𝟙_ V) ⟶ Y) (g : X ⟶ Z) :
            f ⊗ₘ g = (λ_ X).hom ≫ g ≫ (λ_ Z).inv ≫ f ▷ Z := by
          rw [← cancel_epi (λ_ X).inv]
          simp only [Iso.inv_hom_id_assoc]
          exact leftUnitor_inv_comp_tensorHom f g
        change eComp V x y z ≫ (λ_ (x ⟶[V] z)).inv ≫
            (eId V c ⊗ₘ 𝟙 (x ⟶[V] z)) =
          (((λ_ (x ⟶[V] y)).inv ≫
              (eId V c ⊗ₘ 𝟙 (x ⟶[V] y))) ⊗ₘ
            ((λ_ (y ⟶[V] z)).inv ≫
              (eId V c ⊗ₘ 𝟙 (y ⟶[V] z)))) ≫
            tensorμ (c ⟶[V] c) (x ⟶[V] y) (c ⟶[V] c) (y ⟶[V] z) ≫
            (eComp V c c c ⊗ₘ eComp V x y z)
        rw [← cancel_epi (λ_ ((x ⟶[V] y) ⊗ (y ⟶[V] z))).hom]
        nth_rewrite 2 [MonoidalCategory.tensor_left_unitality]
        simp only [Category.assoc]
        rw [tensorHom_comp_tensorHom_assoc]
        simp only [Iso.hom_inv_id_assoc]
        rw [tensorμ_natural_assoc, tensorHom_comp_tensorHom]
        simp only [id_tensorHom_id, Category.id_comp]
        rw [hIdentity]
        nth_rewrite 2 [← Category.id_comp (eComp V x y z)]
        rw [← tensorHom_comp_tensorHom]
        simp only [tensorHom_id]
        rw [hTensorUnit, ← MonoidalCategory.leftUnitor_monoidal_assoc,
          ← MonoidalCategory.tensor_left_unitality_assoc] }
  have h := (G.comp V d.tensorEnrichedFunctor).map_comp x y z
  simpa only [EnrichedFunctor.comp, G,
    EnrichedMonoidalCategoryData.tensorEnrichedFunctor, Category.assoc] using h

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]

/-- The two actual source-associator paths for the late-first labels agree
by the original index pentagon. No enriched operator law is used. -/
private theorem orderedIndexAssociatorPentagonForProof (c b a n : I) :
    ((α_ c b a).hom ⊗ₘ 𝟙 n) ≫ (α_ c (b ⊗ a) n).hom ≫
        c ◁ (α_ b a n).hom =
      (α_ (c ⊗ b) a n).hom ≫ (α_ c b (a ⊗ n)).hom := by
  simpa only [tensorHom_id] using MonoidalCategory.pentagon c b a n

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The actual fixed-left tensor functor, used only inside the index proof. -/
private abbrev leftTensorForIndexCube (d : EnrichedMonoidalCategoryData V I) (c : I) :
    EnrichedFunctor V I I where
  obj x := c ⊗ x
  map x y := (λ_ (x ⟶[V] y)).inv ≫
    (eId V c ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap c c x y
  map_id x := by
    simpa only [eHomEquiv_id, MonoidalCategory.whiskerLeft_id] using
      fixedLeftTensorPointForAssociativity d c x x (𝟙 x)
  map_comp x y z := fixedLeftTensorCompForAssociativity d c x y z

private theorem leftTensorPointForIndexCube
    (d : EnrichedMonoidalCategoryData V I) (c x y : I) (f : x ⟶ y) :
    eHomEquiv V f ≫ (leftTensorForIndexCube d c).map x y =
      eHomEquiv V (c ◁ f) :=
  fixedLeftTensorPointForAssociativity d c x y f

private theorem leftTensorPreForIndexCube
    (d : EnrichedMonoidalCategoryData V I) (c x y z : I) (f : x ⟶ y) :
    eHomWhiskerRight V f z ≫ (leftTensorForIndexCube d c).map x z =
      (leftTensorForIndexCube d c).map y z ≫
        eHomWhiskerRight V (c ◁ f) (c ⊗ z) := by
  have hp := leftTensorPointForIndexCube d c x y f
  have hr := congrArg
    (fun p : (𝟙_ V) ⟶ ((c ⊗ x) ⟶[V] (c ⊗ y)) =>
      (eHomEquiv V).symm p) hp
  simp only [Equiv.symm_apply_apply] at hr
  have h := enrichedFunctorFullPrecompositionForProof
    (leftTensorForIndexCube d c) x y z f
  have hWhisker := congrArg
    (fun f : (c ⊗ x) ⟶ (c ⊗ y) => eHomWhiskerRight V f (c ⊗ z)) hr
  have hTail := congrArg
    (fun g : ((c ⊗ y) ⟶[V] (c ⊗ z)) ⟶
        ((c ⊗ x) ⟶[V] (c ⊗ z)) =>
      (leftTensorForIndexCube d c).map y z ≫ g) hWhisker
  exact h.trans hTail

private theorem leftTensorAssocForIndexCube
    (d : EnrichedMonoidalCategoryData V I) (c b x y : I) :
    (leftTensorForIndexCube d (c ⊗ b)).map x y ≫
        eHomWhiskerLeft V ((c ⊗ b) ⊗ x) (α_ c b y).hom =
      ((leftTensorForIndexCube d b).map x y ≫
        (leftTensorForIndexCube d c).map (b ⊗ x) (b ⊗ y)) ≫
        eHomWhiskerRight V (α_ c b x).hom (c ⊗ (b ⊗ y)) := by
  simpa only [leftTensorForIndexCube, Category.assoc] using
    associator_third_full_hom d c b x y

/-- The original raw index map, with the same full selected tensor action. -/
private theorem indexGeneratorSelectedForCube
    (d : EnrichedMonoidalCategoryData V I) (n m k a b : I) :
    indexGenerator d n m k a b =
      (((leftTensorForIndexCube d b).map (a ⊗ n) m ⊗ₘ
        𝟙 ((b ⊗ m) ⟶[V] k)) ≫
        eComp V (b ⊗ (a ⊗ n)) (b ⊗ m) k) ≫
        eHomWhiskerRight V (α_ b a n).hom k := by
  simp only [indexGenerator, leftTensorForIndexCube, eHomWhiskerRight,
    tensorHom_id, Category.assoc]

omit [BraidedCategory V] [MonoidalCategory I] in
/-- Move the actual middle index isomorphism across the complete eComp map. -/
private theorem middleIsoTransportForIndexCube (X Y Y' Z : I) (e : Y ≅ Y') :
    (eHomWhiskerLeft V X e.hom ▷ (Y' ⟶[V] Z)) ≫ eComp V X Y' Z =
      (X ⟶[V] Y) ◁ eHomWhiskerRight V e.hom Z ≫ eComp V X Y Z := by
  have h := eHom_whisker_cancel V (X := X) (Z := Z) e
  have ht := congrArg
    (fun f : ((X ⟶[V] Y) ⊗ (Y ⟶[V] Z)) ⟶ (X ⟶[V] Z) =>
      ((X ⟶[V] Y) ◁ eHomWhiskerRight V e.hom Z) ≫ f) h
  rw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← eHomWhiskerRight_comp, e.inv_hom_id, eHomWhiskerRight_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp] at ht
  exact ht

/-- The complete original three-index generator cube. The Hom convention is
early-first and the labels are late-first; no operator category law is an input. -/
theorem indexGenerator_assoc
    (d : EnrichedMonoidalCategoryData V I) (n m k l a b c : I) :
    (indexGenerator d n m k a b ▷ ((c ⊗ k) ⟶[V] l)) ≫
        indexGenerator d n k l (b ⊗ a) c ≫
        eHomWhiskerRight V ((α_ c b a).hom ⊗ₘ 𝟙 n) l =
      (α_ ((a ⊗ n) ⟶[V] m) ((b ⊗ m) ⟶[V] k)
          ((c ⊗ k) ⟶[V] l)).hom ≫
        ((a ⊗ n) ⟶[V] m) ◁ indexGenerator d m k l b c ≫
        indexGenerator d n m l a (c ⊗ b) := by
  let W : V := (a ⊗ n) ⟶[V] m
  let Z : V := (b ⊗ m) ⟶[V] k
  let T : V := (c ⊗ k) ⟶[V] l
  let B0 : I := b ⊗ (a ⊗ n)
  let B1 : I := b ⊗ m
  let U0 : I := c ⊗ B0
  let U1 : I := c ⊗ B1
  let U2 : I := c ⊗ k
  let Qn : I := (c ⊗ (b ⊗ a)) ⊗ n
  let Rn : I := ((c ⊗ b) ⊗ a) ⊗ n
  let H0 : V := U0 ⟶[V] U1
  let H1 : V := U1 ⟶[V] U2
  let qb : W ⟶ (B0 ⟶[V] B1) :=
    (leftTensorForIndexCube d b).map (a ⊗ n) m
  let qc : (B0 ⟶[V] B1) ⟶ H0 :=
    (leftTensorForIndexCube d c).map B0 B1
  let Amap : W ⟶ H0 := qb ≫ qc
  let Bmap : Z ⟶ H1 := (leftTensorForIndexCube d c).map B1 k
  let e01 : H0 ⊗ H1 ⟶ (U0 ⟶[V] U2) := eComp V U0 U1 U2
  let e02 : (U0 ⟶[V] U2) ⊗ T ⟶ (U0 ⟶[V] l) :=
    eComp V U0 U2 l
  let e12 : H1 ⊗ T ⟶ (U1 ⟶[V] l) := eComp V U1 U2 l
  let e03 : H0 ⊗ (U1 ⟶[V] l) ⟶ (U0 ⟶[V] l) :=
    eComp V U0 U1 l
  let Kmap : (W ⊗ Z) ⊗ T ⟶ (U0 ⟶[V] l) :=
    ((Amap ⊗ₘ Bmap) ⊗ₘ 𝟙 T) ≫ (e01 ▷ T) ≫ e02
  let ab : W ⊗ Z ⟶ (((b ⊗ a) ⊗ n) ⟶[V] k) :=
    indexGenerator d n m k a b
  let bc : Z ⊗ T ⟶ (((c ⊗ b) ⊗ m) ⟶[V] l) :=
    indexGenerator d m k l b c
  let JL : (W ⊗ Z) ⊗ T ⟶ (Qn ⟶[V] l) :=
    (ab ▷ T) ≫ indexGenerator d n k l (b ⊗ a) c
  let JR : W ⊗ (Z ⊗ T) ⟶ (Rn ⟶[V] l) :=
    (W ◁ bc) ≫ indexGenerator d n m l a (c ⊗ b)
  let eb : ((b ⊗ a) ⊗ n) ⟶ B0 := (α_ b a n).hom
  let el : Qn ⟶ c ⊗ ((b ⊗ a) ⊗ n) := (α_ c (b ⊗ a) n).hom
  let er : Rn ⟶ (c ⊗ b) ⊗ (a ⊗ n) :=
    (α_ (c ⊗ b) a n).hom
  let e0 : (c ⊗ b) ⊗ (a ⊗ n) ⟶ U0 :=
    (α_ c b (a ⊗ n)).hom
  let e1 : (c ⊗ b) ⊗ m ≅ U1 := α_ c b m
  let label : Rn ⟶ Qn := (α_ c b a).hom ⊗ₘ 𝟙 n
  let sl : Qn ⟶ U0 := el ≫ c ◁ eb
  let sr : Rn ⟶ U0 := er ≫ e0
  suffices hGoal : JL ≫ eHomWhiskerRight V label l =
      (α_ W Z T).hom ≫ JR by
    simpa only [JL, JR, ab, bc, W, Z, T, label, Category.assoc] using hGoal
  have hAB : ab = (qb ⊗ₘ 𝟙 Z) ≫ eComp V B0 B1 k ≫
      eHomWhiskerRight V eb k := by
    simpa only [ab, qb, B0, B1, W, Z, eb, Category.assoc] using
      indexGeneratorSelectedForCube d n m k a b
  have hPre : eHomWhiskerRight V eb k ≫
      (leftTensorForIndexCube d c).map ((b ⊗ a) ⊗ n) k =
      (leftTensorForIndexCube d c).map B0 k ≫
        eHomWhiskerRight V (c ◁ eb) U2 :=
    leftTensorPreForIndexCube d c ((b ⊗ a) ⊗ n) B0 k eb
  have hMap : eComp V B0 B1 k ≫
      (leftTensorForIndexCube d c).map B0 k =
      (qc ⊗ₘ Bmap) ≫ e01 := by
    simpa only [qc, Bmap, e01, H0, H1, U0, U1, U2] using
      (leftTensorForIndexCube d c).map_comp B0 B1 k
  have hPair : (qb ⊗ₘ 𝟙 Z) ≫ (qc ⊗ₘ Bmap) = Amap ⊗ₘ Bmap := by
    simpa only [Amap, Category.id_comp] using
      tensorHom_comp_tensorHom qb (𝟙 Z) qc Bmap
  have hABmap : ab ≫
      (leftTensorForIndexCube d c).map ((b ⊗ a) ⊗ n) k =
      (Amap ⊗ₘ Bmap) ≫ e01 ≫ eHomWhiskerRight V (c ◁ eb) U2 := by
    calc
      ab ≫ (leftTensorForIndexCube d c).map ((b ⊗ a) ⊗ n) k =
          (qb ⊗ₘ 𝟙 Z) ≫ eComp V B0 B1 k ≫
          (eHomWhiskerRight V eb k ≫
            (leftTensorForIndexCube d c).map ((b ⊗ a) ⊗ n) k) := by
        rw [hAB]
        simp only [Category.assoc]
      _ = (qb ⊗ₘ 𝟙 Z) ≫ eComp V B0 B1 k ≫
          (leftTensorForIndexCube d c).map B0 k ≫
          eHomWhiskerRight V (c ◁ eb) U2 := by
        rw [hPre]
      _ = (qb ⊗ₘ 𝟙 Z) ≫ ((qc ⊗ₘ Bmap) ≫ e01) ≫
          eHomWhiskerRight V (c ◁ eb) U2 := by
        simpa only [Category.assoc] using congrArg
          (fun f : ((B0 ⟶[V] B1) ⊗ Z) ⟶ (U0 ⟶[V] U2) =>
            (qb ⊗ₘ 𝟙 Z) ≫ f ≫ eHomWhiskerRight V (c ◁ eb) U2) hMap
      _ = ((qb ⊗ₘ 𝟙 Z) ≫ (qc ⊗ₘ Bmap)) ≫ e01 ≫
          eHomWhiskerRight V (c ◁ eb) U2 := by
        simp only [Category.assoc]
      _ = (Amap ⊗ₘ Bmap) ≫ e01 ≫
          eHomWhiskerRight V (c ◁ eb) U2 := by
        rw [hPair]
  have hOuterLeft : indexGenerator d n k l (b ⊗ a) c =
      (((leftTensorForIndexCube d c).map ((b ⊗ a) ⊗ n) k ⊗ₘ 𝟙 T) ≫
        eComp V (c ⊗ ((b ⊗ a) ⊗ n)) U2 l) ≫
        eHomWhiskerRight V el l := by
    simpa only [T, U2, el, Category.assoc] using
      indexGeneratorSelectedForCube d n k l (b ⊗ a) c
  have hShiftLeft :
      (eHomWhiskerRight V (c ◁ eb) U2 ▷ T) ≫
          eComp V (c ⊗ ((b ⊗ a) ⊗ n)) U2 l =
        e02 ≫ eHomWhiskerRight V (c ◁ eb) l := by
    simpa only [e02, U0, B0, T, U2] using
      (eComp_eHomWhiskerRight V (c ◁ eb) U2 l).symm
  have hSL : eHomWhiskerRight V (c ◁ eb) l ≫
      eHomWhiskerRight V el l = eHomWhiskerRight V sl l := by
    simpa only [sl] using (eHomWhiskerRight_comp V el (c ◁ eb) l).symm
  have hJL : JL = Kmap ≫ eHomWhiskerRight V sl l := by
    change (ab ▷ T) ≫ indexGenerator d n k l (b ⊗ a) c =
      Kmap ≫ eHomWhiskerRight V sl l
    calc
      _ = (ab ▷ T) ≫
          ((leftTensorForIndexCube d c).map ((b ⊗ a) ⊗ n) k ⊗ₘ 𝟙 T) ≫
          eComp V (c ⊗ ((b ⊗ a) ⊗ n)) U2 l ≫
          eHomWhiskerRight V el l := by
        rw [hOuterLeft]
        simp only [Category.assoc]
      _ = (ab ≫ (leftTensorForIndexCube d c).map ((b ⊗ a) ⊗ n) k) ▷ T ≫
          eComp V (c ⊗ ((b ⊗ a) ⊗ n)) U2 l ≫
          eHomWhiskerRight V el l := by
        simp only [tensorHom_id, MonoidalCategory.comp_whiskerRight,
          Category.assoc]
      _ = (((Amap ⊗ₘ Bmap) ≫ e01) ▷ T) ≫
          (eHomWhiskerRight V (c ◁ eb) U2 ▷ T) ≫
          eComp V (c ⊗ ((b ⊗ a) ⊗ n)) U2 l ≫
          eHomWhiskerRight V el l := by
        rw [hABmap]
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = (((Amap ⊗ₘ Bmap) ≫ e01) ▷ T) ≫ e02 ≫
          eHomWhiskerRight V (c ◁ eb) l ≫ eHomWhiskerRight V el l := by
        simpa only [Category.assoc] using congrArg
          (fun f : ((U0 ⟶[V] U2) ⊗ T) ⟶
              ((c ⊗ ((b ⊗ a) ⊗ n)) ⟶[V] l) =>
            (((Amap ⊗ₘ Bmap) ≫ e01) ▷ T) ≫ f ≫
              eHomWhiskerRight V el l) hShiftLeft
      _ = (((Amap ⊗ₘ Bmap) ≫ e01) ▷ T) ≫ e02 ≫
          eHomWhiskerRight V sl l := by
        simpa only [Category.assoc] using congrArg
          (fun f : (U0 ⟶[V] l) ⟶ (Qn ⟶[V] l) =>
            (((Amap ⊗ₘ Bmap) ≫ e01) ▷ T) ≫ e02 ≫ f) hSL
      _ = Kmap ≫ eHomWhiskerRight V sl l := by
        simp only [Kmap, tensorHom_id, MonoidalCategory.comp_whiskerRight,
          Category.assoc]
  let Xcb : I := (c ⊗ b) ⊗ (a ⊗ n)
  let Mcb : I := (c ⊗ b) ⊗ m
  let Acb : W ⟶ (Xcb ⟶[V] Mcb) :=
    (leftTensorForIndexCube d (c ⊗ b)).map (a ⊗ n) m
  let gBC : Z ⊗ T ⟶ (U1 ⟶[V] l) := (Bmap ⊗ₘ 𝟙 T) ≫ e12
  let pre1 : (U1 ⟶[V] l) ⟶ (Mcb ⟶[V] l) :=
    eHomWhiskerRight V e1.hom l
  let post1 : (Xcb ⟶[V] Mcb) ⟶ (Xcb ⟶[V] U1) :=
    eHomWhiskerLeft V Xcb e1.hom
  have hBC : bc = gBC ≫ pre1 := by
    simpa only [bc, gBC, pre1, Bmap, e12, U1, U2, B1, Z, T, e1,
      Category.assoc] using indexGeneratorSelectedForCube d m k l b c
  have hOuterRight : indexGenerator d n m l a (c ⊗ b) =
      (Acb ⊗ₘ 𝟙 (Mcb ⟶[V] l)) ≫ eComp V Xcb Mcb l ≫
        eHomWhiskerRight V er l := by
    simpa only [Acb, Xcb, Mcb, er, Category.assoc] using
      indexGeneratorSelectedForCube d n m l a (c ⊗ b)
  have hPairRight :
      (W ◁ (gBC ≫ pre1)) ≫ (Acb ⊗ₘ 𝟙 (Mcb ⟶[V] l)) =
        Acb ⊗ₘ (gBC ≫ pre1) := by
    simpa only [Category.id_comp, Category.comp_id, id_tensorHom] using
      tensorHom_comp_tensorHom (𝟙 W) (gBC ≫ pre1) Acb
        (𝟙 (Mcb ⟶[V] l))
  have hPairSplit : (Acb ⊗ₘ gBC) ≫ ((Xcb ⟶[V] Mcb) ◁ pre1) =
      Acb ⊗ₘ (gBC ≫ pre1) := by
    simpa only [Category.comp_id, id_tensorHom] using
      tensorHom_comp_tensorHom Acb gBC (𝟙 (Xcb ⟶[V] Mcb)) pre1
  have hMiddle : (post1 ▷ (U1 ⟶[V] l)) ≫ eComp V Xcb U1 l =
      ((Xcb ⟶[V] Mcb) ◁ pre1) ≫ eComp V Xcb Mcb l := by
    simpa only [post1, pre1, Xcb, Mcb, U1, B1] using
      middleIsoTransportForIndexCube Xcb Mcb U1 l e1
  have hPairPost : (Acb ⊗ₘ gBC) ≫ (post1 ▷ (U1 ⟶[V] l)) =
      (Acb ≫ post1) ⊗ₘ gBC := by
    simpa only [Category.comp_id, tensorHom_id] using
      tensorHom_comp_tensorHom Acb gBC post1 (𝟙 (U1 ⟶[V] l))
  have hAssociator : Acb ≫ post1 =
      Amap ≫ eHomWhiskerRight V e0 U1 := by
    simpa only [Acb, post1, Amap, qb, qc, B0, B1, U0, U1, Xcb, Mcb,
      e0, e1, W] using leftTensorAssocForIndexCube d c b (a ⊗ n) m
  have hPairSource :
      (Amap ⊗ₘ gBC) ≫ (eHomWhiskerRight V e0 U1 ▷ (U1 ⟶[V] l)) =
        (Amap ≫ eHomWhiskerRight V e0 U1) ⊗ₘ gBC := by
    simpa only [Category.comp_id, tensorHom_id] using
      tensorHom_comp_tensorHom Amap gBC (eHomWhiskerRight V e0 U1)
        (𝟙 (U1 ⟶[V] l))
  have hShiftRight :
      (eHomWhiskerRight V e0 U1 ▷ (U1 ⟶[V] l)) ≫ eComp V Xcb U1 l =
        e03 ≫ eHomWhiskerRight V e0 l := by
    simpa only [e03, U0, Xcb] using
      (eComp_eHomWhiskerRight V e0 U1 l).symm
  have hSR : eHomWhiskerRight V e0 l ≫ eHomWhiskerRight V er l =
      eHomWhiskerRight V sr l := by
    simpa only [sr] using (eHomWhiskerRight_comp V er e0 l).symm
  have hJR : JR = (Amap ⊗ₘ gBC) ≫ e03 ≫
      eHomWhiskerRight V sr l := by
    change (W ◁ bc) ≫ indexGenerator d n m l a (c ⊗ b) =
      (Amap ⊗ₘ gBC) ≫ e03 ≫ eHomWhiskerRight V sr l
    calc
      _ = (W ◁ (gBC ≫ pre1)) ≫ (Acb ⊗ₘ 𝟙 (Mcb ⟶[V] l)) ≫
          eComp V Xcb Mcb l ≫ eHomWhiskerRight V er l := by
        rw [hBC, hOuterRight]
      _ = (Acb ⊗ₘ (gBC ≫ pre1)) ≫ eComp V Xcb Mcb l ≫
          eHomWhiskerRight V er l := by
        simpa only [Category.assoc] using congrArg
          (fun f : W ⊗ (Z ⊗ T) ⟶
              (Xcb ⟶[V] Mcb) ⊗ (Mcb ⟶[V] l) =>
            f ≫ eComp V Xcb Mcb l ≫ eHomWhiskerRight V er l) hPairRight
      _ = (Acb ⊗ₘ gBC) ≫
          (((Xcb ⟶[V] Mcb) ◁ pre1) ≫ eComp V Xcb Mcb l) ≫
          eHomWhiskerRight V er l := by
        rw [← hPairSplit]
        simp only [Category.assoc]
      _ = (Acb ⊗ₘ gBC) ≫
          ((post1 ▷ (U1 ⟶[V] l)) ≫ eComp V Xcb U1 l) ≫
          eHomWhiskerRight V er l := by
        rw [← hMiddle]
      _ = ((Acb ≫ post1) ⊗ₘ gBC) ≫ eComp V Xcb U1 l ≫
          eHomWhiskerRight V er l := by
        simpa only [Category.assoc] using congrArg
          (fun f : W ⊗ (Z ⊗ T) ⟶
              (Xcb ⟶[V] U1) ⊗ (U1 ⟶[V] l) =>
            f ≫ eComp V Xcb U1 l ≫ eHomWhiskerRight V er l) hPairPost
      _ = ((Amap ≫ eHomWhiskerRight V e0 U1) ⊗ₘ gBC) ≫
          eComp V Xcb U1 l ≫ eHomWhiskerRight V er l := by
        rw [hAssociator]
      _ = (Amap ⊗ₘ gBC) ≫
          ((eHomWhiskerRight V e0 U1 ▷ (U1 ⟶[V] l)) ≫
            eComp V Xcb U1 l) ≫ eHomWhiskerRight V er l := by
        rw [← hPairSource]
        simp only [Category.assoc]
      _ = (Amap ⊗ₘ gBC) ≫ e03 ≫ eHomWhiskerRight V e0 l ≫
          eHomWhiskerRight V er l := by
        rw [hShiftRight]
        simp only [Category.assoc]
      _ = (Amap ⊗ₘ gBC) ≫ e03 ≫ eHomWhiskerRight V sr l := by
        simpa only [Category.assoc] using congrArg
          (fun f : (U0 ⟶[V] l) ⟶ (Rn ⟶[V] l) =>
            (Amap ⊗ₘ gBC) ≫ e03 ≫ f) hSR
  have hRightTensor :
      (Amap ⊗ₘ (Bmap ⊗ₘ 𝟙 T)) ≫ (H0 ◁ e12) = Amap ⊗ₘ gBC := by
    simpa only [gBC, Category.comp_id, id_tensorHom] using
      tensorHom_comp_tensorHom Amap (Bmap ⊗ₘ 𝟙 T) (𝟙 H0) e12
  have hNaturality : ((Amap ⊗ₘ Bmap) ⊗ₘ 𝟙 T) ≫ (α_ H0 H1 T).hom =
      (α_ W Z T).hom ≫ (Amap ⊗ₘ (Bmap ⊗ₘ 𝟙 T)) :=
    associator_naturality Amap Bmap (𝟙 T)
  have hEAssoc : (α_ H0 H1 T).hom ≫ (H0 ◁ e12) ≫ e03 =
      (e01 ▷ T) ≫ e02 := by
    simpa only [H0, H1, T, e01, e02, e12, e03, U2] using
      e_assoc' V U0 U1 U2 l
  have hJRCommon : (α_ W Z T).hom ≫ JR =
      Kmap ≫ eHomWhiskerRight V sr l := by
    calc
      _ = (α_ W Z T).hom ≫ (Amap ⊗ₘ gBC) ≫ e03 ≫
          eHomWhiskerRight V sr l := by
        rw [hJR]
      _ = (α_ W Z T).hom ≫ (Amap ⊗ₘ (Bmap ⊗ₘ 𝟙 T)) ≫
          (H0 ◁ e12) ≫ e03 ≫ eHomWhiskerRight V sr l := by
        rw [← hRightTensor]
        simp only [Category.assoc]
      _ = ((Amap ⊗ₘ Bmap) ⊗ₘ 𝟙 T) ≫ (α_ H0 H1 T).hom ≫
          (H0 ◁ e12) ≫ e03 ≫ eHomWhiskerRight V sr l := by
        simpa only [Category.assoc] using congrArg
          (fun f : (W ⊗ Z) ⊗ T ⟶ H0 ⊗ (H1 ⊗ T) =>
            f ≫ (H0 ◁ e12) ≫ e03 ≫ eHomWhiskerRight V sr l)
          hNaturality.symm
      _ = ((Amap ⊗ₘ Bmap) ⊗ₘ 𝟙 T) ≫
          (e01 ▷ T) ≫ e02 ≫ eHomWhiskerRight V sr l := by
        simpa only [Category.assoc] using congrArg
          (fun f : (H0 ⊗ H1) ⊗ T ⟶ (U0 ⟶[V] l) =>
            ((Amap ⊗ₘ Bmap) ⊗ₘ 𝟙 T) ≫ f ≫
              eHomWhiskerRight V sr l) hEAssoc
      _ = Kmap ≫ eHomWhiskerRight V sr l := by
        simp only [Kmap, Category.assoc]
  have hPaths : label ≫ sl = sr := by
    simpa only [label, sl, sr, el, er, e0, eb, tensorHom_id,
      Category.assoc] using orderedIndexAssociatorPentagonForProof c b a n
  have hPrePaths : eHomWhiskerRight V sl l ≫
      eHomWhiskerRight V label l = eHomWhiskerRight V sr l :=
    (eHomWhiskerRight_comp V label sl l).symm.trans
      (congrArg (fun f : Rn ⟶ U0 => eHomWhiskerRight V f l) hPaths)
  calc
    JL ≫ eHomWhiskerRight V label l = Kmap ≫
        eHomWhiskerRight V sl l ≫ eHomWhiskerRight V label l := by
      rw [hJL]
      simp only [Category.assoc]
    _ = Kmap ≫ eHomWhiskerRight V sr l :=
      congrArg (fun f : (U0 ⟶[V] l) ⟶ (Rn ⟶[V] l) => Kmap ≫ f)
        hPrePaths
    _ = (α_ W Z T).hom ≫ JR := hJRCommon.symm

end CategoryTheory.Enriched.SphereOperator
