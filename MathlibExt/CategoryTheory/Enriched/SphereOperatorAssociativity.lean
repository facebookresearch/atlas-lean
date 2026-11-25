/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorUnit
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexGeneratorAssociativity
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorTripleTensor

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits BraidedCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]

/-- The literal tensor reorder used by the original composition generator. -/
private abbrev orderedTensoratorForAssoc (W Z A B : V) :
    (W ⊗ A) ⊗ (Z ⊗ B) ⟶ (W ⊗ Z) ⊗ (B ⊗ A) :=
  tensorδ W Z A B ≫ (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom)

/-- Naturality of the inverse mixed tensorator uses the canonical tensor
functor's oplax monoidal naturality. -/
private theorem tensorDeltaNaturalityForAssoc
    {W Z A B W' Z' A' B' : V}
    (f : W ⟶ W') (g : Z ⟶ Z') (p : A ⟶ A') (q : B ⟶ B') :
    ((f ⊗ₘ p) ⊗ₘ (g ⊗ₘ q)) ≫ tensorδ W' Z' A' B' =
      tensorδ W Z A B ≫ ((f ⊗ₘ g) ⊗ₘ (p ⊗ₘ q)) := by
  have h := Functor.OplaxMonoidal.δ_natural (MonoidalCategory.tensor V)
    (show (W, Z) ⟶ (W', Z') from (f, g))
    (show (A, B) ⟶ (A', B') from (p, q))
  simp only [MonoidalCategory.tensor_δ] at h
  change tensorδ W Z A B ≫ ((f ⊗ₘ g) ⊗ₘ (p ⊗ₘ q)) =
    ((f ⊗ₘ p) ⊗ₘ (g ⊗ₘ q)) ≫ tensorδ W' Z' A' B' at h
  exact h.symm

/-- The entire Hom and coefficient factors remain in the ordered tensorator
square; the final coefficient braid is positive and reverses their order. -/
private theorem orderedTensoratorNaturalityForAssoc
    {W Z A B W' Z' A' B' : V}
    (f : W ⟶ W') (g : Z ⟶ Z') (p : A ⟶ A') (q : B ⟶ B') :
    ((f ⊗ₘ p) ⊗ₘ (g ⊗ₘ q)) ≫
        orderedTensoratorForAssoc W' Z' A' B' =
      orderedTensoratorForAssoc W Z A B ≫
        ((f ⊗ₘ g) ⊗ₘ (q ⊗ₘ p)) := by
  have hDelta := tensorDeltaNaturalityForAssoc f g p q
  have hBraid :
      ((f ⊗ₘ g) ⊗ₘ (p ⊗ₘ q)) ≫
          (𝟙 (W' ⊗ Z') ⊗ₘ (β_ A' B').hom) =
        (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom) ≫
          ((f ⊗ₘ g) ⊗ₘ (q ⊗ₘ p)) := by
    simpa only [MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp] using
      congrArg (fun t : A ⊗ B ⟶ B' ⊗ A' => (f ⊗ₘ g) ⊗ₘ t)
        (braiding_naturality p q)
  dsimp only [orderedTensoratorForAssoc]
  calc
    _ = (((f ⊗ₘ p) ⊗ₘ (g ⊗ₘ q)) ≫ tensorδ W' Z' A' B') ≫
        (𝟙 (W' ⊗ Z') ⊗ₘ (β_ A' B').hom) :=
      (Category.assoc _ _ _).symm
    _ = (tensorδ W Z A B ≫ ((f ⊗ₘ g) ⊗ₘ (p ⊗ₘ q))) ≫
        (𝟙 (W' ⊗ Z') ⊗ₘ (β_ A' B').hom) :=
      congrArg (fun t : (W ⊗ A) ⊗ (Z ⊗ B) ⟶
        (W' ⊗ Z') ⊗ (A' ⊗ B') =>
        t ≫ (𝟙 (W' ⊗ Z') ⊗ₘ (β_ A' B').hom)) hDelta
    _ = tensorδ W Z A B ≫
        (((f ⊗ₘ g) ⊗ₘ (p ⊗ₘ q)) ≫
          (𝟙 (W' ⊗ Z') ⊗ₘ (β_ A' B').hom)) := Category.assoc _ _ _
    _ = tensorδ W Z A B ≫
        ((𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom) ≫
          ((f ⊗ₘ g) ⊗ₘ (q ⊗ₘ p))) :=
      congrArg (fun t : (W ⊗ Z) ⊗ (A ⊗ B) ⟶
        (W' ⊗ Z') ⊗ (B' ⊗ A') => tensorδ W Z A B ≫ t) hBraid
    _ = _ := (Category.assoc _ _ _).symm

omit [BraidedCategory V] in
/-- The ordinary arrow of the self enrichment is its entire unit-point action. -/
private theorem coefficientOrdinaryPointForAssoc [MonoidalClosed V]
    (P Q H : V) (e : (𝟙_ V) ⟶ H) (f : H ⟶ (ihom P).obj Q) :
    (eHomEquiv V (C := V) (X := P) (Y := Q)).symm (e ≫ f) =
      (ρ_ P).inv ≫ P ◁ e ≫ MonoidalClosed.uncurry f := by
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
  change (ρ_ P).inv ≫ MonoidalClosed.uncurry (e ≫ f) =
    (ρ_ P).inv ≫ P ◁ e ≫ MonoidalClosed.uncurry f
  exact congrArg (fun t : P ⊗ (𝟙_ V) ⟶ Q => (ρ_ P).inv ≫ t)
    (MonoidalClosed.uncurry_natural_left (C := V) e f)

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

open Limits BraidedCategory Opposite

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- Normalize the original coefficient associativity at the actual source associator.
No associativity law for the operator is supplied. -/
private theorem coefficientAssociatorPointForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (c b a : I) :
    (L.mu c b ▷ S.obj a) ≫ L.mu (c ⊗ b) a ≫
        (ρ_ (S.obj ((c ⊗ b) ⊗ a))).inv ≫
        S.obj ((c ⊗ b) ⊗ a) ◁ eHomEquiv V (α_ c b a).hom ≫
        MonoidalClosed.uncurry
          (S.map ((c ⊗ b) ⊗ a) (c ⊗ (b ⊗ a))) =
      (α_ (S.obj c) (S.obj b) (S.obj a)).hom ≫
        S.obj c ◁ L.mu b a ≫ L.mu c (b ⊗ a) := by
  have h := L.assoc c b a
  rw [coefficientOrdinaryPointForAssoc] at h
  simpa only [Category.assoc] using h

variable (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (n l : I)
  [HasCoproduct (weightedCoend.relations (weight d n l) S)]
  [HasCoproduct (weightedCoend.objects (weight d n l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n l) S)
    (weightedCoend.rightMap (weight d n l) S)]

/-- The complete target relation moves the actual source associator from its
weight factor to its coefficient factor. Both original relation faces are used. -/
private theorem targetAssociatorPointRelationForProof (c b a : I) :
    (eHomWhiskerRight V ((α_ c b a).hom ⊗ₘ 𝟙 n) l ⊗ₘ
        𝟙 (S.obj ((c ⊗ b) ⊗ a))) ≫
        weightedCoend.ι (weight d n l) S ((c ⊗ b) ⊗ a) =
      (𝟙 (((c ⊗ (b ⊗ a)) ⊗ n) ⟶[V] l) ⊗ₘ
        ((ρ_ (S.obj ((c ⊗ b) ⊗ a))).inv ≫
          S.obj ((c ⊗ b) ⊗ a) ◁ eHomEquiv V (α_ c b a).hom ≫
          MonoidalClosed.uncurry
            (S.map ((c ⊗ b) ⊗ a) (c ⊗ (b ⊗ a))))) ≫
        weightedCoend.ι (weight d n l) S (c ⊗ (b ⊗ a)) := by
  let R : I := (c ⊗ b) ⊗ a
  let T : I := c ⊗ (b ⊗ a)
  let r : R ⟶ T := (α_ c b a).hom
  let W : EnrichedFunctor V Iᵒᵖ V := weight d n l
  let U : V := W.obj (op T)
  let X : V := S.obj R
  let Y : V := S.obj T
  let wa : U ⟶ W.obj (op R) :=
    (ρ_ U).inv ≫ U ◁ eHomEquiv V r ≫
      MonoidalClosed.uncurry (W.map (op T) (op R))
  let fa : X ⟶ Y := (ρ_ X).inv ≫ X ◁ eHomEquiv V r ≫
    MonoidalClosed.uncurry (S.map R T)
  have hPoint : (wa ⊗ₘ 𝟙 X) ≫ weightedCoend.ι W S R =
      (𝟙 U ⊗ₘ fa) ≫ weightedCoend.ι W S T :=
    CategoryTheory.Enriched.weightedCoend.condition_unitPoint W S R T (eHomEquiv V r)
  have hWeight : wa = eHomWhiskerRight V (r ⊗ₘ 𝟙 n) l :=
    weight_point_pre d n l R T r
  have hSource :
      (eHomWhiskerRight V (r ⊗ₘ 𝟙 n) l ⊗ₘ 𝟙 X) ≫
          weightedCoend.ι W S R =
        (wa ⊗ₘ 𝟙 X) ≫ weightedCoend.ι W S R :=
    congrArg (fun f : U ⟶ W.obj (op R) =>
      (f ⊗ₘ 𝟙 X) ≫ weightedCoend.ι W S R) hWeight.symm
  simpa only [W, U, R, T, r, X, Y, fa, weight_obj, Category.assoc] using
    hSource.trans hPoint

/-- The target coend relation and the original coefficient associativity give
the exact late-first triple tensorator transfer for an arbitrary full Hom map. -/
private theorem targetAssociatorTensoratorTransferForProof
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (c b a : I) (P : V) (q : P ⟶ (((c ⊗ (b ⊗ a)) ⊗ n) ⟶[V] l)) :
    (q ⊗ₘ ((L.mu c b ▷ S.obj a) ≫ L.mu (c ⊗ b) a)) ≫
        (eHomWhiskerRight V ((α_ c b a).hom ⊗ₘ 𝟙 n) l ⊗ₘ
          𝟙 (S.obj ((c ⊗ b) ⊗ a))) ≫
        weightedCoend.ι (weight d n l) S ((c ⊗ b) ⊗ a) =
      (q ⊗ₘ ((α_ (S.obj c) (S.obj b) (S.obj a)).hom ≫
          S.obj c ◁ L.mu b a ≫ L.mu c (b ⊗ a))) ≫
        weightedCoend.ι (weight d n l) S (c ⊗ (b ⊗ a)) := by
  let R : I := (c ⊗ b) ⊗ a
  let T : I := c ⊗ (b ⊗ a)
  let U : V := (T ⊗ n) ⟶[V] l
  let X : V := S.obj R
  let Y : V := S.obj T
  let K : V := (S.obj c ⊗ S.obj b) ⊗ S.obj a
  let t : K ⟶ X := (L.mu c b ▷ S.obj a) ≫ L.mu (c ⊗ b) a
  let u : K ⟶ Y := (α_ (S.obj c) (S.obj b) (S.obj a)).hom ≫
    S.obj c ◁ L.mu b a ≫ L.mu c (b ⊗ a)
  let f : X ⟶ Y := (ρ_ X).inv ≫ X ◁ eHomEquiv V (α_ c b a).hom ≫
    MonoidalClosed.uncurry (S.map R T)
  let p : U ⟶ ((R ⊗ n) ⟶[V] l) :=
    eHomWhiskerRight V ((α_ c b a).hom ⊗ₘ 𝟙 n) l
  have hTarget : (p ⊗ₘ 𝟙 X) ≫ weightedCoend.ι (weight d n l) S R =
      (𝟙 U ⊗ₘ f) ≫ weightedCoend.ι (weight d n l) S T :=
    targetAssociatorPointRelationForProof d S n l c b a
  have hCoefficient : t ≫ f = u := by
    simpa only [t, f, u, R, T, X, Y, Category.assoc] using
      coefficientAssociatorPointForProof d S L c b a
  have hPair : (q ⊗ₘ t) ≫ (𝟙 U ⊗ₘ f) = q ⊗ₘ (t ≫ f) := by
    exact (MonoidalCategory.tensorHom_comp_tensorHom q t (𝟙 U) f).trans
      (congrArg (fun z => z ⊗ₘ (t ≫ f)) (Category.comp_id q))
  change (q ⊗ₘ t) ≫ (p ⊗ₘ 𝟙 X) ≫
      weightedCoend.ι (weight d n l) S R =
    (q ⊗ₘ u) ≫ weightedCoend.ι (weight d n l) S T
  calc
    _ = (q ⊗ₘ t) ≫ ((𝟙 U ⊗ₘ f) ≫ weightedCoend.ι (weight d n l) S T) :=
      congrArg (fun h : U ⊗ X ⟶ Hom d S n l => (q ⊗ₘ t) ≫ h) hTarget
    _ = ((q ⊗ₘ t) ≫ (𝟙 U ⊗ₘ f)) ≫
        weightedCoend.ι (weight d n l) S T :=
      (Category.assoc (q ⊗ₘ t) (𝟙 U ⊗ₘ f)
        (weightedCoend.ι (weight d n l) S T)).symm
    _ = (q ⊗ₘ (t ≫ f)) ≫ weightedCoend.ι (weight d n l) S T :=
      congrArg (fun h : P ⊗ K ⟶ U ⊗ Y =>
        h ≫ weightedCoend.ι (weight d n l) S T) hPair
    _ = (q ⊗ₘ u) ≫ weightedCoend.ι (weight d n l) S T :=
      congrArg (fun h : K ⟶ Y =>
        (q ⊗ₘ h) ≫ weightedCoend.ι (weight d n l) S T) hCoefficient

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

open Limits BraidedCategory Opposite

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (n m k l : I)
  [HasCoproduct (weightedCoend.relations (weight d n m) S)]
  [HasCoproduct (weightedCoend.objects (weight d n m) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n m) S)
    (weightedCoend.rightMap (weight d n m) S)]
  [HasCoproduct (weightedCoend.relations (weight d m k) S)]
  [HasCoproduct (weightedCoend.objects (weight d m k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d m k) S)
    (weightedCoend.rightMap (weight d m k) S)]
  [HasCoproduct (weightedCoend.relations (weight d k l) S)]
  [HasCoproduct (weightedCoend.objects (weight d k l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d k l) S)
    (weightedCoend.rightMap (weight d k l) S)]

/-- The full three-Hom equality follows from all three actual preserved coend
universal properties. The generator equality is a proof obligation, not category data. -/
private theorem tripleCompositionSource_hom_extForProof {X : V}
    {f g : (Hom d S n m ⊗ Hom d S m k) ⊗ Hom d S k l ⟶ X}
    (h : ∀ a b c : I,
      ((weightedCoend.ι (weight d n m) S a ⊗ₘ
          weightedCoend.ι (weight d m k) S b) ⊗ₘ
          weightedCoend.ι (weight d k l) S c) ≫ f =
        ((weightedCoend.ι (weight d n m) S a ⊗ₘ
            weightedCoend.ι (weight d m k) S b) ⊗ₘ
            weightedCoend.ι (weight d k l) S c) ≫ g) : f = g := by
  apply weightedCoend.Mapped.hom_ext (weight d k l) S
    (tensorLeft (Hom d S n m ⊗ Hom d S m k))
  intro c
  let C : V := weightedCoend.objects (weight d k l) S c
  apply weightedCoend.Mapped.hom_ext (weight d m k) S
    (tensorLeft (Hom d S n m) ⋙ tensorRight C)
  intro b
  let B : V := weightedCoend.objects (weight d m k) S b
  apply weightedCoend.Mapped.hom_ext (weight d n m) S
    (tensorRight B ⋙ tensorRight C)
  intro a
  change ((weightedCoend.ι (weight d n m) S a ▷ B) ▷ C) ≫
      (((Hom d S n m ◁ weightedCoend.ι (weight d m k) S b) ▷ C) ≫
        ((Hom d S n m ⊗ Hom d S m k) ◁ weightedCoend.ι (weight d k l) S c) ≫ f) =
    ((weightedCoend.ι (weight d n m) S a ▷ B) ▷ C) ≫
      (((Hom d S n m ◁ weightedCoend.ι (weight d m k) S b) ▷ C) ≫
        ((Hom d S n m ⊗ Hom d S m k) ◁ weightedCoend.ι (weight d k l) S c) ≫ g)
  simpa only [MonoidalCategory.tensorHom_def, MonoidalCategory.comp_whiskerRight,
    Category.assoc] using h a b c

/-- The same three original coends detect the right-associated full Hom equation
used in the enriched-category associativity field. -/
private theorem tripleCompositionSource_right_hom_extForProof {X : V}
    {f g : Hom d S n m ⊗ (Hom d S m k ⊗ Hom d S k l) ⟶ X}
    (h : ∀ a b c : I,
      (weightedCoend.ι (weight d n m) S a ⊗ₘ
          (weightedCoend.ι (weight d m k) S b ⊗ₘ
            weightedCoend.ι (weight d k l) S c)) ≫ f =
        (weightedCoend.ι (weight d n m) S a ⊗ₘ
          (weightedCoend.ι (weight d m k) S b ⊗ₘ
            weightedCoend.ι (weight d k l) S c)) ≫ g) : f = g := by
  apply (cancel_epi (α_ (Hom d S n m) (Hom d S m k) (Hom d S k l)).hom).1
  apply tripleCompositionSource_hom_extForProof d S n m k l
  intro a b c
  let A : V := weightedCoend.objects (weight d n m) S a
  let B : V := weightedCoend.objects (weight d m k) S b
  let C : V := weightedCoend.objects (weight d k l) S c
  let u : A ⟶ Hom d S n m := weightedCoend.ι (weight d n m) S a
  let v : B ⟶ Hom d S m k := weightedCoend.ι (weight d m k) S b
  let w : C ⟶ Hom d S k l := weightedCoend.ι (weight d k l) S c
  have hNatural : ((u ⊗ₘ v) ⊗ₘ w) ≫
        (α_ (Hom d S n m) (Hom d S m k) (Hom d S k l)).hom =
      (α_ A B C).hom ≫ (u ⊗ₘ (v ⊗ₘ w)) :=
    associator_naturality u v w
  have hLeft := congrArg
    (fun q : (A ⊗ B) ⊗ C ⟶
        Hom d S n m ⊗ (Hom d S m k ⊗ Hom d S k l) => q ≫ f) hNatural
  have hRight := congrArg
    (fun q : (A ⊗ B) ⊗ C ⟶
        Hom d S n m ⊗ (Hom d S m k ⊗ Hom d S k l) => q ≫ g) hNatural
  have hGenerator := congrArg
    (fun q : A ⊗ (B ⊗ C) ⟶ X => (α_ A B C).hom ≫ q) (h a b c)
  change ((u ⊗ₘ v) ⊗ₘ w) ≫
      ((α_ (Hom d S n m) (Hom d S m k) (Hom d S k l)).hom ≫ f) =
    ((u ⊗ₘ v) ⊗ₘ w) ≫
      ((α_ (Hom d S n m) (Hom d S m k) (Hom d S k l)).hom ≫ g)
  calc
    _ = (α_ A B C).hom ≫ ((u ⊗ₘ (v ⊗ₘ w)) ≫ f) := by
      simpa only [Category.assoc] using hLeft
    _ = (α_ A B C).hom ≫ ((u ⊗ₘ (v ⊗ₘ w)) ≫ g) := hGenerator
    _ = _ := by
      simpa only [Category.assoc] using hRight.symm

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

open Limits BraidedCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]

/-- Naturality carries the complete first binary index and coefficient maps
through the second actual ordered tensorator. -/
private theorem leftBinaryTensoratorsForAssoc
    (W Z T A B C W' A' K D : V)
    (j : W ⊗ Z ⟶ W') (t : B ⊗ A ⟶ A')
    (k : W' ⊗ T ⟶ K) (u : C ⊗ A' ⟶ D) :
    (((orderedTensoratorForAssoc W Z A B ≫ (j ⊗ₘ t)) ⊗ₘ
        𝟙 (T ⊗ C)) ≫
        orderedTensoratorForAssoc W' T A' C) ≫ (k ⊗ₘ u) =
      (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
        orderedTensoratorForAssoc (W ⊗ Z) T (B ⊗ A) C ≫
        (((j ▷ T) ≫ k) ⊗ₘ ((C ◁ t) ≫ u)) := by
  have hSplit :
      ((orderedTensoratorForAssoc W Z A B ≫ (j ⊗ₘ t)) ⊗ₘ
          𝟙 (T ⊗ C)) =
        (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
          ((j ⊗ₘ t) ⊗ₘ 𝟙 (T ⊗ C)) := by
    simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.comp_whiskerRight]
  have hNatural :
      ((j ⊗ₘ t) ⊗ₘ 𝟙 (T ⊗ C)) ≫
          orderedTensoratorForAssoc W' T A' C =
        orderedTensoratorForAssoc (W ⊗ Z) T (B ⊗ A) C ≫
          ((j ⊗ₘ 𝟙 T) ⊗ₘ (𝟙 C ⊗ₘ t)) := by
    simpa only [MonoidalCategory.id_tensorHom_id] using
      orderedTensoratorNaturalityForAssoc j (𝟙 T) t (𝟙 C)
  have hJoin :
      ((j ⊗ₘ 𝟙 T) ⊗ₘ (𝟙 C ⊗ₘ t)) ≫ (k ⊗ₘ u) =
        (((j ▷ T) ≫ k) ⊗ₘ ((C ◁ t) ≫ u)) := by
    simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
      MonoidalCategory.tensorHom_comp_tensorHom (j ⊗ₘ 𝟙 T)
        (𝟙 C ⊗ₘ t) k u
  rw [hSplit]
  calc
    _ = (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
        ((((j ⊗ₘ t) ⊗ₘ 𝟙 (T ⊗ C)) ≫
          orderedTensoratorForAssoc W' T A' C) ≫ (k ⊗ₘ u)) := by
      simp only [Category.assoc]
    _ = (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
        ((orderedTensoratorForAssoc (W ⊗ Z) T (B ⊗ A) C ≫
          ((j ⊗ₘ 𝟙 T) ⊗ₘ (𝟙 C ⊗ₘ t))) ≫ (k ⊗ₘ u)) :=
      congrArg (fun f : ((W ⊗ Z) ⊗ (B ⊗ A)) ⊗ (T ⊗ C) ⟶
        (W' ⊗ T) ⊗ (C ⊗ A') =>
        (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫ f ≫
          (k ⊗ₘ u)) hNatural
    _ = (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
        orderedTensoratorForAssoc (W ⊗ Z) T (B ⊗ A) C ≫
        (((j ⊗ₘ 𝟙 T) ⊗ₘ (𝟙 C ⊗ₘ t)) ≫ (k ⊗ₘ u)) := by
      simp only [Category.assoc]
    _ = _ := congrArg
      (fun f : ((W ⊗ Z) ⊗ T) ⊗ (C ⊗ (B ⊗ A)) ⟶ K ⊗ D =>
        (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
          orderedTensoratorForAssoc (W ⊗ Z) T (B ⊗ A) C ≫ f) hJoin

/-- The complete second binary maps pass through the other ordered
tensorator, retaining the coefficient order (C tensor B) tensor A. -/
private theorem rightBinaryTensoratorsForAssoc
    (W Z T A B C Z' B' K D : V)
    (j : Z ⊗ T ⟶ Z') (t : C ⊗ B ⟶ B')
    (k : W ⊗ Z' ⟶ K) (u : B' ⊗ A ⟶ D) :
    ((𝟙 (W ⊗ A) ⊗ₘ
        (orderedTensoratorForAssoc Z T B C ≫ (j ⊗ₘ t))) ≫
        orderedTensoratorForAssoc W Z' A B') ≫ (k ⊗ₘ u) =
      ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
        orderedTensoratorForAssoc W (Z ⊗ T) A (C ⊗ B) ≫
        (((W ◁ j) ≫ k) ⊗ₘ ((t ▷ A) ≫ u)) := by
  have hSplit :
      (𝟙 (W ⊗ A) ⊗ₘ
          (orderedTensoratorForAssoc Z T B C ≫ (j ⊗ₘ t))) =
        ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
          (𝟙 (W ⊗ A) ⊗ₘ (j ⊗ₘ t)) := by
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.whiskerLeft_comp]
  have hNatural :
      (𝟙 (W ⊗ A) ⊗ₘ (j ⊗ₘ t)) ≫
          orderedTensoratorForAssoc W Z' A B' =
        orderedTensoratorForAssoc W (Z ⊗ T) A (C ⊗ B) ≫
          ((𝟙 W ⊗ₘ j) ⊗ₘ (t ⊗ₘ 𝟙 A)) := by
    simpa only [MonoidalCategory.id_tensorHom_id] using
      orderedTensoratorNaturalityForAssoc (𝟙 W) j (𝟙 A) t
  have hJoin :
      ((𝟙 W ⊗ₘ j) ⊗ₘ (t ⊗ₘ 𝟙 A)) ≫ (k ⊗ₘ u) =
        (((W ◁ j) ≫ k) ⊗ₘ ((t ▷ A) ≫ u)) := by
    simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using
      MonoidalCategory.tensorHom_comp_tensorHom (𝟙 W ⊗ₘ j)
        (t ⊗ₘ 𝟙 A) k u
  rw [hSplit]
  calc
    _ = ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
        (((𝟙 (W ⊗ A) ⊗ₘ (j ⊗ₘ t)) ≫
          orderedTensoratorForAssoc W Z' A B') ≫ (k ⊗ₘ u)) := by
      simp only [Category.assoc]
    _ = ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
        ((orderedTensoratorForAssoc W (Z ⊗ T) A (C ⊗ B) ≫
          ((𝟙 W ⊗ₘ j) ⊗ₘ (t ⊗ₘ 𝟙 A))) ≫ (k ⊗ₘ u)) :=
      congrArg (fun f : (W ⊗ A) ⊗ ((Z ⊗ T) ⊗ (C ⊗ B)) ⟶
        (W ⊗ Z') ⊗ (B' ⊗ A) =>
        ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫ f ≫
          (k ⊗ₘ u)) hNatural
    _ = ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
        orderedTensoratorForAssoc W (Z ⊗ T) A (C ⊗ B) ≫
        (((𝟙 W ⊗ₘ j) ⊗ₘ (t ⊗ₘ 𝟙 A)) ≫ (k ⊗ₘ u)) := by
      simp only [Category.assoc]
    _ = _ := congrArg
      (fun f : (W ⊗ (Z ⊗ T)) ⊗ ((C ⊗ B) ⊗ A) ⟶ K ⊗ D =>
        ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
          orderedTensoratorForAssoc W (Z ⊗ T) A (C ⊗ B) ≫ f) hJoin

variable [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (n m k l : I)
  [HasCoproduct (weightedCoend.relations (weight d n l) S)]
  [HasCoproduct (weightedCoend.objects (weight d n l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n l) S)
    (weightedCoend.rightMap (weight d n l) S)]

/-- Join the full index cube and the original coefficient associativity
through the actual target coend relation and the complete triple tensorator. -/
private theorem rawTripleTargetForAssoc (a b c : I) :
    (orderedTensoratorForAssoc ((a ⊗ n) ⟶[V] m) ((b ⊗ m) ⟶[V] k)
        (S.obj a) (S.obj b) ▷ (((c ⊗ k) ⟶[V] l) ⊗ S.obj c)) ≫
      orderedTensoratorForAssoc
        (((a ⊗ n) ⟶[V] m) ⊗ ((b ⊗ m) ⟶[V] k))
        ((c ⊗ k) ⟶[V] l) (S.obj b ⊗ S.obj a) (S.obj c) ≫
      (((indexGenerator d n m k a b ▷ ((c ⊗ k) ⟶[V] l)) ≫
          indexGenerator d n k l (b ⊗ a) c) ⊗ₘ
        ((S.obj c ◁ L.mu b a) ≫ L.mu c (b ⊗ a))) ≫
      weightedCoend.ι (weight d n l) S (c ⊗ (b ⊗ a)) =
    (α_ (((a ⊗ n) ⟶[V] m) ⊗ S.obj a)
        (((b ⊗ m) ⟶[V] k) ⊗ S.obj b)
        (((c ⊗ k) ⟶[V] l) ⊗ S.obj c)).hom ≫
      ((((a ⊗ n) ⟶[V] m) ⊗ S.obj a) ◁
        orderedTensoratorForAssoc ((b ⊗ m) ⟶[V] k) ((c ⊗ k) ⟶[V] l)
          (S.obj b) (S.obj c)) ≫
      orderedTensoratorForAssoc ((a ⊗ n) ⟶[V] m)
        (((b ⊗ m) ⟶[V] k) ⊗ ((c ⊗ k) ⟶[V] l))
        (S.obj a) (S.obj c ⊗ S.obj b) ≫
      ((((a ⊗ n) ⟶[V] m) ◁ indexGenerator d m k l b c ≫
          indexGenerator d n m l a (c ⊗ b)) ⊗ₘ
        ((L.mu c b ▷ S.obj a) ≫ L.mu (c ⊗ b) a)) ≫
      weightedCoend.ι (weight d n l) S ((c ⊗ b) ⊗ a) := by
  let W : V := (a ⊗ n) ⟶[V] m
  let Z : V := (b ⊗ m) ⟶[V] k
  let T : V := (c ⊗ k) ⟶[V] l
  let A : V := S.obj a
  let B : V := S.obj b
  let C : V := S.obj c
  let P : V := (W ⊗ Z) ⊗ T
  let Q : I := c ⊗ (b ⊗ a)
  let R : I := (c ⊗ b) ⊗ a
  let UQ : V := (Q ⊗ n) ⟶[V] l
  let UR : V := (R ⊗ n) ⟶[V] l
  let JL : P ⟶ UQ :=
    (indexGenerator d n m k a b ▷ T) ≫ indexGenerator d n k l (b ⊗ a) c
  let JR : W ⊗ (Z ⊗ T) ⟶ UR :=
    W ◁ indexGenerator d m k l b c ≫ indexGenerator d n m l a (c ⊗ b)
  let p : UQ ⟶ UR := eHomWhiskerRight V ((α_ c b a).hom ⊗ₘ 𝟙 n) l
  let tL : C ⊗ (B ⊗ A) ⟶ S.obj Q := C ◁ L.mu b a ≫ L.mu c (b ⊗ a)
  let tR : (C ⊗ B) ⊗ A ⟶ S.obj R :=
    (L.mu c b ▷ A) ≫ L.mu (c ⊗ b) a
  let iQ : UQ ⊗ S.obj Q ⟶ Hom d S n l :=
    weightedCoend.ι (weight d n l) S Q
  let iR : UR ⊗ S.obj R ⟶ Hom d S n l :=
    weightedCoend.ι (weight d n l) S R
  have hIndex : JL ≫ p = (α_ W Z T).hom ≫ JR := by
    simpa only [JL, JR, p, W, Z, T, Category.assoc] using
      indexGenerator_assoc d n m k l a b c
  have hMove :
      (JL ⊗ₘ tR) ≫ (p ⊗ₘ 𝟙 (S.obj R)) ≫ iR =
        (JL ⊗ₘ ((α_ C B A).hom ≫ tL)) ≫ iQ := by
    simpa only [JL, p, tR, tL, iR, iQ, R, Q, P, W, Z, T, A, B, C,
      Category.assoc] using
      targetAssociatorTensoratorTransferForProof d S n l L c b a P JL
  have hPre := congrArg
    (fun f : P ⊗ ((C ⊗ B) ⊗ A) ⟶ Hom d S n l =>
      (𝟙 P ⊗ₘ (α_ C B A).inv) ≫ f) hMove
  have hPreLeft :
      (𝟙 P ⊗ₘ (α_ C B A).inv) ≫
          ((JL ⊗ₘ tR) ≫ (p ⊗ₘ 𝟙 (S.obj R)) ≫ iR) =
        ((JL ≫ p) ⊗ₘ ((α_ C B A).inv ≫ tR)) ≫ iR := by
    simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id]
  have hPreRight :
      (𝟙 P ⊗ₘ (α_ C B A).inv) ≫
          ((JL ⊗ₘ ((α_ C B A).hom ≫ tL)) ≫ iQ) =
        (JL ⊗ₘ tL) ≫ iQ := by
    simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Iso.inv_hom_id_assoc]
  have hCoend :
      ((α_ W Z T).hom ⊗ₘ (α_ C B A).inv) ≫ (JR ⊗ₘ tR) ≫ iR =
        (JL ⊗ₘ tL) ≫ iQ := by
    have hOut :
        ((α_ W Z T).hom ⊗ₘ (α_ C B A).inv) ≫ (JR ⊗ₘ tR) ≫ iR =
          ((JL ≫ p) ⊗ₘ ((α_ C B A).inv ≫ tR)) ≫ iR := by
      simpa only [MonoidalCategory.tensorHom_comp_tensorHom_assoc] using
        congrArg (fun f : P ⟶ UR =>
          (f ⊗ₘ ((α_ C B A).inv ≫ tR)) ≫ iR) hIndex.symm
    exact hOut.trans (hPreLeft.symm.trans (hPre.trans hPreRight))
  let ΦL :
      ((W ⊗ A) ⊗ (Z ⊗ B)) ⊗ (T ⊗ C) ⟶
        P ⊗ (C ⊗ (B ⊗ A)) :=
    (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
      orderedTensoratorForAssoc (W ⊗ Z) T (B ⊗ A) C
  let ΦR :
      ((W ⊗ A) ⊗ (Z ⊗ B)) ⊗ (T ⊗ C) ⟶
        (W ⊗ (Z ⊗ T)) ⊗ ((C ⊗ B) ⊗ A) :=
    (α_ (W ⊗ A) (Z ⊗ B) (T ⊗ C)).hom ≫
      ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
      orderedTensoratorForAssoc W (Z ⊗ T) A (C ⊗ B)
  have hTriple :
      ΦL ≫ ((α_ W Z T).hom ⊗ₘ (α_ C B A).inv) = ΦR := by
    simpa only [ΦL, ΦR, orderedTensoratorForAssoc, Category.assoc] using
      tensorDelta_ordered_triple W Z T A B C
  have hJoined : ΦL ≫ (JL ⊗ₘ tL) ≫ iQ = ΦR ≫ (JR ⊗ₘ tR) ≫ iR := by
    calc
      _ = ΦL ≫
          (((α_ W Z T).hom ⊗ₘ (α_ C B A).inv) ≫ (JR ⊗ₘ tR) ≫ iR) :=
        congrArg (fun f : P ⊗ (C ⊗ (B ⊗ A)) ⟶ Hom d S n l => ΦL ≫ f)
          hCoend.symm
      _ = (ΦL ≫ ((α_ W Z T).hom ⊗ₘ (α_ C B A).inv)) ≫
          (JR ⊗ₘ tR) ≫ iR := by simp only [Category.assoc]
      _ = _ := congrArg
        (fun f : ((W ⊗ A) ⊗ (Z ⊗ B)) ⊗ (T ⊗ C) ⟶
          (W ⊗ (Z ⊗ T)) ⊗ ((C ⊗ B) ⊗ A) => f ≫ (JR ⊗ₘ tR) ≫ iR)
        hTriple
  simpa only [ΦL, ΦR, JL, JR, tL, tR, iQ, iR, Q, R, W, Z, T, A, B, C,
    Category.assoc] using hJoined

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

open Limits BraidedCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (n m k l : I)
  [HasCoproduct (weightedCoend.relations (weight d n m) S)]
  [HasCoproduct (weightedCoend.objects (weight d n m) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n m) S)
    (weightedCoend.rightMap (weight d n m) S)]
  [HasCoproduct (weightedCoend.relations (weight d m k) S)]
  [HasCoproduct (weightedCoend.objects (weight d m k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d m k) S)
    (weightedCoend.rightMap (weight d m k) S)]
  [HasCoproduct (weightedCoend.relations (weight d k l) S)]
  [HasCoproduct (weightedCoend.objects (weight d k l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d k l) S)
    (weightedCoend.rightMap (weight d k l) S)]
  [HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]
  [HasCoproduct (weightedCoend.relations (weight d m l) S)]
  [HasCoproduct (weightedCoend.objects (weight d m l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d m l) S)
    (weightedCoend.rightMap (weight d m l) S)]
  [HasCoproduct (weightedCoend.relations (weight d n l) S)]
  [HasCoproduct (weightedCoend.objects (weight d n l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n l) S)
    (weightedCoend.rightMap (weight d n l) S)]

omit [HasCoproduct (weightedCoend.relations (weight d n m) S)]
  [HasCoproduct (weightedCoend.objects (weight d n m) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n m) S)
    (weightedCoend.rightMap (weight d n m) S)]
  [HasCoproduct (weightedCoend.relations (weight d m k) S)]
  [HasCoproduct (weightedCoend.objects (weight d m k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d m k) S)
    (weightedCoend.rightMap (weight d m k) S)]
  [HasCoproduct (weightedCoend.relations (weight d m l) S)]
  [HasCoproduct (weightedCoend.objects (weight d m l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d m l) S)
    (weightedCoend.rightMap (weight d m l) S)] in
/-- Expand the first binary descent, then the second one, on their complete
original generators. Naturality keeps both index and coefficient maps. -/
private theorem leftRawCompositionForAssoc (a b c : I) :
    (compositionGenerator d S L n m k a b ⊗ₘ
        weightedCoend.ι (weight d k l) S c) ≫ composition d S L n k l =
      (orderedTensoratorForAssoc ((a ⊗ n) ⟶[V] m) ((b ⊗ m) ⟶[V] k)
          (S.obj a) (S.obj b) ▷ (((c ⊗ k) ⟶[V] l) ⊗ S.obj c)) ≫
        orderedTensoratorForAssoc
          (((a ⊗ n) ⟶[V] m) ⊗ ((b ⊗ m) ⟶[V] k))
          ((c ⊗ k) ⟶[V] l) (S.obj b ⊗ S.obj a) (S.obj c) ≫
        ((((indexGenerator d n m k a b ▷ ((c ⊗ k) ⟶[V] l)) ≫
            indexGenerator d n k l (b ⊗ a) c) ⊗ₘ
          ((S.obj c ◁ L.mu b a) ≫ L.mu c (b ⊗ a)))) ≫
        weightedCoend.ι (weight d n l) S (c ⊗ (b ⊗ a)) := by
  let W : V := (a ⊗ n) ⟶[V] m
  let Z : V := (b ⊗ m) ⟶[V] k
  let T : V := (c ⊗ k) ⟶[V] l
  let A : V := S.obj a
  let B : V := S.obj b
  let C : V := S.obj c
  let W' : V := ((b ⊗ a) ⊗ n) ⟶[V] k
  let A' : V := S.obj (b ⊗ a)
  let K : V := ((c ⊗ (b ⊗ a)) ⊗ n) ⟶[V] l
  let D : V := S.obj (c ⊗ (b ⊗ a))
  let j : W ⊗ Z ⟶ W' := indexGenerator d n m k a b
  let t : B ⊗ A ⟶ A' := L.mu b a
  let q : W' ⊗ T ⟶ K := indexGenerator d n k l (b ⊗ a) c
  let u : C ⊗ A' ⟶ D := L.mu c (b ⊗ a)
  let r : (W ⊗ A) ⊗ (Z ⊗ B) ⟶ W' ⊗ A' :=
    orderedTensoratorForAssoc W Z A B ≫ (j ⊗ₘ t)
  let iab : W' ⊗ A' ⟶ Hom d S n k :=
    weightedCoend.ι (weight d n k) S (b ⊗ a)
  let ic : T ⊗ C ⟶ Hom d S k l := weightedCoend.ι (weight d k l) S c
  let iout : K ⊗ D ⟶ Hom d S n l :=
    weightedCoend.ι (weight d n l) S (c ⊗ (b ⊗ a))
  have hGenerator : compositionGenerator d S L n m k a b = r ≫ iab := by
    have hLiteral : compositionGenerator d S L n m k a b =
        orderedTensoratorForAssoc W Z A B ≫ (j ⊗ₘ t) ≫ iab := by
          dsimp only [compositionGenerator, orderedTensoratorForAssoc,
            W, Z, A, B, j, t, iab]
          simp only [Category.assoc]
    exact hLiteral.trans
      (Category.assoc (orderedTensoratorForAssoc W Z A B) (j ⊗ₘ t) iab).symm
  have hPair : ((r ≫ iab) ⊗ₘ ic) =
      (r ⊗ₘ 𝟙 (T ⊗ C)) ≫ (iab ⊗ₘ ic) := by
    simpa only [Category.id_comp] using
      (MonoidalCategory.tensorHom_comp_tensorHom r (𝟙 (T ⊗ C)) iab ic).symm
  have hSecond :
      (iab ⊗ₘ ic) ≫ composition d S L n k l =
        compositionGenerator d S L n k l (b ⊗ a) c :=
    composition_generator d S L n k l (b ⊗ a) c
  have hBinary :
      ((r ⊗ₘ 𝟙 (T ⊗ C)) ≫ orderedTensoratorForAssoc W' T A' C) ≫
          (q ⊗ₘ u) =
        (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
          orderedTensoratorForAssoc (W ⊗ Z) T (B ⊗ A) C ≫
          (((j ▷ T) ≫ q) ⊗ₘ ((C ◁ t) ≫ u)) := by
    exact leftBinaryTensoratorsForAssoc W Z T A B C W' A' K D j t q u
  change (compositionGenerator d S L n m k a b ⊗ₘ ic) ≫
      composition d S L n k l =
    (orderedTensoratorForAssoc W Z A B ▷ (T ⊗ C)) ≫
      orderedTensoratorForAssoc (W ⊗ Z) T (B ⊗ A) C ≫
      (((j ▷ T) ≫ q) ⊗ₘ ((C ◁ t) ≫ u)) ≫ iout
  calc
    _ = ((r ≫ iab) ⊗ₘ ic) ≫ composition d S L n k l :=
      congrArg (fun f : (W ⊗ A) ⊗ (Z ⊗ B) ⟶ Hom d S n k =>
        (f ⊗ₘ ic) ≫ composition d S L n k l) hGenerator
    _ = ((r ⊗ₘ 𝟙 (T ⊗ C)) ≫ (iab ⊗ₘ ic)) ≫
        composition d S L n k l :=
      congrArg (fun f : ((W ⊗ A) ⊗ (Z ⊗ B)) ⊗ (T ⊗ C) ⟶
        Hom d S n k ⊗ Hom d S k l => f ≫ composition d S L n k l) hPair
    _ = (r ⊗ₘ 𝟙 (T ⊗ C)) ≫ compositionGenerator d S L n k l (b ⊗ a) c :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f : (W' ⊗ A') ⊗ (T ⊗ C) ⟶ Hom d S n l =>
          (r ⊗ₘ 𝟙 (T ⊗ C)) ≫ f) hSecond)
    _ = (((r ⊗ₘ 𝟙 (T ⊗ C)) ≫
          orderedTensoratorForAssoc W' T A' C) ≫ (q ⊗ₘ u)) ≫ iout := by
      have hLiteral : compositionGenerator d S L n k l (b ⊗ a) c =
          orderedTensoratorForAssoc W' T A' C ≫ (q ⊗ₘ u) ≫ iout := by
          dsimp only [compositionGenerator, orderedTensoratorForAssoc,
            W', T, A', C, q, u, iout, K, D]
          simp only [Category.assoc]
      exact (congrArg
        (fun f : (W' ⊗ A') ⊗ (T ⊗ C) ⟶ Hom d S n l =>
          (r ⊗ₘ 𝟙 (T ⊗ C)) ≫ f) hLiteral).trans
        ((Category.assoc (r ⊗ₘ 𝟙 (T ⊗ C))
          (orderedTensoratorForAssoc W' T A' C) ((q ⊗ₘ u) ≫ iout)).symm.trans
          (Category.assoc ((r ⊗ₘ 𝟙 (T ⊗ C)) ≫
            orderedTensoratorForAssoc W' T A' C) (q ⊗ₘ u) iout).symm)
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f : ((W ⊗ A) ⊗ (Z ⊗ B)) ⊗ (T ⊗ C) ⟶ K ⊗ D => f ≫ iout) hBinary

omit [HasCoproduct (weightedCoend.relations (weight d k l) S)]
  [HasCoproduct (weightedCoend.objects (weight d k l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d k l) S)
    (weightedCoend.rightMap (weight d k l) S)]
  [HasCoproduct (weightedCoend.relations (weight d m k) S)]
  [HasCoproduct (weightedCoend.objects (weight d m k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d m k) S)
    (weightedCoend.rightMap (weight d m k) S)]
  [HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)] in
/-- Expand the other binary descent on the same complete original
generators, with the actual late-first coefficient order. -/
private theorem rightRawCompositionForAssoc (a b c : I) :
    (weightedCoend.ι (weight d n m) S a ⊗ₘ
        compositionGenerator d S L m k l b c) ≫ composition d S L n m l =
      ((((a ⊗ n) ⟶[V] m) ⊗ S.obj a) ◁
          orderedTensoratorForAssoc ((b ⊗ m) ⟶[V] k) ((c ⊗ k) ⟶[V] l)
            (S.obj b) (S.obj c)) ≫
        orderedTensoratorForAssoc ((a ⊗ n) ⟶[V] m)
          (((b ⊗ m) ⟶[V] k) ⊗ ((c ⊗ k) ⟶[V] l))
          (S.obj a) (S.obj c ⊗ S.obj b) ≫
        ((((a ⊗ n) ⟶[V] m) ◁ indexGenerator d m k l b c ≫
            indexGenerator d n m l a (c ⊗ b)) ⊗ₘ
          ((L.mu c b ▷ S.obj a) ≫ L.mu (c ⊗ b) a)) ≫
        weightedCoend.ι (weight d n l) S ((c ⊗ b) ⊗ a) := by
  let W : V := (a ⊗ n) ⟶[V] m
  let Z : V := (b ⊗ m) ⟶[V] k
  let T : V := (c ⊗ k) ⟶[V] l
  let A : V := S.obj a
  let B : V := S.obj b
  let C : V := S.obj c
  let Z' : V := ((c ⊗ b) ⊗ m) ⟶[V] l
  let B' : V := S.obj (c ⊗ b)
  let K : V := (((c ⊗ b) ⊗ a) ⊗ n) ⟶[V] l
  let D : V := S.obj ((c ⊗ b) ⊗ a)
  let j : Z ⊗ T ⟶ Z' := indexGenerator d m k l b c
  let t : C ⊗ B ⟶ B' := L.mu c b
  let q : W ⊗ Z' ⟶ K := indexGenerator d n m l a (c ⊗ b)
  let u : B' ⊗ A ⟶ D := L.mu (c ⊗ b) a
  let r : (Z ⊗ B) ⊗ (T ⊗ C) ⟶ Z' ⊗ B' :=
    orderedTensoratorForAssoc Z T B C ≫ (j ⊗ₘ t)
  let ia : W ⊗ A ⟶ Hom d S n m := weightedCoend.ι (weight d n m) S a
  let ibc : Z' ⊗ B' ⟶ Hom d S m l :=
    weightedCoend.ι (weight d m l) S (c ⊗ b)
  let iout : K ⊗ D ⟶ Hom d S n l :=
    weightedCoend.ι (weight d n l) S ((c ⊗ b) ⊗ a)
  have hGenerator : compositionGenerator d S L m k l b c = r ≫ ibc := by
    have hLiteral : compositionGenerator d S L m k l b c =
        orderedTensoratorForAssoc Z T B C ≫ (j ⊗ₘ t) ≫ ibc := by
          dsimp only [compositionGenerator, orderedTensoratorForAssoc,
            Z, T, B, C, j, t, ibc]
          simp only [Category.assoc]
    exact hLiteral.trans
      (Category.assoc (orderedTensoratorForAssoc Z T B C) (j ⊗ₘ t) ibc).symm
  have hPair : (ia ⊗ₘ (r ≫ ibc)) =
      (𝟙 (W ⊗ A) ⊗ₘ r) ≫ (ia ⊗ₘ ibc) := by
    simpa only [Category.id_comp] using
      (MonoidalCategory.tensorHom_comp_tensorHom (𝟙 (W ⊗ A)) r ia ibc).symm
  have hSecond :
      (ia ⊗ₘ ibc) ≫ composition d S L n m l =
        compositionGenerator d S L n m l a (c ⊗ b) :=
    composition_generator d S L n m l a (c ⊗ b)
  have hBinary :
      ((𝟙 (W ⊗ A) ⊗ₘ r) ≫ orderedTensoratorForAssoc W Z' A B') ≫
          (q ⊗ₘ u) =
        ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
          orderedTensoratorForAssoc W (Z ⊗ T) A (C ⊗ B) ≫
          (((W ◁ j) ≫ q) ⊗ₘ ((t ▷ A) ≫ u)) := by
    exact rightBinaryTensoratorsForAssoc W Z T A B C Z' B' K D j t q u
  change (ia ⊗ₘ compositionGenerator d S L m k l b c) ≫
      composition d S L n m l =
    ((W ⊗ A) ◁ orderedTensoratorForAssoc Z T B C) ≫
      orderedTensoratorForAssoc W (Z ⊗ T) A (C ⊗ B) ≫
      (((W ◁ j) ≫ q) ⊗ₘ ((t ▷ A) ≫ u)) ≫ iout
  calc
    _ = (ia ⊗ₘ (r ≫ ibc)) ≫ composition d S L n m l :=
      congrArg (fun f : (Z ⊗ B) ⊗ (T ⊗ C) ⟶ Hom d S m l =>
        (ia ⊗ₘ f) ≫ composition d S L n m l) hGenerator
    _ = ((𝟙 (W ⊗ A) ⊗ₘ r) ≫ (ia ⊗ₘ ibc)) ≫
        composition d S L n m l :=
      congrArg (fun f : (W ⊗ A) ⊗ ((Z ⊗ B) ⊗ (T ⊗ C)) ⟶
        Hom d S n m ⊗ Hom d S m l => f ≫ composition d S L n m l) hPair
    _ = (𝟙 (W ⊗ A) ⊗ₘ r) ≫ compositionGenerator d S L n m l a (c ⊗ b) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f : (W ⊗ A) ⊗ (Z' ⊗ B') ⟶ Hom d S n l =>
          (𝟙 (W ⊗ A) ⊗ₘ r) ≫ f) hSecond)
    _ = (((𝟙 (W ⊗ A) ⊗ₘ r) ≫
          orderedTensoratorForAssoc W Z' A B') ≫ (q ⊗ₘ u)) ≫ iout := by
      have hLiteral : compositionGenerator d S L n m l a (c ⊗ b) =
          orderedTensoratorForAssoc W Z' A B' ≫ (q ⊗ₘ u) ≫ iout := by
          dsimp only [compositionGenerator, orderedTensoratorForAssoc,
            W, Z', A, B', q, u, iout, K, D]
          simp only [Category.assoc]
      exact (congrArg
        (fun f : (W ⊗ A) ⊗ (Z' ⊗ B') ⟶ Hom d S n l =>
          (𝟙 (W ⊗ A) ⊗ₘ r) ≫ f) hLiteral).trans
        ((Category.assoc (𝟙 (W ⊗ A) ⊗ₘ r)
          (orderedTensoratorForAssoc W Z' A B') ((q ⊗ₘ u) ≫ iout)).symm.trans
          (Category.assoc ((𝟙 (W ⊗ A) ⊗ₘ r) ≫
            orderedTensoratorForAssoc W Z' A B') (q ⊗ₘ u) iout).symm)
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f : (W ⊗ A) ⊗ ((Z ⊗ B) ⊗ (T ⊗ C)) ⟶ K ⊗ D => f ≫ iout) hBinary

/-- Associativity on all three entire original coend generators. The proof
uses the full index cube, coefficient associativity and actual target relation. -/
theorem composition_generator_assoc (a b c : I) :
    ((weightedCoend.ι (weight d n m) S a ⊗ₘ
        weightedCoend.ι (weight d m k) S b) ⊗ₘ
        weightedCoend.ι (weight d k l) S c) ≫
        (composition d S L n m k ▷ Hom d S k l) ≫
        composition d S L n k l =
      (α_ (weightedCoend.objects (weight d n m) S a)
          (weightedCoend.objects (weight d m k) S b)
          (weightedCoend.objects (weight d k l) S c)).hom ≫
        (weightedCoend.ι (weight d n m) S a ⊗ₘ
          (weightedCoend.ι (weight d m k) S b ⊗ₘ
            weightedCoend.ι (weight d k l) S c)) ≫
        (Hom d S n m ◁ composition d S L m k l) ≫
        composition d S L n m l := by
  let A : V := weightedCoend.objects (weight d n m) S a
  let B : V := weightedCoend.objects (weight d m k) S b
  let C : V := weightedCoend.objects (weight d k l) S c
  let ia : A ⟶ Hom d S n m := weightedCoend.ι (weight d n m) S a
  let ib : B ⟶ Hom d S m k := weightedCoend.ι (weight d m k) S b
  let ic : C ⟶ Hom d S k l := weightedCoend.ι (weight d k l) S c
  have hFirstLeft :
      ((ia ⊗ₘ ib) ⊗ₘ ic) ≫ (composition d S L n m k ▷ Hom d S k l) =
        compositionGenerator d S L n m k a b ⊗ₘ ic :=
    (MonoidalCategory.tensorHom_comp_whiskerRight (ia ⊗ₘ ib)
      (composition d S L n m k) ic).trans
      (congrArg (fun f : A ⊗ B ⟶ Hom d S n k => f ⊗ₘ ic)
        (composition_generator d S L n m k a b))
  have hFirstRight :
      (ia ⊗ₘ (ib ⊗ₘ ic)) ≫ (Hom d S n m ◁ composition d S L m k l) =
        ia ⊗ₘ compositionGenerator d S L m k l b c :=
    (MonoidalCategory.tensorHom_comp_whiskerLeft ia (ib ⊗ₘ ic)
      (composition d S L m k l)).trans
      (congrArg (fun f : B ⊗ C ⟶ Hom d S m l => ia ⊗ₘ f)
        (composition_generator d S L m k l b c))
  have hRaw :
      (compositionGenerator d S L n m k a b ⊗ₘ ic) ≫
          composition d S L n k l =
        (α_ A B C).hom ≫
          (ia ⊗ₘ compositionGenerator d S L m k l b c) ≫
          composition d S L n m l := by
    refine (leftRawCompositionForAssoc d S L n m k l a b c).trans ?_
    refine (rawTripleTargetForAssoc d S L n m k l a b c).trans ?_
    simpa only [A, B, C, ia, ic, operator_objects, Category.assoc] using
      congrArg (fun f : A ⊗ (B ⊗ C) ⟶ Hom d S n l => (α_ A B C).hom ≫ f)
        (rightRawCompositionForAssoc d S L n m k l a b c).symm
  change ((ia ⊗ₘ ib) ⊗ₘ ic) ≫
      (composition d S L n m k ▷ Hom d S k l) ≫
      composition d S L n k l =
    (α_ A B C).hom ≫ (ia ⊗ₘ (ib ⊗ₘ ic)) ≫
      (Hom d S n m ◁ composition d S L m k l) ≫ composition d S L n m l
  have hLeftEnd :
      ((ia ⊗ₘ ib) ⊗ₘ ic) ≫
          (composition d S L n m k ▷ Hom d S k l) ≫
          composition d S L n k l =
        (compositionGenerator d S L n m k a b ⊗ₘ ic) ≫
          composition d S L n k l := by
    exact (Category.assoc ((ia ⊗ₘ ib) ⊗ₘ ic)
      (composition d S L n m k ▷ Hom d S k l)
      (composition d S L n k l)).symm.trans
      (congrArg (fun f : (A ⊗ B) ⊗ C ⟶ Hom d S n k ⊗ Hom d S k l =>
        f ≫ composition d S L n k l) hFirstLeft)
  have hRightEnd :
      (α_ A B C).hom ≫ (ia ⊗ₘ (ib ⊗ₘ ic)) ≫
          (Hom d S n m ◁ composition d S L m k l) ≫
          composition d S L n m l =
        (α_ A B C).hom ≫
          (ia ⊗ₘ compositionGenerator d S L m k l b c) ≫
          composition d S L n m l := by
    have hPost := congrArg
      (fun f : A ⊗ (B ⊗ C) ⟶ Hom d S n m ⊗ Hom d S m l =>
        (α_ A B C).hom ≫ f ≫ composition d S L n m l) hFirstRight
    exact (congrArg
      (fun f : A ⊗ (B ⊗ C) ⟶ Hom d S n l => (α_ A B C).hom ≫ f)
      (Category.assoc (ia ⊗ₘ (ib ⊗ₘ ic))
        (Hom d S n m ◁ composition d S L m k l)
        (composition d S L n m l)).symm).trans hPost
  exact hLeftEnd.trans (hRaw.trans hRightEnd.symm)

/-- The literal full three-Hom equation required by EnrichedCategory.assoc.
All three source coends are eliminated through their preserved universal
properties. No operator associativity or category structure is supplied. -/
theorem composition_assoc :
    (α_ (Hom d S n m) (Hom d S m k) (Hom d S k l)).inv ≫
        (composition d S L n m k ▷ Hom d S k l) ≫
        composition d S L n k l =
      (Hom d S n m ◁ composition d S L m k l) ≫
        composition d S L n m l := by
  apply tripleCompositionSource_right_hom_extForProof d S n m k l
  intro a b c
  let A : V := weightedCoend.objects (weight d n m) S a
  let B : V := weightedCoend.objects (weight d m k) S b
  let C : V := weightedCoend.objects (weight d k l) S c
  let ia : A ⟶ Hom d S n m := weightedCoend.ι (weight d n m) S a
  let ib : B ⟶ Hom d S m k := weightedCoend.ι (weight d m k) S b
  let ic : C ⟶ Hom d S k l := weightedCoend.ι (weight d k l) S c
  have hNatural :
      (ia ⊗ₘ (ib ⊗ₘ ic)) ≫
          (α_ (Hom d S n m) (Hom d S m k) (Hom d S k l)).inv =
        (α_ A B C).inv ≫ ((ia ⊗ₘ ib) ⊗ₘ ic) :=
    associator_inv_naturality ia ib ic
  have hFullGenerator := congrArg
    (fun f : (A ⊗ B) ⊗ C ⟶ Hom d S n l => (α_ A B C).inv ≫ f)
    (composition_generator_assoc d S L n m k l a b c)
  change (ia ⊗ₘ (ib ⊗ₘ ic)) ≫
      ((α_ (Hom d S n m) (Hom d S m k) (Hom d S k l)).inv ≫
        (composition d S L n m k ▷ Hom d S k l) ≫
        composition d S L n k l) =
    (ia ⊗ₘ (ib ⊗ₘ ic)) ≫
      ((Hom d S n m ◁ composition d S L m k l) ≫ composition d S L n m l)
  calc
    _ = (α_ A B C).inv ≫ ((ia ⊗ₘ ib) ⊗ₘ ic) ≫
        (composition d S L n m k ▷ Hom d S k l) ≫
        composition d S L n k l := by
      simpa only [Category.assoc] using
        congrArg (fun f : A ⊗ (B ⊗ C) ⟶
          (Hom d S n m ⊗ Hom d S m k) ⊗ Hom d S k l =>
          f ≫ (composition d S L n m k ▷ Hom d S k l) ≫
            composition d S L n k l) hNatural
    _ = _ := by
      simpa only [A, B, C, ia, ib, ic, Category.assoc, Iso.inv_hom_id_assoc] using hFullGenerator

end CategoryTheory.Enriched.SphereOperator
