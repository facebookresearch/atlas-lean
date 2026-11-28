/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers

/-!
# Finite power coordinates and strong monoidal functors

Finite tensor powers have canonical one-factor, two-factor, head-tail, and right-associated
coordinates. A chosen map from the tensor unit can be prepended to a power, naturally under
maps preserving that chosen element.

A strong monoidal functor carries each finite power to the corresponding power of its image.
The comparison is recursive in the unit and tensor isomorphisms and is natural in object maps
and monoidal natural transformations. It respects block splitting, head-tail coordinates, and
power-index equalities, with independent source and target category universes.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory.TensorPower

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- One factor tensor power is the object.

The left unitor identifies power one with `X`. -/
noncomputable def tensorPowObjOneIso (X : C) :
    tensorPowObj X 1 ≅ X :=
  leftUnitor X

/-- Two factor tensor power is the binary tensor.

The block split and one-factor coordinates identify power two with `X ⊗ X`. -/
noncomputable def tensorPowObjTwoIso (X : C) :
    tensorPowObj X 2 ≅ X ⊗ X :=
  tensorPowAddIso X 1 1 ≪≫
    tensorIso (tensorPowObjOneIso X) (tensorPowObjOneIso X)

/-- Finite tensor power separates its first factor.

Recursively reassociate power `n+2` as `X ⊗ X^(n+1)`. -/
noncomputable def tensorPowObjHeadTailIso (X : C) :
    ∀ (n : ℕ), tensorPowObj X (n + 2) ≅
      X ⊗ tensorPowObj X (n + 1)
  | 0 => tensorPowObjTwoIso X ≪≫
      tensorIso (Iso.refl X) (tensorPowObjOneIso X).symm
  | n + 1 => tensorIso (tensorPowObjHeadTailIso X n) (Iso.refl X) ≪≫
      associator X (tensorPowObj X (n + 1)) X

/-- Successor head tail map is the preceding map and associator.

The successor forward coordinate is the preceding head-tail coordinate tensored with `𝟙 X`,
followed by the associator. -/
theorem tensorPowObjHeadTailIso_succ_hom (X : C) (n : ℕ) :
    (tensorPowObjHeadTailIso X (n + 1)).hom =
      ((tensorPowObjHeadTailIso X n).hom ⊗ₘ 𝟙 X) ≫
        (associator X (tensorPowObj X (n + 1)) X).hom :=
  rfl

/-- Head tail coordinate from the finite block split.

Split the power into blocks of lengths one and `n+1`, then apply the one-factor coordinate. -/
noncomputable def tensorPowObjHeadTailAddIso (X : C) (n : ℕ) :
    tensorPowObj X (n + 2) ≅ X ⊗ tensorPowObj X (n + 1) :=
  eqToIso (congrArg (tensorPowObj X) (Nat.one_add (n + 1)).symm) ≪≫
    tensorPowAddIso X 1 (n + 1) ≪≫
    tensorIso (tensorPowObjOneIso X) (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Recursive and block split head tail coordinates agree.

The recursive head-tail isomorphism equals the one obtained from the block-splitting
isomorphism. -/
theorem tensorPowObjHeadTailIso_eq_addIso (X : C) :
    ∀ n : ℕ,
      tensorPowObjHeadTailIso X n = tensorPowObjHeadTailAddIso X n
  | 0 => by
      apply Iso.ext
      unfold tensorPowObjHeadTailIso tensorPowObjHeadTailAddIso
      unfold tensorPowObjTwoIso
      simp only [Iso.trans_hom]
      have hcast :
          (eqToIso (congrArg (tensorPowObj X)
            (Nat.one_add 1).symm)).hom = 𝟙 _ := by
        rfl
      rw [hcast, Category.id_comp]
      simp only [tensorPowAddIso]
      unfold tensorPowObjOneIso
      monoidal_coherence
  | n + 1 => by
      apply Iso.ext
      rw [tensorPowObjHeadTailIso_succ_hom]
      unfold tensorPowObjHeadTailAddIso
      simp only [Iso.trans_hom]
      let h := (Nat.one_add (n + 1)).symm
      have hcast :
          (eqToIso (congrArg (tensorPowObj X)
            (Nat.one_add (n + 2)).symm)).hom =
          ((eqToIso (congrArg (tensorPowObj X) h)).hom ⊗ₘ 𝟙 X) := by
        change eqToHom (congrArg (fun k => tensorPowObj X k ⊗ X) h) =
          (eqToHom (congrArg (tensorPowObj X) h) ⊗ₘ 𝟙 X)
        rw [tensorHom_id, MonoidalCategory.eqToHom_whiskerRight]
      rw [hcast]
      rw [show (tensorPowAddIso X 1 ((n + 1) + 1)).hom =
          ((tensorPowAddIso X 1 (n + 1)).hom ⊗ₘ 𝟙 X) ≫
            (associator (tensorPowObj X 1)
              (tensorPowObj X (n + 1)) X).hom by rfl]
      rw [tensorPowObjHeadTailIso_eq_addIso X n]
      unfold tensorPowObjHeadTailAddIso
      simp only [Iso.trans_hom]
      simp only [tensorIso_hom, Iso.refl_hom]
      let c := (eqToIso (congrArg (tensorPowObj X)
        (Nat.one_add (n + 1)).symm)).hom
      let a := (tensorPowAddIso X 1 (n + 1)).hom
      let o := (tensorPowObjOneIso X).hom
      have hcomp :
          ((c ≫ a ≫ (o ⊗ₘ 𝟙 (tensorPowObj X (n + 1)))) ⊗ₘ 𝟙 X) =
            (c ⊗ₘ 𝟙 X) ≫ (a ⊗ₘ 𝟙 X) ≫
              ((o ⊗ₘ 𝟙 (tensorPowObj X (n + 1))) ⊗ₘ 𝟙 X) := by
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
        simp only [Category.comp_id]
      rw [hcomp]
      simp only [Category.assoc]
      rw [associator_naturality]
      simp only [tensorPowObj_succ, Nat.succ_eq_add_one, tensorHom_id,
        tensorPowObj_zero, id_whiskerRight, whiskerRight_tensor,
        comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc,
        eqToIso.hom, eqToHom_whiskerRight]
      have hcast' : c ▷ X =
          (eqToIso (congrArg (tensorPowObj X)
            (Nat.one_add (n + 2)).symm)).hom := by
        simpa only [tensorHom_id] using hcast.symm
      rw [hcast']
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Head tail coordinates are natural under power maps.

The power map in degree `n+2` becomes `f ⊗ tensorPowMap f (n+1)` under the head-tail
coordinates. -/
theorem tensorPowMap_comp_tensorPowObjHeadTailIso_hom
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorPowMap f (n + 2) ≫
        (tensorPowObjHeadTailIso Y n).hom =
      (tensorPowObjHeadTailIso X n).hom ≫
        (f ⊗ₘ tensorPowMap f (n + 1)) := by
  rw [tensorPowObjHeadTailIso_eq_addIso,
    tensorPowObjHeadTailIso_eq_addIso]
  unfold tensorPowObjHeadTailAddIso
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
  let h := (Nat.one_add (n + 1)).symm
  let cX := (eqToIso (congrArg (tensorPowObj X) h)).hom
  let cY := (eqToIso (congrArg (tensorPowObj Y) h)).hom
  let aX := (tensorPowAddIso X 1 (n + 1)).hom
  let aY := (tensorPowAddIso Y 1 (n + 1)).hom
  let oX := (tensorPowObjOneIso X).hom
  let oY := (tensorPowObjOneIso Y).hom
  have hcast : tensorPowMap f (n + 2) ≫ cY =
      cX ≫ tensorPowMap f (1 + (n + 1)) := by
    have cast_naturality {m p : ℕ} (hp : m = p) :
        tensorPowMap f m ≫
            (eqToIso (congrArg (tensorPowObj Y) hp)).hom =
          (eqToIso (congrArg (tensorPowObj X) hp)).hom ≫
            tensorPowMap f p := by
      subst p
      simp
    exact cast_naturality h
  have hadd := tensorPowAddIso_hom_naturality f 1 (n + 1)
  have hone : tensorPowMap f 1 ≫ oY = oX ≫ f := by
    change (𝟙 (𝟙_ C) ⊗ₘ f) ≫ (leftUnitor Y).hom =
      (leftUnitor X).hom ≫ f
    simpa only [id_tensorHom] using leftUnitor_naturality f
  calc
    tensorPowMap f (n + 2) ≫
          (cY ≫ aY ≫ (oY ⊗ₘ 𝟙 _)) =
      (tensorPowMap f (n + 2) ≫ cY) ≫
        aY ≫ (oY ⊗ₘ 𝟙 _) := by simp only [Category.assoc]
    _ = (cX ≫ tensorPowMap f (1 + (n + 1))) ≫
        aY ≫ (oY ⊗ₘ 𝟙 _) := by rw [hcast]
    _ = cX ≫
        (tensorPowMap f (1 + (n + 1)) ≫ aY) ≫
          (oY ⊗ₘ 𝟙 _) := by simp only [Category.assoc]
    _ = cX ≫
        (aX ≫ (tensorPowMap f 1 ⊗ₘ tensorPowMap f (n + 1))) ≫
          (oY ⊗ₘ 𝟙 _) := by rw [hadd]
    _ = cX ≫ aX ≫
        ((tensorPowMap f 1 ⊗ₘ tensorPowMap f (n + 1)) ≫
          (oY ⊗ₘ 𝟙 _)) := by simp only [Category.assoc]
    _ = cX ≫ aX ≫
        ((oX ⊗ₘ 𝟙 _) ≫
          (f ⊗ₘ tensorPowMap f (n + 1))) := by
            rw [tensorHom_comp_tensorHom,
              tensorHom_comp_tensorHom]
            simp only [Category.comp_id, Category.id_comp, hone]
    _ = (cX ≫ aX ≫ (oX ⊗ₘ 𝟙 _)) ≫
        (f ⊗ₘ tensorPowMap f (n + 1)) := by
          simp only [Category.assoc]

/-- Prepending a chosen unit source morphism to a finite power.

For `u : 𝟙 → X`, use the inverse left unitor, `u` on the first factor, and the inverse head-
tail coordinate. -/
noncomputable def tensorPowPrependMap
    {X : C} (u : 𝟙_ C ⟶ X) (n : ℕ) :
    tensorPowObj X (n + 1) ⟶ tensorPowObj X (n + 2) :=
  (leftUnitor (tensorPowObj X (n + 1))).inv ≫
    (u ⊗ₘ 𝟙 (tensorPowObj X (n + 1))) ≫
    (tensorPowObjHeadTailIso X n).inv

set_option backward.isDefEq.respectTransparency false in
/-- Power maps commute with compatible prepended elements.

If `u ≫ f = v`, the power map and the prepend maps for `u` and `v` form a commutative square. -/
theorem tensorPowMap_comp_tensorPowPrependMap
    {X Y : C} (f : X ⟶ Y)
    (u : 𝟙_ C ⟶ X) (v : 𝟙_ C ⟶ Y)
    (huv : u ≫ f = v) (n : ℕ) :
    tensorPowMap f (n + 1) ≫ tensorPowPrependMap v n =
      tensorPowPrependMap u n ≫ tensorPowMap f (n + 2) := by
  apply (cancel_mono (tensorPowObjHeadTailIso Y n).hom).1
  unfold tensorPowPrependMap
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorPowMap_comp_tensorPowObjHeadTailIso_hom]
  simp only [Iso.inv_hom_id_assoc]
  rw [leftUnitor_inv_naturality_assoc]
  rw [← id_tensorHom]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id, huv]

/-- Right associated positive tensor powers.

Start at `X` and recursively prepend `X` to obtain the right-associated power with `n+1`
factors. -/
def tensorPowObjRightSucc (X : C) : ℕ → C
  | 0 => X
  | n + 1 => X ⊗ tensorPowObjRightSucc X n

/-- Left and right associated positive powers are isomorphic.

The recursive head-tail coordinates identify the left-associated power `n+1` with the right-
associated positive power. -/
noncomputable def tensorPowObjRightSuccIso (X : C) :
    ∀ n : ℕ, tensorPowObj X (n + 1) ≅ tensorPowObjRightSucc X n
  | 0 => tensorPowObjOneIso X
  | n + 1 => tensorPowObjHeadTailIso X n ≪≫
      tensorIso (Iso.refl X) (tensorPowObjRightSuccIso X n)

/-- Right associated comparison at one factor.

At index zero, the comparison is the one-factor unitor isomorphism. -/
@[simp]
theorem tensorPowObjRightSuccIso_zero (X : C) :
    tensorPowObjRightSuccIso X 0 = tensorPowObjOneIso X :=
  rfl

/-- Right associated comparison at a successor.

The successor comparison is the head-tail isomorphism followed by the tensor of the identity
first factor and the preceding comparison. -/
@[simp]
theorem tensorPowObjRightSuccIso_succ (X : C) (n : ℕ) :
    tensorPowObjRightSuccIso X (n + 1) =
      tensorPowObjHeadTailIso X n ≪≫
        tensorIso (Iso.refl X) (tensorPowObjRightSuccIso X n) :=
  rfl

/-- Forward two factor coordinate uses the one factor map.

The forward two-factor coordinate is the one-factor map tensored with `𝟙 X`. -/
theorem tensorPowObjTwoIso_hom (X : C) :
    (tensorPowObjTwoIso X).hom =
      (tensorPowObjOneIso X).hom ⊗ₘ 𝟙 X := by
  unfold tensorPowObjTwoIso tensorPowObjOneIso
  unfold tensorPowAddIso
  unfold tensorPowAddIso
  monoidal_coherence

/-- Inverse two factor coordinate uses the inverse one factor map.

The inverse two-factor coordinate is the inverse one-factor map tensored with `𝟙 X`. -/
theorem tensorPowObjTwoIso_inv (X : C) :
    (tensorPowObjTwoIso X).inv =
      (tensorPowObjOneIso X).inv ⊗ₘ 𝟙 X := by
  unfold tensorPowObjTwoIso tensorPowObjOneIso
  unfold tensorPowAddIso
  unfold tensorPowAddIso
  monoidal_coherence

/-- Right associated triple as the left associated power.

The inverse associator and inverse two-factor coordinate identify `X ⊗ (X ⊗ X)` with power
three. -/
noncomputable def tensorPowObjThreeRightIso (X : C) :
    X ⊗ (X ⊗ X) ≅ tensorPowObj X 3 :=
  (associator X X X).symm ≪≫
    tensorIso (tensorPowObjTwoIso X).symm (Iso.refl X)

set_option backward.isDefEq.respectTransparency false in
/-- Forward triple coordinate is the inverse associator and two factor map.

Its forward map is the inverse associator followed by the inverse two-factor coordinate
tensored with `𝟙 X`. -/
theorem tensorPowObjThreeRightIso_hom (X : C) :
    (tensorPowObjThreeRightIso X).hom =
      (associator X X X).inv ≫
        ((tensorPowObjTwoIso X).inv ⊗ₘ 𝟙 X) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Triple coordinate in one factor unitor form.

The forward triple coordinate uses the inverse associator and two successive one-factor
inverse tensor maps. -/
theorem tensorPowObjThreeRightIso_hom_normalized (X : C) :
    (tensorPowObjThreeRightIso X).hom =
      (associator X X X).inv ≫
        (((tensorPowObjOneIso X).inv ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 X) := by
  rw [tensorPowObjThreeRightIso_hom, tensorPowObjTwoIso_inv]

/-- Forward one factor coordinate is natural.

The power-one map followed by the target coordinate equals the source coordinate followed by
`f`. -/
theorem tensorPowObjOneIso_hom_naturality
    {X Y : C} (f : X ⟶ Y) :
    tensorPowMap f 1 ≫ (tensorPowObjOneIso Y).hom =
      (tensorPowObjOneIso X).hom ≫ f := by
  change (𝟙 (𝟙_ C) ⊗ₘ f) ≫ (leftUnitor Y).hom =
    (leftUnitor X).hom ≫ f
  simpa only [id_tensorHom] using leftUnitor_naturality f

/-- Inverse one factor coordinate is natural.

The morphism `f` followed by the inverse target coordinate equals the inverse source
coordinate followed by the power-one map. -/
theorem tensorPowObjOneIso_inv_naturality
    {X Y : C} (f : X ⟶ Y) :
    f ≫ (tensorPowObjOneIso Y).inv =
      (tensorPowObjOneIso X).inv ≫ tensorPowMap f 1 := by
  apply (cancel_mono (tensorPowObjOneIso Y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorPowObjOneIso_hom_naturality]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Strong monoidal functor comparison on finite tensor powers.

The inverse unit and tensor structure isomorphisms recursively compare `G(X^n)` with `(G
X)^n`. -/
noncomputable def mapTensorPowObjIso (G : Functor C D) [G.Monoidal] (X : C) :
    ∀ (n : ℕ), G.obj (tensorPowObj X n) ≅ tensorPowObj (G.obj X) n
  | 0 => (Functor.Monoidal.εIso G).symm
  | n + 1 =>
      (Functor.Monoidal.μIso G (tensorPowObj X n) X).symm ≪≫
        tensorIso (mapTensorPowObjIso G X n) (Iso.refl (G.obj X))

/-- Strong monoidal power comparison at zero.

At power zero, the comparison is the inverse monoidal unit isomorphism. -/
@[simp]
theorem mapTensorPowObjIso_zero (G : Functor C D) [G.Monoidal] (X : C) :
    mapTensorPowObjIso G X 0 = (Functor.Monoidal.εIso G).symm :=
  rfl

/-- Strong monoidal power comparison at a successor.

The successor comparison is the inverse tensor structure map followed by the tensor of the
preceding comparison and the identity last factor. -/
@[simp]
theorem mapTensorPowObjIso_succ (G : Functor C D) [G.Monoidal] (X : C) (n : ℕ) :
    mapTensorPowObjIso G X (n + 1) =
      (Functor.Monoidal.μIso G (tensorPowObj X n) X).symm ≪≫
        tensorIso (mapTensorPowObjIso G X n) (Iso.refl (G.obj X)) :=
  rfl

/-- Strong monoidal power comparison is object natural.

The functor image of a power map commutes with the comparison and the power of its image
morphism. -/
theorem mapTensorPowObjIso_hom_naturality (G : Functor C D) [G.Monoidal]
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    G.map (tensorPowMap f n) ≫ (mapTensorPowObjIso G Y n).hom =
      (mapTensorPowObjIso G X n).hom ≫ tensorPowMap (G.map f) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change
      G.map (tensorPowMap f n ⊗ₘ f) ≫
          ((Functor.Monoidal.μIso G (tensorPowObj Y n) Y).inv ≫
            ((mapTensorPowObjIso G Y n).hom ⊗ₘ 𝟙 (G.obj Y))) =
        ((Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
            ((mapTensorPowObjIso G X n).hom ⊗ₘ 𝟙 (G.obj X))) ≫
          (tensorPowMap (G.map f) n ⊗ₘ G.map f)
    rw [Functor.Monoidal.map_tensor]
    simp only [Functor.Monoidal.μIso_inv, Category.assoc,
      Functor.Monoidal.μ_δ_assoc]
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, ih]

set_option backward.isDefEq.respectTransparency.types false in
/-- Strong monoidal power comparison respects index equalities.

Mapping a power-index equality and comparing equals comparing first and then transporting the
image power index. -/
@[reassoc]
theorem mapTensorPowObjIso_hom_eqToIso
    (G : Functor C D) [G.Monoidal] (X : C)
    {m n : ℕ} (h : m = n) :
    G.map (eqToIso (congrArg (tensorPowObj X) h)).hom ≫
        (mapTensorPowObjIso G X n).hom =
      (mapTensorPowObjIso G X m).hom ≫
        (eqToIso (congrArg (tensorPowObj (G.obj X)) h)).hom := by
  cases h
  simp

/-- Strong monoidal power comparison agrees with the one factor coordinate.

At power one, comparison followed by the target one-factor coordinate equals the functor image
of the source one-factor coordinate. -/
theorem mapTensorPowObjIso_hom_comp_tensorPowObjOneIso
    (G : Functor C D) [G.Monoidal] (X : C) :
    (mapTensorPowObjIso G X 1).hom ≫
        (tensorPowObjOneIso (G.obj X)).hom =
      G.map (tensorPowObjOneIso X).hom := by
  change (mapTensorPowObjIso G X 1).hom ≫
      (leftUnitor (G.obj X)).hom = G.map (leftUnitor X).hom
  rw [Functor.Monoidal.map_leftUnitor]
  simp only [mapTensorPowObjIso_succ, mapTensorPowObjIso_zero,
    Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv]
  dsimp [tensorPowObj, tensorIso]
  rw [tensorHom_id]
  exact Category.assoc _ _ _

/-- Power comparison is natural in monoidal transformations.

A monoidal natural transformation commutes with the finite-power comparisons and its
component's power map. -/
theorem mapTensorPowObjIso_hom_naturality_monoidal
    (G H : Functor C D) [G.Monoidal] [H.Monoidal]
    (α : G ⟶ H) [NatTrans.IsMonoidal α] (X : C) (n : ℕ) :
    α.app (tensorPowObj X n) ≫ (mapTensorPowObjIso H X n).hom =
      (mapTensorPowObjIso G X n).hom ≫ tensorPowMap (α.app X) n := by
  induction n with
  | zero =>
      have hUnit : (Functor.Monoidal.εIso G).hom ≫ α.app (𝟙_ C) =
          (Functor.Monoidal.εIso H).hom := by
        simpa only [Functor.Monoidal.εIso_hom] using
          (NatTrans.IsMonoidal.unit (τ := α))
      change α.app (𝟙_ C) ≫ (Functor.Monoidal.εIso H).inv =
        (Functor.Monoidal.εIso G).inv ≫ 𝟙 (𝟙_ D)
      rw [Category.comp_id]
      apply (cancel_epi (Functor.Monoidal.εIso G).hom).1
      calc
        (Functor.Monoidal.εIso G).hom ≫
              (α.app (𝟙_ C) ≫ (Functor.Monoidal.εIso H).inv) =
            ((Functor.Monoidal.εIso G).hom ≫ α.app (𝟙_ C)) ≫
              (Functor.Monoidal.εIso H).inv :=
          (Category.assoc _ _ _).symm
        _ = (Functor.Monoidal.εIso H).hom ≫
              (Functor.Monoidal.εIso H).inv := by
          rw [hUnit]
        _ = 𝟙 _ := Iso.hom_inv_id _
        _ = (Functor.Monoidal.εIso G).hom ≫
              (Functor.Monoidal.εIso G).inv :=
          (Iso.hom_inv_id _).symm
  | succ n ih =>
      have hTensor :
          (Functor.Monoidal.μIso G (tensorPowObj X n) X).hom ≫
              α.app (tensorPowObj X n ⊗ X) =
            (α.app (tensorPowObj X n) ⊗ₘ α.app X) ≫
              (Functor.Monoidal.μIso H (tensorPowObj X n) X).hom := by
        simpa only [Functor.Monoidal.μIso_hom] using
          (NatTrans.IsMonoidal.tensor
            (τ := α) (tensorPowObj X n) X)
      have hTensorInv :
          α.app (tensorPowObj X n ⊗ X) ≫
              (Functor.Monoidal.μIso H (tensorPowObj X n) X).inv =
            (Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
              (α.app (tensorPowObj X n) ⊗ₘ α.app X) := by
        apply (cancel_epi
          (Functor.Monoidal.μIso G (tensorPowObj X n) X).hom).1
        calc
          (Functor.Monoidal.μIso G (tensorPowObj X n) X).hom ≫
                (α.app (tensorPowObj X n ⊗ X) ≫
                  (Functor.Monoidal.μIso H (tensorPowObj X n) X).inv) =
              ((Functor.Monoidal.μIso G (tensorPowObj X n) X).hom ≫
                α.app (tensorPowObj X n ⊗ X)) ≫
                  (Functor.Monoidal.μIso H (tensorPowObj X n) X).inv :=
            (Category.assoc _ _ _).symm
          _ = ((α.app (tensorPowObj X n) ⊗ₘ α.app X) ≫
                (Functor.Monoidal.μIso H (tensorPowObj X n) X).hom) ≫
                  (Functor.Monoidal.μIso H (tensorPowObj X n) X).inv := by
            rw [hTensor]
          _ = α.app (tensorPowObj X n) ⊗ₘ α.app X := by simp
          _ = (Functor.Monoidal.μIso G (tensorPowObj X n) X).hom ≫
                ((Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
                  (α.app (tensorPowObj X n) ⊗ₘ α.app X)) := by simp
      change
        α.app (tensorPowObj X n ⊗ X) ≫
            ((Functor.Monoidal.μIso H (tensorPowObj X n) X).inv ≫
              ((mapTensorPowObjIso H X n).hom ⊗ₘ 𝟙 (H.obj X))) =
          ((Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
              ((mapTensorPowObjIso G X n).hom ⊗ₘ 𝟙 (G.obj X))) ≫
            (tensorPowMap (α.app X) n ⊗ₘ α.app X)
      calc
        α.app (tensorPowObj X n ⊗ X) ≫
              ((Functor.Monoidal.μIso H (tensorPowObj X n) X).inv ≫
                ((mapTensorPowObjIso H X n).hom ⊗ₘ 𝟙 (H.obj X))) =
            (α.app (tensorPowObj X n ⊗ X) ≫
              (Functor.Monoidal.μIso H (tensorPowObj X n) X).inv) ≫
                ((mapTensorPowObjIso H X n).hom ⊗ₘ 𝟙 (H.obj X)) :=
          (Category.assoc _ _ _).symm
        _ = ((Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
              (α.app (tensorPowObj X n) ⊗ₘ α.app X)) ≫
                ((mapTensorPowObjIso H X n).hom ⊗ₘ 𝟙 (H.obj X)) := by
          rw [hTensorInv]
        _ = (Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
              ((α.app (tensorPowObj X n) ⊗ₘ α.app X) ≫
                ((mapTensorPowObjIso H X n).hom ⊗ₘ 𝟙 (H.obj X))) :=
          Category.assoc _ _ _
        _ = (Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
              ((α.app (tensorPowObj X n) ≫
                  (mapTensorPowObjIso H X n).hom) ⊗ₘ α.app X) := by
          rw [tensorHom_comp_tensorHom, Category.comp_id]
        _ = (Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
              (((mapTensorPowObjIso G X n).hom ≫
                  tensorPowMap (α.app X) n) ⊗ₘ α.app X) := by
          rw [ih]
        _ = (Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
              (((mapTensorPowObjIso G X n).hom ⊗ₘ 𝟙 (G.obj X)) ≫
                (tensorPowMap (α.app X) n ⊗ₘ α.app X)) := by
          rw [tensorHom_comp_tensorHom, Category.id_comp]
        _ = ((Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
              ((mapTensorPowObjIso G X n).hom ⊗ₘ 𝟙 (G.obj X))) ≫
                (tensorPowMap (α.app X) n ⊗ₘ α.app X) :=
          (Category.assoc _ _ _).symm

/-- Strong monoidal power comparison respects block splitting.

The full power comparison followed by image-object block splitting equals the functor image of
source splitting, inverse tensor structure, and the two block comparisons. -/
@[reassoc]
theorem mapTensorPowObjIso_hom_add (G : Functor C D) [G.Monoidal]
    (X : C) (m n : ℕ) :
    (mapTensorPowObjIso G X (m + n)).hom ≫
        (tensorPowAddIso (G.obj X) m n).hom =
      G.map (tensorPowAddIso X m n).hom ≫
        (Functor.Monoidal.μIso G
          (tensorPowObj X m) (tensorPowObj X n)).inv ≫
          ((mapTensorPowObjIso G X m).hom ⊗ₘ
            (mapTensorPowObjIso G X n).hom) := by
  induction n generalizing m with
  | zero =>
      have hTensor :
          (G.obj (tensorPowObj X m) ◁ Functor.OplaxMonoidal.η G) ≫
              ((mapTensorPowObjIso G X m).hom ▷ 𝟙_ D) =
            (mapTensorPowObjIso G X m).hom ⊗ₘ
              Functor.OplaxMonoidal.η G := by
        rw [← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom, Category.id_comp,
          Category.comp_id]
      change (mapTensorPowObjIso G X m).hom ≫
          (rightUnitor (tensorPowObj (G.obj X) m)).inv =
        G.map (rightUnitor (tensorPowObj X m)).inv ≫
          Functor.OplaxMonoidal.δ G (tensorPowObj X m) (𝟙_ C) ≫
            ((mapTensorPowObjIso G X m).hom ⊗ₘ
              Functor.OplaxMonoidal.η G)
      calc
        (mapTensorPowObjIso G X m).hom ≫
              (rightUnitor (tensorPowObj (G.obj X) m)).inv =
            (rightUnitor (G.obj (tensorPowObj X m))).inv ≫
              ((mapTensorPowObjIso G X m).hom ▷ 𝟙_ D) :=
          rightUnitor_inv_naturality _
        _ = (G.map (rightUnitor (tensorPowObj X m)).inv ≫
              Functor.OplaxMonoidal.δ G (tensorPowObj X m) (𝟙_ C) ≫
              G.obj (tensorPowObj X m) ◁ Functor.OplaxMonoidal.η G) ≫
                ((mapTensorPowObjIso G X m).hom ▷ 𝟙_ D) := by
          rw [Functor.OplaxMonoidal.right_unitality]
        _ = G.map (rightUnitor (tensorPowObj X m)).inv ≫
              Functor.OplaxMonoidal.δ G (tensorPowObj X m) (𝟙_ C) ≫
                ((mapTensorPowObjIso G X m).hom ⊗ₘ
                  Functor.OplaxMonoidal.η G) := by
          simp only [Category.assoc, hTensor]
  | succ n ih =>
      let pM := (mapTensorPowObjIso G X m).hom
      let pN := (mapTensorPowObjIso G X n).hom
      let addC := (tensorPowAddIso X m n).hom
      let addD := (tensorPowAddIso (G.obj X) m n).hom
      have hTensorComp :
          ((mapTensorPowObjIso G X (m + n)).hom ⊗ₘ 𝟙 (G.obj X)) ≫
              (addD ⊗ₘ 𝟙 (G.obj X)) =
            ((mapTensorPowObjIso G X (m + n)).hom ≫ addD) ⊗ₘ
              𝟙 (G.obj X) := by
        rw [tensorHom_comp_tensorHom, Category.comp_id]
      have hInduction :
          Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
              (((mapTensorPowObjIso G X (m + n)).hom ≫ addD) ⊗ₘ
                𝟙 (G.obj X)) ≫
              (associator _ _ _).hom =
            Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
              ((G.map addC ≫
                Functor.OplaxMonoidal.δ G
                  (tensorPowObj X m) (tensorPowObj X n) ≫
                (pM ⊗ₘ pN)) ⊗ₘ 𝟙 (G.obj X)) ≫
              (associator _ _ _).hom := by
        have h := congrArg (fun f =>
          Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
            (f ⊗ₘ 𝟙 (G.obj X)) ≫ (associator _ _ _).hom) (ih m)
        simpa only [pM, pN, addC, addD,
          Functor.Monoidal.μIso_inv] using h
      have hSplit :
          ((G.map addC ≫
              Functor.OplaxMonoidal.δ G
                (tensorPowObj X m) (tensorPowObj X n) ≫
              (pM ⊗ₘ pN)) ⊗ₘ 𝟙 (G.obj X)) =
            (G.map addC ⊗ₘ 𝟙 (G.obj X)) ≫
              (Functor.OplaxMonoidal.δ G
                  (tensorPowObj X m) (tensorPowObj X n) ⊗ₘ
                𝟙 (G.obj X)) ≫
              ((pM ⊗ₘ pN) ⊗ₘ 𝟙 (G.obj X)) := by
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          Category.comp_id]
        simp only [Category.comp_id]
      have hDelta :
          Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
              (G.map addC ⊗ₘ 𝟙 (G.obj X)) =
            G.map (addC ⊗ₘ 𝟙 X) ≫
              Functor.OplaxMonoidal.δ G
                (tensorPowObj X m ⊗ tensorPowObj X n) X := by
        simpa only [G.map_id] using
          (Functor.OplaxMonoidal.δ_natural G addC (𝟙 X))
      have hOplax := Functor.OplaxMonoidal.associativity G
        (tensorPowObj X m) (tensorPowObj X n) X
      have hOplax' :
          Functor.OplaxMonoidal.δ G
              (tensorPowObj X m ⊗ tensorPowObj X n) X ≫
              (Functor.OplaxMonoidal.δ G
                (tensorPowObj X m) (tensorPowObj X n) ⊗ₘ
                  𝟙 (G.obj X)) ≫
              (associator _ _ _).hom =
            G.map (associator _ _ _).hom ≫
              Functor.OplaxMonoidal.δ G
                (tensorPowObj X m) (tensorPowObj X n ⊗ X) ≫
              (G.obj (tensorPowObj X m) ◁
                Functor.OplaxMonoidal.δ G (tensorPowObj X n) X) := by
        simpa only [tensorHom_id] using hOplax
      have hLast :
          (G.obj (tensorPowObj X m) ◁
              Functor.OplaxMonoidal.δ G (tensorPowObj X n) X) ≫
              (pM ⊗ₘ (pN ⊗ₘ 𝟙 (G.obj X))) =
            pM ⊗ₘ
              (Functor.OplaxMonoidal.δ G (tensorPowObj X n) X ≫
                (pN ⊗ₘ 𝟙 (G.obj X))) := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom,
          Category.id_comp]
      change
        (Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
            ((mapTensorPowObjIso G X (m + n)).hom ⊗ₘ 𝟙 (G.obj X))) ≫
          ((addD ⊗ₘ 𝟙 (G.obj X)) ≫
            (associator _ _ _).hom) =
        G.map ((addC ⊗ₘ 𝟙 X) ≫ (associator _ _ _).hom) ≫
          Functor.OplaxMonoidal.δ G
            (tensorPowObj X m) (tensorPowObj X n ⊗ X) ≫
          (pM ⊗ₘ
            (Functor.OplaxMonoidal.δ G (tensorPowObj X n) X ≫
              (pN ⊗ₘ 𝟙 (G.obj X))))
      calc
        (Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
              ((mapTensorPowObjIso G X (m + n)).hom ⊗ₘ 𝟙 (G.obj X))) ≫
            ((addD ⊗ₘ 𝟙 (G.obj X)) ≫
              (associator _ _ _).hom) =
          Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
            (((mapTensorPowObjIso G X (m + n)).hom ≫ addD) ⊗ₘ
              𝟙 (G.obj X)) ≫
                (associator _ _ _).hom := by
          slice_lhs 2 3 => rw [hTensorComp]
        _ = Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
            ((G.map addC ≫
              Functor.OplaxMonoidal.δ G
                (tensorPowObj X m) (tensorPowObj X n) ≫
              (pM ⊗ₘ pN)) ⊗ₘ 𝟙 (G.obj X)) ≫
                (associator _ _ _).hom := by
          exact hInduction
        _ = (Functor.OplaxMonoidal.δ G (tensorPowObj X (m + n)) X ≫
              (G.map addC ⊗ₘ 𝟙 (G.obj X))) ≫
            (Functor.OplaxMonoidal.δ G
                (tensorPowObj X m) (tensorPowObj X n) ⊗ₘ
              𝟙 (G.obj X)) ≫
            ((pM ⊗ₘ pN) ⊗ₘ 𝟙 (G.obj X)) ≫
              (associator _ _ _).hom := by
          rw [hSplit]
          simp only [Category.assoc]
        _ = (G.map (addC ⊗ₘ 𝟙 X) ≫
              Functor.OplaxMonoidal.δ G
                (tensorPowObj X m ⊗ tensorPowObj X n) X) ≫
            (Functor.OplaxMonoidal.δ G
                (tensorPowObj X m) (tensorPowObj X n) ⊗ₘ
              𝟙 (G.obj X)) ≫
            ((pM ⊗ₘ pN) ⊗ₘ 𝟙 (G.obj X)) ≫
              (associator _ _ _).hom := by
          rw [hDelta]
        _ = G.map (addC ⊗ₘ 𝟙 X) ≫
            (Functor.OplaxMonoidal.δ G
                (tensorPowObj X m ⊗ tensorPowObj X n) X ≫
              (Functor.OplaxMonoidal.δ G
                  (tensorPowObj X m) (tensorPowObj X n) ⊗ₘ
                𝟙 (G.obj X)) ≫
              (associator _ _ _).hom) ≫
            (pM ⊗ₘ (pN ⊗ₘ 𝟙 (G.obj X))) := by
          rw [associator_naturality]
          simp only [Category.assoc]
        _ = G.map (addC ⊗ₘ 𝟙 X) ≫
            (G.map (associator _ _ _).hom ≫
              Functor.OplaxMonoidal.δ G
                (tensorPowObj X m) (tensorPowObj X n ⊗ X) ≫
              (G.obj (tensorPowObj X m) ◁
                Functor.OplaxMonoidal.δ G (tensorPowObj X n) X)) ≫
            (pM ⊗ₘ (pN ⊗ₘ 𝟙 (G.obj X))) := by
          exact congrArg (fun f => G.map (addC ⊗ₘ 𝟙 X) ≫ f ≫
            (pM ⊗ₘ (pN ⊗ₘ 𝟙 (G.obj X)))) hOplax'
        _ = G.map ((addC ⊗ₘ 𝟙 X) ≫
              (associator _ _ _).hom) ≫
            Functor.OplaxMonoidal.δ G
              (tensorPowObj X m) (tensorPowObj X n ⊗ X) ≫
            (pM ⊗ₘ
              (Functor.OplaxMonoidal.δ G (tensorPowObj X n) X ≫
                (pN ⊗ₘ 𝟙 (G.obj X)))) := by
          rw [G.map_comp]
          simp only [Category.assoc, hLast]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Strong monoidal power comparison respects head tail coordinates.

The comparison for `n+2` commutes with source and target head-tail coordinates, the inverse
tensor structure map, and the comparison of the tail power. -/
theorem mapTensorPowObjIso_hom_headTail
    (G : Functor C D) [G.Monoidal] (X : C) (n : ℕ) :
    (mapTensorPowObjIso G X (n + 2)).hom ≫
        (tensorPowObjHeadTailIso (G.obj X) n).hom =
      G.map (tensorPowObjHeadTailIso X n).hom ≫
        (Functor.Monoidal.μIso G X
          (tensorPowObj X (n + 1))).inv ≫
        (𝟙 (G.obj X) ⊗ₘ
          (mapTensorPowObjIso G X (n + 1)).hom) := by
  rw [tensorPowObjHeadTailIso_eq_addIso,
    tensorPowObjHeadTailIso_eq_addIso]
  unfold tensorPowObjHeadTailAddIso
  simp only [Iso.trans_hom]
  let h := (Nat.one_add (n + 1)).symm
  rw [← mapTensorPowObjIso_hom_eqToIso_assoc G X h]
  rw [mapTensorPowObjIso_hom_add_assoc G X 1 (n + 1)]
  simp only [tensorIso_hom, Iso.refl_hom]
  rw [tensorHom_comp_tensorHom]
  simp only [Category.comp_id]
  rw [mapTensorPowObjIso_hom_comp_tensorPowObjOneIso]
  have hfactor :
      (G.map (tensorPowObjOneIso X).hom ⊗ₘ
          (mapTensorPowObjIso G X (n + 1)).hom) =
        (G.map (tensorPowObjOneIso X).hom ⊗ₘ
            𝟙 (G.obj (tensorPowObj X (n + 1)))) ≫
          (𝟙 (G.obj X) ⊗ₘ
            (mapTensorPowObjIso G X (n + 1)).hom) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  rw [hfactor]
  simp only [tensorHom_id, Functor.Monoidal.μIso_inv]
  rw [Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [← G.map_comp_assoc, ← G.map_comp_assoc]
  rw [Category.assoc]

end CategoryTheory.MonoidalCategory.TensorPower
