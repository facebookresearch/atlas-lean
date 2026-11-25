/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.GradedHomology.Monoidal
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyBraiding
public import MathlibExt.Algebra.Homology.KoszulTensorBraiding
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import Mathlib.CategoryTheory.GradedObject.Braiding

/-!
# Native Koszul interchange on canonical graded homology

This owner adds the actual coefficient-category symmetry to the structural
Monoidal owner. The native graded interchange inserts the literal integer
sign (-1)^(p*q), is natural and involutive, and agrees with the native signed
chain braiding on the actual descended cycle pairings. No braiding equation
or desired comparison is supplied by a caller.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.GradedHomology

variable {V : Type u} [Category.{v} V] [Preadditive V]
  [CategoryWithHomology V] [HasZeroObject V] [HasFiniteColimits V]
  [MonoidalCategory V] [MonoidalPreadditive V]
  [∀ X : V, PreservesFiniteColimits (tensorLeft X)]
  [∀ X : V, PreservesFiniteColimits (tensorRight X)]

variable [SymmetricCategory V]

local notation "MC" => V
local notation "Ch" => ChainComplex MC ℕ
local notation "Gr" => GradedObject ℕ MC

omit [CategoryWithHomology V] [HasZeroObject V] [HasFiniteColimits V] [MonoidalPreadditive V] [∀ X : V,
  PreservesFiniteColimits (tensorLeft X)] [∀ X : V, PreservesFiniteColimits (tensorRight X)] [SymmetricCategory V] in
omit [MonoidalCategory V] in
private theorem signed_comp {A B C : V} (r : ℤ) (f : A ⟶ B) (g : B ⟶ C) :
    (r • f) ≫ g = r • (f ≫ g) := by
  simp only [Preadditive.zsmul_comp]

/-- The actual Koszul sign in bidegree `(p,q)`. -/
abbrev sign (p q : ℕ) : ℤ := (-1 : ℤ) ^ (p * q)

theorem sign_symm (p q : ℕ) : sign q p = sign p q := by
  rw [sign, sign, Nat.mul_comm]

@[simp]
theorem sign_square (p q : ℕ) : sign p q * sign p q = 1 := by
  rw [sign, ← pow_add, ← two_mul, pow_mul]
  simp

theorem sign_add_left (p q r : ℕ) : sign (p + q) r = sign p r * sign q r := by
  simp only [sign, Nat.add_mul, pow_add]

theorem sign_add_right (p q r : ℕ) : sign p (q + r) = sign p q * sign p r := by
  simp only [sign, Nat.mul_add, pow_add]

/-- The actual signed interchange on native graded tensor summands. -/
def koszulSwapHom (X Y : Gr) : X ⊗ Y ⟶ Y ⊗ X :=
  fun n => GradedObject.Monoidal.tensorObjDesc fun p q h =>
    sign p q • ((β_ (X p) (Y q)).hom ≫
      GradedObject.Monoidal.ιTensorObj Y X q p n (by rw [Nat.add_comm, h]))

omit [CategoryWithHomology V] [HasZeroObject V] [MonoidalPreadditive V] in
@[reassoc (attr := simp)]
theorem ι_koszulSwapHom (X Y : Gr) (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj X Y p q n h ≫ koszulSwapHom X Y n =
      sign p q • ((β_ (X p) (Y q)).hom ≫
        GradedObject.Monoidal.ιTensorObj Y X q p n (by rw [Nat.add_comm, h])) := by
  exact GradedObject.Monoidal.ι_tensorObjDesc _ p q h

omit [CategoryWithHomology V] [HasZeroObject V] [MonoidalPreadditive V] in
@[reassoc]
theorem koszulSwapHom_naturality {X Y X' Y' : Gr} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ koszulSwapHom X' Y' = koszulSwapHom X Y ≫ (g ⊗ₘ f) := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  change GradedObject.Monoidal.ιTensorObj X Y p q n h ≫
      GradedObject.Monoidal.tensorHom f g n ≫ koszulSwapHom X' Y' n =
    GradedObject.Monoidal.ιTensorObj X Y p q n h ≫
      koszulSwapHom X Y n ≫ GradedObject.Monoidal.tensorHom g f n
  rw [GradedObject.Monoidal.ι_tensorHom_assoc, ι_koszulSwapHom,
    ι_koszulSwapHom_assoc]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  rw [GradedObject.Monoidal.ι_tensorHom, ← BraidedCategory.braiding_naturality_assoc]

omit [CategoryWithHomology V] [HasZeroObject V] [MonoidalPreadditive V] in
@[simp]
theorem koszulSwapHom_involutive (X Y : Gr) :
    koszulSwapHom X Y ≫ koszulSwapHom Y X = 𝟙 (X ⊗ Y) := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  change GradedObject.Monoidal.ιTensorObj X Y p q n h ≫
      koszulSwapHom X Y n ≫ koszulSwapHom Y X n =
    GradedObject.Monoidal.ιTensorObj X Y p q n h ≫ 𝟙 ((X ⊗ Y) n)
  rw [ι_koszulSwapHom_assoc]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [ι_koszulSwapHom]
  simp only [Preadditive.comp_zsmul, smul_smul, sign_symm, sign_square,
    one_smul, SymmetricCategory.symmetry_assoc, Category.comp_id]
  exact (Category.comp_id (GradedObject.Monoidal.ιTensorObj X Y p q n h)).symm

/-- The canonical signed interchange is an actual isomorphism, with the
reverse signed interchange as inverse. -/
def koszulSwap (X Y : Gr) : X ⊗ Y ≅ Y ⊗ X where
  hom := koszulSwapHom X Y
  inv := koszulSwapHom Y X
  hom_inv_id := koszulSwapHom_involutive X Y
  inv_hom_id := koszulSwapHom_involutive Y X

omit [CategoryWithHomology V] [HasZeroObject V] [∀ X : V, PreservesFiniteColimits (tensorLeft X)] [∀ X : V,
  PreservesFiniteColimits (tensorRight X)] in
theorem chainPair_braiding (K L : Ch) (p q : ℕ) :
    (ChainGradedPairing.pair (𝟙 (tensorObj K L)) p q) ≫
      (koszulTensorBraidingIso K L).hom.f (p + q) =
    sign p q • ((β_ (K.X p) (L.X q)).hom ≫
      ChainGradedPairing.pair (𝟙 (tensorObj L K)) q p ≫
      ((tensorObj L K).XIsoOfEq (Nat.add_comm q p)).hom) := by
  simp only [ChainGradedPairing.pair, HomologicalComplex.id_f, Category.comp_id]
  rw [ιTensorObj_koszulTensorBraidingIso_hom, ιTensorObj_comp_XIsoOfEq,
    ComplexShape.σ_down_ℕ]
  rw [Units.smul_def]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

/-- The native Koszul chain interchange descends to the actual bidegree
homology pairings with the same sign. -/
theorem pair_braiding (K L : Ch) (p q : ℕ) :
    pair K L p q ≫ homologyMap (koszulTensorBraidingIso K L).hom (p + q) =
      sign p q • ((β_ (K.homology p) (L.homology q)).hom ≫
        pair L K q p ≫ (homologyIsoOfEq (tensorObj L K) (Nat.add_comm q p)).hom) := by
  exact ChainGradedPairing.pairHomology_braiding
    (𝟙 (tensorObj K L)) (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K L)))
    (𝟙 (tensorObj L K)) (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj L K)))
    (koszulTensorBraidingIso K L).hom (sign p q) p q (chainPair_braiding K L p q)

/-- Koszul braiding coherence of the canonical graded Künneth tensorator. -/
@[reassoc]
theorem tensorator_braiding (K L : Ch) :
    tensorator K L ≫ homologyFunctor.map (koszulTensorBraidingIso K L).hom =
      (koszulSwap (homologyFunctor.obj K) (homologyFunctor.obj L)).hom ≫ tensorator L K := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  change GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
      (homologyFunctor.obj L) p q n h ≫ tensorator K L n ≫
      homologyMap (koszulTensorBraidingIso K L).hom n =
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
      (homologyFunctor.obj L) p q n h ≫
      koszulSwapHom (homologyFunctor.obj K) (homologyFunctor.obj L) n ≫
      tensorator L K n
  have hl := (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ homologyMap (koszulTensorBraidingIso K L).hom n)
      (ι_tensorator K L p q n h))
  have hr := (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ tensorator L K n)
      (ι_koszulSwapHom (homologyFunctor.obj K) (homologyFunctor.obj L) p q n h))
  let hqp : q + p = n := (Nat.add_comm q p).trans h
  let b := (β_ (K.homology p) (L.homology q)).hom
  let i := GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj L)
    (homologyFunctor.obj K) q p n hqp
  have hnat := homologyIsoOfEq_hom_naturality (koszulTensorBraidingIso K L).hom h
  have hh :
      (homologyIsoOfEq (tensorObj L K) (Nat.add_comm q p)).hom ≫
        (homologyIsoOfEq (tensorObj L K) h).hom =
      (homologyIsoOfEq (tensorObj L K) hqp).hom := by
    rw [homologyIsoOfEq_hom_trans]
  have hi := ι_tensorator L K q p n hqp
  have hright : (sign p q • (b ≫ i)) ≫ tensorator L K n =
      sign p q • (b ≫ pair L K q p ≫
        (homologyIsoOfEq (tensorObj L K) hqp).hom) := by
    exact (signed_comp (sign p q) (b ≫ i) (tensorator L K n)).trans
      ((congrArg (fun z => sign p q • z) (Category.assoc b i (tensorator L K n))).trans
        (congrArg (fun z => sign p q • (b ≫ z)) hi))
  have hcore : (pair K L p q ≫ (homologyIsoOfEq (tensorObj K L) h).hom) ≫
      homologyMap (koszulTensorBraidingIso K L).hom n =
    sign p q • (b ≫ pair L K q p ≫
      (homologyIsoOfEq (tensorObj L K) hqp).hom) := by
    calc
      _ = (pair K L p q ≫
          homologyMap (koszulTensorBraidingIso K L).hom (p + q)) ≫
          (homologyIsoOfEq (tensorObj L K) h).hom :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun z => pair K L p q ≫ z) hnat.symm).trans
            (Category.assoc _ _ _).symm)
      _ = (sign p q • (b ≫ pair L K q p ≫
          (homologyIsoOfEq (tensorObj L K) (Nat.add_comm q p)).hom)) ≫
          (homologyIsoOfEq (tensorObj L K) h).hom :=
        congrArg (fun z => z ≫ (homologyIsoOfEq (tensorObj L K) h).hom)
          (pair_braiding K L p q)
      _ = sign p q • (b ≫ pair L K q p ≫
          ((homologyIsoOfEq (tensorObj L K) (Nat.add_comm q p)).hom ≫
            (homologyIsoOfEq (tensorObj L K) h).hom)) := by
        simp only [Preadditive.zsmul_comp, Category.assoc]
      _ = sign p q • (b ≫ pair L K q p ≫
          (homologyIsoOfEq (tensorObj L K) hqp).hom) :=
        congrArg (fun z => sign p q • (b ≫ pair L K q p ≫ z)) hh
  have hm := hcore.trans hright.symm
  exact hl.trans (hm.trans hr.symm)


end HomologicalComplex.GradedHomology
