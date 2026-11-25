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

public import MathlibExt.Algebra.Homology.Kunneth.Coherence
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyBraiding
public import MathlibExt.Algebra.Homology.KoszulTensorBraiding
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import MathlibExt.Algebra.Homology.GradedHomology.Koszul

/-!
# Koszul braiding and the canonical Künneth tensorator

The ordinary graded-object braiding does not insert a degree sign. The
isomorphism here inserts `(-1)^(p*q)` on its actual `(p,q)` summand. The
compatibility theorem uses the existing signed chain tensor braiding and
descends its actual bidegree formula through homology quotients.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.Kunneth

variable {R : Type u} [CommRing R]


/-- The actual Koszul sign in bidegree `(p,q)`. -/
abbrev sign (p q : ℕ) : ℤ :=
  HomologicalComplex.GradedHomology.sign p q

theorem sign_symm (p q : ℕ) : sign q p = sign p q := by
  exact HomologicalComplex.GradedHomology.sign_symm p q

theorem sign_square (p q : ℕ) : sign p q * sign p q = 1 := by
  exact HomologicalComplex.GradedHomology.sign_square p q

theorem sign_add_left (p q r : ℕ) : sign (p + q) r = sign p r * sign q r := by
  exact HomologicalComplex.GradedHomology.sign_add_left p q r

theorem sign_add_right (p q r : ℕ) : sign p (q + r) = sign p q * sign p r := by
  exact HomologicalComplex.GradedHomology.sign_add_right p q r

/-- The actual signed interchange on native graded tensor summands. -/
def koszulSwapHom (X Y : (GradedObject ℕ (ModuleCat.{u} R))) : X ⊗ Y ⟶ Y ⊗ X :=
  HomologicalComplex.GradedHomology.koszulSwapHom X Y

@[reassoc (attr := simp)]
theorem ι_koszulSwapHom (X Y : (GradedObject ℕ (ModuleCat.{u} R))) (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj X Y p q n h ≫ koszulSwapHom X Y n =
      sign p q • ((β_ (X p) (Y q)).hom ≫
        GradedObject.Monoidal.ιTensorObj Y X q p n (by rw [Nat.add_comm, h])) := by
  exact HomologicalComplex.GradedHomology.ι_koszulSwapHom X Y p q n h

@[reassoc]
theorem koszulSwapHom_naturality {X Y X' Y' : (GradedObject ℕ (ModuleCat.{u} R))} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ koszulSwapHom X' Y' = koszulSwapHom X Y ≫ (g ⊗ₘ f) := by
  exact HomologicalComplex.GradedHomology.koszulSwapHom_naturality f g

@[simp]
theorem koszulSwapHom_involutive (X Y : (GradedObject ℕ (ModuleCat.{u} R))) :
    koszulSwapHom X Y ≫ koszulSwapHom Y X = 𝟙 (X ⊗ Y) := by
  exact HomologicalComplex.GradedHomology.koszulSwapHom_involutive X Y

/-- The canonical signed interchange is an actual isomorphism, with the
reverse signed interchange as inverse. -/
def koszulSwap (X Y : (GradedObject ℕ (ModuleCat.{u} R))) : X ⊗ Y ≅ Y ⊗ X :=
  HomologicalComplex.GradedHomology.koszulSwap X Y

/-- The native Koszul chain interchange descends to the actual bidegree
homology pairings with the same sign. -/
theorem pair_braiding (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q : ℕ) :
    pair K L p q ≫ homologyMap (koszulTensorBraidingIso K L).hom (p + q) =
      sign p q • ((β_ (K.homology p) (L.homology q)).hom ≫
        pair L K q p ≫ (homologyIsoOfEq (tensorObj L K) (Nat.add_comm q p)).hom) := by
  exact HomologicalComplex.GradedHomology.pair_braiding K L p q

/-- Koszul braiding coherence of the canonical graded Künneth tensorator. -/
@[reassoc]
theorem tensorator_braiding (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    tensorator K L ≫ homologyFunctor.map (koszulTensorBraidingIso K L).hom =
      (koszulSwap (homologyFunctor.obj K) (homologyFunctor.obj L)).hom ≫ tensorator L K := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_braiding K L)

end HomologicalComplex.Kunneth
