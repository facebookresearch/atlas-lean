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

public import MathlibExt.Algebra.Homology.Kunneth.Graded
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import MathlibExt.Algebra.Homology.GradedTensorTower
public import MathlibExt.Algebra.Homology.GradedHomology.Monoidal

/-!
# Coherence of the canonical cycle Künneth maps

Associativity is checked on three original cycle objects and then descends
through the actual epimorphic homology quotient maps. Unit coherence uses
the canonical homology of the single tensor unit. These are proofs for
the already defined tensorator, not inputs to its monoidal structure.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.Kunneth

variable {R : Type u} [CommRing R]


/-- The literal existing tensorator equals the canonical shared cycle descent.
This is proved by its actual graded source injections, not supplied as data. -/
theorem tensorator_eq_gradedHomology (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    tensorator K L = HomologicalComplex.GradedHomology.tensorator (V := (ModuleCat.{u} R)) K L := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  rw [ι_tensorator, HomologicalComplex.GradedHomology.ι_tensorator]
  rfl


/-- The canonical tensor pairing of cycles in a specified total degree. -/
def cyclesPair (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q n : ℕ) (h : p + q = n) :
    K.cycles p ⊗ L.cycles q ⟶ (tensorObj K L).cycles n :=
  HomologicalComplex.GradedHomology.cyclesPair K L p q n h

@[reassoc (attr := simp)]
theorem cyclesPair_i (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q n : ℕ) (h : p + q = n) :
    cyclesPair K L p q n h ≫ (tensorObj K L).iCycles n =
      (K.iCycles p ⊗ₘ L.iCycles q) ≫ ιTensorObj K L p q n h := by
  exact HomologicalComplex.GradedHomology.cyclesPair_i K L p q n h

@[reassoc (attr := simp)]
theorem quotient_tensorator (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q n : ℕ) (h : p + q = n) :
    (K.homologyπ p ⊗ₘ L.homologyπ q) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
        (homologyFunctor.obj L) p q n h ≫ tensorator K L n =
      cyclesPair K L p q n h ≫ (tensorObj K L).homologyπ n := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.quotient_tensorator K L p q n h)

/-- Associativity of the actual bidegree Künneth pairings, including the
literal equality-induced map between the two parenthesized total degrees. -/
theorem pair_assoc (A B C : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q r : ℕ) :
    (pair A B p q ⊗ₘ 𝟙 (C.homology r)) ≫
      pair (tensorObj A B) C (p + q) r ≫
      homologyMap (α_ A B C).hom ((p + q) + r) ≫
      eqToHom (congrArg (fun n => (tensorObj A (tensorObj B C)).homology n)
        (Nat.add_assoc p q r)) =
    (α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
      (𝟙 (A.homology p) ⊗ₘ pair B C q r) ≫ pair A (tensorObj B C) p (q + r) := by
  exact HomologicalComplex.GradedHomology.pair_assoc A B C p q r

/-- Associator coherence for the canonical graded Künneth tensorator. -/
@[reassoc]
theorem tensorator_associativity (A B C : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    tensorator A B ▷ homologyFunctor.obj C ≫ tensorator (A ⊗ B) C ≫
      homologyFunctor.map (α_ A B C).hom =
    (α_ (homologyFunctor.obj A) (homologyFunctor.obj B) (homologyFunctor.obj C)).hom ≫
      homologyFunctor.obj A ◁ tensorator B C ≫ tensorator A (B ⊗ C) := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_associativity A B C)

/-- The scalar unit paired with a homology class gives its native left unitor. -/
theorem unit_left_pair (K : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    ((singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv ⊗ₘ
      𝟙 (K.homology n)) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)))
        (homologyFunctor.obj K) 0 n n (zero_add n) ≫ tensorator (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) K n ≫
      homologyMap (λ_ K).hom n = (λ_ (K.homology n)).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.unit_left_pair K n)

/-- The scalar unit paired on the right gives the native right unitor. -/
theorem unit_right_pair (K : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    (𝟙 (K.homology n) ⊗ₘ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
        (homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))) n 0 n (add_zero n) ≫ tensorator K
          (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) n ≫
      homologyMap (ρ_ K).hom n = (ρ_ (K.homology n)).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.unit_right_pair K n)

/-- Left unit coherence for the canonical cycle Künneth tensorator. -/
theorem tensorator_left_unitality (K : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    (λ_ (homologyFunctor.obj K)).hom = unitMap ▷ homologyFunctor.obj K ≫
      tensorator (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) K ≫ homologyFunctor.map (λ_ K).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_left_unitality K)

/-- Right unit coherence for the canonical cycle Künneth tensorator. -/
theorem tensorator_right_unitality (K : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    (ρ_ (homologyFunctor.obj K)).hom = homologyFunctor.obj K ◁ unitMap ≫
      tensorator K (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) ≫ homologyFunctor.map (ρ_ K).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_right_unitality K)

/-- The earned lax monoidal structure on the existing native graded
homology functor, over every commutative ring in its actual coefficient world. -/
def laxMonoidal : (homologyFunctor (R := R)).LaxMonoidal where
  ε := unitMap
  μ := tensorator
  μ_natural_left f K := by
    simp only [tensorator_eq_gradedHomology]
    exact
      (HomologicalComplex.GradedHomology.laxMonoidal (V := (ModuleCat.{u} R))).μ_natural_left f K
  μ_natural_right K f := by
    simp only [tensorator_eq_gradedHomology]
    exact
      (HomologicalComplex.GradedHomology.laxMonoidal (V := (ModuleCat.{u} R))).μ_natural_right K f
  associativity := tensorator_associativity
  left_unitality := tensorator_left_unitality
  right_unitality := tensorator_right_unitality

end HomologicalComplex.Kunneth
