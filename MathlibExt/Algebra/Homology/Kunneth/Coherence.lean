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
# Associator and unit coherence of the canonical module Künneth maps

Let R be a commutative ring and K,L nonnegative R-module chain complexes
in ModuleCat^u(R). The canonical graded Künneth tensorator
μ_(K,L):H(K)⊗H(L)→H(K⊗L) is the module-category specialization
of graded cycle descent.

The associator equation compares the two iterated cycle pairings;
in bidegrees p,q,r it retains (p+q)+r=p+(q+r).
The unit map identifies the scalar graded unit with homology of R[0].
It satisfies
λ_(H(K))=H(λ_K) μ_(𝟙,K)(ε⊗id)
and ρ_(H(K))=H(ρ_K) μ_(K,𝟙)(id⊗ε).

Naturality, associativity and these unit equations give graded
homology its lax monoidal structure over every commutative R.
The structure maps are the canonical cycle tensorator and scalar-unit
homology map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.Kunneth

variable {R : Type u} [CommRing R]


/-- For nonnegative R-module chain complexes K,L over a
commutative ring R, the Künneth graded tensorator equals
the graded-homology cycle tensorator specialized to
V=ModuleCat^u(R).
Both maps are determined by their bidegree cycle descents. -/
theorem tensorator_eq_gradedHomology (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    tensorator K L = HomologicalComplex.GradedHomology.tensorator (V := (ModuleCat.{u} R)) K L := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  rw [ι_tensorator, HomologicalComplex.GradedHomology.ι_tensorator]
  rfl


/-- For nonnegative R-module chain complexes K,L and p+q=n,
the cycle tensor inclusion gives
Z_p(K)⊗[R]Z_q(L)→Z_n(K⊗L).
It includes the homogeneous tensor summand and factors through
cycles because both input differentials vanish. -/
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

/-- For nonnegative R-module chain complexes A,B,C over a
commutative ring R, the two iterated pairings on
H_p(A),H_q(B),H_r(C) agree after applying the chain associator.
The target homology degrees (p+q)+r and p+(q+r) are identified
by associativity of addition, and the source uses the module
tensor associator. -/
theorem pair_assoc (A B C : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q r : ℕ) :
    (pair A B p q ⊗ₘ 𝟙 (C.homology r)) ≫
      pair (tensorObj A B) C (p + q) r ≫
      homologyMap (α_ A B C).hom ((p + q) + r) ≫
      eqToHom (congrArg (fun n => (tensorObj A (tensorObj B C)).homology n)
        (Nat.add_assoc p q r)) =
    (α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
      (𝟙 (A.homology p) ⊗ₘ pair B C q r) ≫ pair A (tensorObj B C) p (q + r) := by
  exact HomologicalComplex.GradedHomology.pair_assoc A B C p q r

/-- For nonnegative R-module chain complexes A,B,C, the
canonical tensorators satisfy
H(α) μ_(A⊗B,C)(μ_(A,B)⊗id) =
μ_(A,B⊗C)(id⊗μ_(B,C)) α_H.
The coefficient ring R is commutative. -/
@[reassoc]
theorem tensorator_associativity (A B C : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    tensorator A B ▷ homologyFunctor.obj C ≫ tensorator (A ⊗ B) C ≫
      homologyFunctor.map (α_ A B C).hom =
    (α_ (homologyFunctor.obj A) (homologyFunctor.obj B) (homologyFunctor.obj C)).hom ≫
      homologyFunctor.obj A ◁ tensorator B C ≫ tensorator A (B ⊗ C) := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_associativity A B C)

/-- For a nonnegative R-module chain complex K, let
e:H_0(R[0])≅R be the scalar-unit homology isomorphism.
Pairing e⁻¹ with H_n(K), then applying H_n of the chain left
unitor, gives R⊗[R]H_n(K)→H_n(K), the ordinary left unitor. -/
theorem unit_left_pair (K : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    ((singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv ⊗ₘ
      𝟙 (K.homology n)) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)))
        (homologyFunctor.obj K) 0 n n (zero_add n) ≫ tensorator (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) K n ≫
      homologyMap (λ_ K).hom n = (λ_ (K.homology n)).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.unit_left_pair K n)

/-- For a nonnegative R-module chain complex K, pairing
H_n(K) with the inverse scalar-unit homology identification
R≅H_0(R[0]), then applying the chain right unitor on homology,
gives the right unitor H_n(K)⊗[R]R→H_n(K). -/
theorem unit_right_pair (K : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    (𝟙 (K.homology n) ⊗ₘ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
        (homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))) n 0 n (add_zero n) ≫ tensorator K
          (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) n ≫
      homologyMap (ρ_ K).hom n = (ρ_ (K.homology n)).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.unit_right_pair K n)

/-- For a nonnegative R-module chain complex K over a
commutative ring R, the canonical maps satisfy
λ_(H(K))=H(λ_K) ∘ μ_(𝟙,K) ∘ (ε⊗id).
The map ε identifies the scalar graded unit with H(R[0]). -/
theorem tensorator_left_unitality (K : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    (λ_ (homologyFunctor.obj K)).hom = unitMap ▷ homologyFunctor.obj K ≫
      tensorator (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) K ≫ homologyFunctor.map (λ_ K).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_left_unitality K)

/-- For a nonnegative R-module chain complex K over a
commutative ring R, the canonical maps satisfy
ρ_(H(K))=H(ρ_K) ∘ μ_(K,𝟙) ∘ (id⊗ε).
The map ε is the canonical scalar-unit homology map. -/
theorem tensorator_right_unitality (K : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    (ρ_ (homologyFunctor.obj K)).hom = homologyFunctor.obj K ◁ unitMap ≫
      tensorator K (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) ≫ homologyFunctor.map (ρ_ K).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_right_unitality K)

/-- For a commutative ring R, graded homology of nonnegative
R-module chain complexes is lax monoidal.
Its unit map is the scalar-unit homology comparison, and its
tensorator is the finite sum of canonical cycle homology pairings,
with the stated associator and unit laws. -/
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
