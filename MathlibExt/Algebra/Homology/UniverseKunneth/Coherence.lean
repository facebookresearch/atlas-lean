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

public import MathlibExt.Algebra.Homology.UniverseKunneth.Graded
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import MathlibExt.Algebra.Homology.GradedTensorTower
public import MathlibExt.Algebra.Homology.GradedHomology.Monoidal

/-!
# Associativity and unit coherence of cycle Künneth tensorators

Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. For chain complexes of shape down ℕ, the cycle pairing
Z_pK⊗Z_qL→Z_{p+q}(K⊗L) descends to H_pK⊗H_qL→H_{p+q}(K⊗L). Summing over the degree antidiagonal
gives the graded homology tensorator μ_{K,L}.

Pairing three cycle classes is compatible with the chain and module associators, including the
identification of total degrees (p+q)+r=p+(q+r). Pairing with the degree-zero class of the
tensor unit agrees with the left and right unitors. Consequently μ and the canonical unit map
e:𝟙→H(𝟙) satisfy the lax monoidal associativity and unit equations. These laws use the specified
cycle maps over any commutative ring, with no bounded-support condition.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.UniverseKunneth

variable {R : Type u} [CommRing R]


/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For chain complexes K,L of shape down ℕ, the
specified Künneth tensorator μ_{K,L}:H(K)⊗H(L)→H(K⊗L) equals the graded-homology tensorator
defined by descending the cycle pairings and summing their homogeneous components. Both maps
have bidegree component H_pK⊗H_qL→H_{p+q}(K⊗L) equal to the canonical cycle pairing. -/
theorem tensorator_eq_gradedHomology (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :
    tensorator K L = HomologicalComplex.GradedHomology.tensorator (V :=
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R)) K L := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  rw [ι_tensorator, HomologicalComplex.GradedHomology.ι_tensorator]


/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For chain complexes K,L of shape down ℕ and
p,q,n∈ℕ with p+q=n, this is the map c_{p,q}:Z_pK⊗Z_qL→Z_n(K⊗L). Its composite with the cycles
inclusion is (i_p^K⊗i_q^L) followed by the (p,q) summand inclusion into (K⊗L)_n. -/
def cyclesPair (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q n : ℕ) (h : p + q =
    n) :
    K.cycles p ⊗ L.cycles q ⟶ (tensorObj K L).cycles n :=
  HomologicalComplex.GradedHomology.cyclesPair K L p q n h

@[reassoc (attr := simp)]
theorem cyclesPair_i (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q n : ℕ) (h : p
    + q = n) :
    cyclesPair K L p q n h ≫ (tensorObj K L).iCycles n =
      (K.iCycles p ⊗ₘ L.iCycles q) ≫ ιTensorObj K L p q n h := by
  exact HomologicalComplex.GradedHomology.cyclesPair_i K L p q n h

@[reassoc (attr := simp)]
theorem quotient_tensorator (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q n : ℕ)
    (h : p + q = n) :
    (K.homologyπ p ⊗ₘ L.homologyπ q) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
        (homologyFunctor.obj L) p q n h ≫ tensorator K L n =
      cyclesPair K L p q n h ≫ (tensorObj K L).homologyπ n := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.quotient_tensorator K L p q n h)

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). Let A,B,C be chain complexes of shape down ℕ and
p,q,r∈ℕ. Pair first H_pA with H_qB, then with H_rC, and apply homology of the chain associator
(A⊗B)⊗C→A⊗(B⊗C). After identifying degree (p+q)+r with p+(q+r), this equals the module
associator followed by pairing H_qB with H_rC and then with H_pA. The equality is between maps
from (H_pA⊗H_qB)⊗H_rC to H_{p+(q+r)}(A⊗(B⊗C)). -/
theorem pair_assoc (A B C : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q r : ℕ) :
    (pair A B p q ⊗ₘ 𝟙 (C.homology r)) ≫
      pair (tensorObj A B) C (p + q) r ≫
      homologyMap (α_ A B C).hom ((p + q) + r) ≫
      eqToHom (congrArg (fun n => (tensorObj A (tensorObj B C)).homology n)
        (Nat.add_assoc p q r)) =
    (α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
      (𝟙 (A.homology p) ⊗ₘ pair B C q r) ≫ pair A (tensorObj B C) p (q + r) := by
  exact HomologicalComplex.GradedHomology.pair_assoc A B C p q r

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For chain complexes A,B,C of shape down ℕ, write
H for graded homology and μ for its cycle tensorator. Then
(μ_{A,B}⊗id_{H(C)})≫μ_{A⊗B,C}≫H(α_{A,B,C})=α_{H(A),H(B),H(C)}≫(id_{H(A)}⊗μ_{B,C})≫μ_{A,B⊗C}. The
source is (H(A)⊗H(B))⊗H(C), and the target is H(A⊗(B⊗C)). -/
@[reassoc]
theorem tensorator_associativity (A B C : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :
    tensorator A B ▷ homologyFunctor.obj C ≫ tensorator (A ⊗ B) C ≫
      homologyFunctor.map (α_ A B C).hom =
    (α_ (homologyFunctor.obj A) (homologyFunctor.obj B) (homologyFunctor.obj C)).hom ≫
      homologyFunctor.obj A ◁ tensorator B C ≫ tensorator A (B ⊗ C) := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_associativity A B C)

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For a chain complex K of shape down ℕ and n∈ℕ,
let u₀:𝟙→H_0(𝟙) be the inverse canonical degree-zero homology comparison for the single
tensor-unit complex. If μ_{0,n} is the (0,n) component of its tensorator with K, then
(u₀⊗id_{H_nK})≫μ_{0,n}≫H_n(λ_K)=λ_{H_nK}. This identifies the scalar unit's cycle class with the
left unit action on homology. -/
theorem unit_left_pair (K : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (n : ℕ) :
    ((singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))).inv
    ⊗ₘ
      𝟙 (K.homology n)) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj (𝟙_ (ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)))
        (homologyFunctor.obj K) 0 n n (zero_add n) ≫ tensorator (𝟙_ (ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) K n ≫
      homologyMap (λ_ K).hom n = (λ_ (K.homology n)).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.unit_left_pair K n)

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For a chain complex K of shape down ℕ and n∈ℕ,
let u₀:𝟙→H_0(𝟙) be the inverse degree-zero homology comparison for the single tensor-unit
complex, and μ_{n,0} the (n,0) tensorator component. Then
(id_{H_nK}⊗u₀)≫μ_{n,0}≫H_n(ρ_K)=ρ_{H_nK}. The unit class therefore acts as the right unit on
H_nK. -/
theorem unit_right_pair (K : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (n : ℕ) :
    (𝟙 (K.homology n) ⊗ₘ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))).inv) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
        (homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ))) n 0 n
    (add_zero n) ≫ tensorator K (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) n ≫
      homologyMap (ρ_ K).hom n = (ρ_ (K.homology n)).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.unit_right_pair K n)

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For a chain complex K of shape down ℕ, let
e:𝟙→H(𝟙) be the canonical homology unit map and μ the cycle tensorator. The left unitor equation
is λ_{H(K)}=(e⊗id_{H(K)})≫μ_{𝟙,K}≫H(λ_K), as maps 𝟙⊗H(K)→H(K). -/
theorem tensorator_left_unitality (K : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :
    (λ_ (homologyFunctor.obj K)).hom = unitMap ▷ homologyFunctor.obj K ≫
      tensorator (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) K ≫ homologyFunctor.map
    (λ_ K).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_left_unitality K)

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For a chain complex K of shape down ℕ, let
e:𝟙→H(𝟙) be the canonical homology unit map and μ the cycle tensorator. The right unitor
equation is ρ_{H(K)}=(id_{H(K)}⊗e)≫μ_{K,𝟙}≫H(ρ_K), as maps H(K)⊗𝟙→H(K). -/
theorem tensorator_right_unitality (K : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :
    (ρ_ (homologyFunctor.obj K)).hom = homologyFunctor.obj K ◁ unitMap ≫
      tensorator K (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) ≫ homologyFunctor.map
    (ρ_ K).hom := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_right_unitality K)

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). The graded homology functor H on chain complexes
of shape down ℕ has a lax monoidal structure with unit map e:𝟙→H(𝟙) and tensorator
μ_{K,L}:H(K)⊗H(L)→H(K⊗L). The unit map is the canonical degree-zero single-complex homology
comparison, and μ is the homogeneous cycle pairing summed over p+q=n. Naturality, associativity
and both unit equations are the cycle-pairing coherence laws. -/
def laxMonoidal : (homologyFunctor (R := R)).LaxMonoidal where
  ε := unitMap
  μ := tensorator
  μ_natural_left f K := by
    simp only [tensorator_eq_gradedHomology]
    exact
      (HomologicalComplex.GradedHomology.laxMonoidal (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v}
    R))).μ_natural_left f K
  μ_natural_right K f := by
    simp only [tensorator_eq_gradedHomology]
    exact
      (HomologicalComplex.GradedHomology.laxMonoidal (V := (ModuleCat.UniverseScalarRestriction.Modules.{u,v}
    R))).μ_natural_right K f
  associativity := tensorator_associativity
  left_unitality := tensorator_left_unitality
  right_unitality := tensorator_right_unitality

end HomologicalComplex.UniverseKunneth
