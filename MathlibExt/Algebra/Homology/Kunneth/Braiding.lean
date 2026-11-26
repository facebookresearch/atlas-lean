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
# Koszul symmetry of the canonical module Künneth tensorator

Let R be a commutative ring and K,L nonnegative R-module chain complexes.
The canonical Künneth pairings H_p(K)⊗[R]H_q(L)→H_(p+q)(K⊗L)
are compatible with the chain Koszul interchange.

On graded objects, the interchange swaps the (p,q) tensor summand with
coefficient (−1)^(pq), then includes it as the (q,p) summand in the
same total degree. It is involutive. The bidegree homology pairing
equation retains this sign and the degree identification q+p=p+q.

For the full graded tensorator μ, the coherence equation is
H(β_Ch) ∘ μ_(K,L)=μ_(L,K) ∘ β_Koszul.
All module carriers lie in ModuleCat^u(R), and these are equations
for the canonical cycle maps over arbitrary R.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.Kunneth

variable {R : Type u} [CommRing R]


/-- For p,q∈ℕ, the module Koszul sign is (−1)^(pq)∈ℤ.
It is symmetric in the two degrees, squares to 1, and is
multiplicative under addition of either degree. -/
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

/-- For graded R-modules X,Y over a commutative ring R,
the map X⊗Y→Y⊗X restricts on X_p⊗[R]Y_q to the tensor
commutation multiplied by (−1)^(pq), followed by inclusion
of the (q,p) summand in total degree p+q. -/
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

/-- For graded R-modules X,Y over a commutative ring R,
the signed interchange X⊗Y≅Y⊗X has reversed signed
interchange as its inverse.
The two component signs multiply to (−1)^(pq+qp)=1. -/
def koszulSwap (X Y : (GradedObject ℕ (ModuleCat.{u} R))) : X ⊗ Y ≅ Y ⊗ X :=
  HomologicalComplex.GradedHomology.koszulSwap X Y

/-- For nonnegative R-module chain complexes K,L over a
commutative ring R, the canonical pairings satisfy
H_(p+q)(β_Ch) ∘ pair_(K,L) =
(−1)^(pq) e ∘ pair_(L,K) ∘ β_(H_pK,H_qL).
The map e transports homology degree q+p to p+q. -/
theorem pair_braiding (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q : ℕ) :
    pair K L p q ≫ homologyMap (koszulTensorBraidingIso K L).hom (p + q) =
      sign p q • ((β_ (K.homology p) (L.homology q)).hom ≫
        pair L K q p ≫ (homologyIsoOfEq (tensorObj L K) (Nat.add_comm q p)).hom) := by
  exact HomologicalComplex.GradedHomology.pair_braiding K L p q

/-- For nonnegative R-module chain complexes K,L over a
commutative ring R, the graded cycle tensorator satisfies
H(β_Ch) ∘ μ_(K,L)=μ_(L,K) ∘ β_Koszul.
The graded interchange has coefficient (−1)^(pq) on each
homogeneous tensor summand. -/
@[reassoc]
theorem tensorator_braiding (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    tensorator K L ≫ homologyFunctor.map (koszulTensorBraidingIso K L).hom =
      (koszulSwap (homologyFunctor.obj K) (homologyFunctor.obj L)).hom ≫ tensorator L K := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_braiding K L)

end HomologicalComplex.Kunneth
