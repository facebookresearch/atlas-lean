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

public import MathlibExt.Algebra.Homology.UniverseKunneth.Coherence
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyBraiding
public import MathlibExt.Algebra.Homology.KoszulTensorBraiding
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import MathlibExt.Algebra.Homology.GradedHomology.Koszul

/-!
# Koszul braiding of cycle pairings and graded homology

Let R be a commutative ring in universe u and choose a common coefficient universe W=max(u,v),
with v independent of u. For ℕ-graded R-modules X,Y, the Koszul interchange on the degree-n
summand X_p⊗Y_q, p+q=n, is (-1)^{pq} times the module tensor interchange into Y_q⊗X_p. Its
inverse is the same signed interchange with X and Y reversed.

For chain complexes K,L of shape down ℕ, the signed chain tensor braiding induces the same
factor (-1)^{pq} on the homology pairing H_pK⊗H_qL→H_{p+q}(K⊗L). Consequently the graded cycle
tensorator μ:H(K)⊗H(L)→H(K⊗L) commutes with the chain Koszul braiding and the Koszul interchange
on graded homology. These compatibility laws hold over every commutative ring.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.UniverseKunneth

variable {R : Type u} [CommRing R]


/-- For p,q∈ℕ, the Koszul sign is sign(p,q)=(-1)^{pq} as an integer. It is symmetric in p,q, has
square one, and is multiplicative when either degree is added. -/
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

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For ℕ-graded R-modules X,Y, this morphism
σ:X⊗Y→Y⊗X sends the summand X_p⊗Y_q in degree n=p+q through (-1)^{pq} times the module braiding
X_p⊗Y_q→Y_q⊗X_p, then through the target summand inclusion. It is natural in both graded
objects. -/
def koszulSwapHom (X Y : (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))) : X ⊗ Y ⟶ Y ⊗ X :=
  HomologicalComplex.GradedHomology.koszulSwapHom X Y

@[reassoc (attr := simp)]
theorem ι_koszulSwapHom (X Y : (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))) (p q n : ℕ) (h
  : p + q = n) :
    GradedObject.Monoidal.ιTensorObj X Y p q n h ≫ koszulSwapHom X Y n =
      sign p q • ((β_ (X p) (Y q)).hom ≫
        GradedObject.Monoidal.ιTensorObj Y X q p n (by rw [Nat.add_comm, h])) := by
  exact HomologicalComplex.GradedHomology.ι_koszulSwapHom X Y p q n h

@[reassoc]
theorem koszulSwapHom_naturality {X Y X' Y' : (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))}
  (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ koszulSwapHom X' Y' = koszulSwapHom X Y ≫ (g ⊗ₘ f) := by
  exact HomologicalComplex.GradedHomology.koszulSwapHom_naturality f g

@[simp]
theorem koszulSwapHom_involutive (X Y : (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))) :
    koszulSwapHom X Y ≫ koszulSwapHom Y X = 𝟙 (X ⊗ Y) := by
  exact HomologicalComplex.GradedHomology.koszulSwapHom_involutive X Y

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For ℕ-graded R-modules X,Y, this is the
isomorphism X⊗Y≅Y⊗X whose forward map on bidegree (p,q) is (-1)^{pq} times the module
interchange. Its inverse is the signed interchange for Y,X; composing the two gives the identity
because the symmetric sign has square one. -/
def koszulSwap (X Y : (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R))) : X ⊗ Y ≅ Y ⊗ X :=
  HomologicalComplex.GradedHomology.koszulSwap X Y

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). Let K,L be chain complexes of shape down ℕ and
p,q∈ℕ. Write κ_{K,L}^{p,q}:H_pK⊗H_qL→H_{p+q}(K⊗L) for the cycle pairing and b:K⊗L≅L⊗K for the
chain Koszul braiding. Then
κ_{K,L}^{p,q}≫H_{p+q}(b.hom)=(-1)^{pq}•(β_{H_pK,H_qL}.hom≫κ_{L,K}^{q,p}≫e), where e identifies
H_{q+p}(L⊗K) with H_{p+q}(L⊗K) using q+p=p+q. -/
theorem pair_braiding (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) (p q : ℕ) :
    pair K L p q ≫ homologyMap (koszulTensorBraidingIso K L).hom (p + q) =
      sign p q • ((β_ (K.homology p) (L.homology q)).hom ≫
        pair L K q p ≫ (homologyIsoOfEq (tensorObj L K) (Nat.add_comm q p)).hom) := by
  exact HomologicalComplex.GradedHomology.pair_braiding K L p q

/-- Let R be a commutative ring in universe u, v an independent lift height, and all coefficient
modules lie in the common universe W=max(u,v). For chain complexes K,L of shape down ℕ, let H
denote graded homology, μ_{K,L}:H(K)⊗H(L)→H(K⊗L) its cycle tensorator, b the chain Koszul
braiding, and σ:H(K)⊗H(L)≅H(L)⊗H(K) the graded Koszul interchange. Then
μ_{K,L}≫H(b.hom)=σ.hom≫μ_{L,K}. -/
@[reassoc]
theorem tensorator_braiding (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ)) :
    tensorator K L ≫ homologyFunctor.map (koszulTensorBraidingIso K L).hom =
      (koszulSwap (homologyFunctor.obj K) (homologyFunctor.obj L)).hom ≫ tensorator L K := by
  simp only [tensorator_eq_gradedHomology]
  exact
    (HomologicalComplex.GradedHomology.tensorator_braiding K L)

end HomologicalComplex.UniverseKunneth
