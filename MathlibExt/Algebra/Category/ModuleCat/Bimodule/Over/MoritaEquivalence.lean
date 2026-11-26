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

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.Over.MoritaCoordinates
public import Mathlib.CategoryTheory.Equivalence

/-!
# Relative Morita equivalence and its complete return maps

Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. At W=max(p,q,v), the tensor functors F(X)=(Q⊗_R X)⊗_R P
and G(Y)=(P⊗_S Y)⊗_S Q act between the relative enveloping-module categories.

A right R-linear contraction α:P⊗_S Q≃R preserving the left action gives the return G(FX)≅X. Its
forward map first takes the raw coefficient coordinates, then contracts both P⊗_S Q pairs, then
uses the identity-coefficient comparison from the reconstructed module to X. Its value is
(α(p₀⊗q₀)⊗op(α(p₁⊗q₁)))•x, and the inverse reverses these three maps.

These returns are natural on the transported object presentations and on the full composite
functor. With a symmetric S-bimodule contraction β:Q⊗_R P≃S, they give an equivalence of the two
categories at W. The β-return is the retained counit ε. Starting from the inverse α-return η⁰,
the chosen unit is η_X=η⁰_X≫G(ε_{FX}⁻¹)≫GF((η⁰_X)⁻¹).

A general component construction states the naturality condition for changing a functor's object
representatives along isomorphisms. It applies to arbitrary categories and functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced
open scoped TensorProduct

universe u r s p q v

namespace ModuleCat.Bimodule.Over.Morita

variable (k : Type u) [CommRing k]
  (R : Type r) [Ring R] [Algebra k R] (S : Type s) [Ring S] [Algebra k S]
  (P : Type p) [AddCommGroup P] [Module k P]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  (Q : Type q) [AddCommGroup Q] [Module k Q]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]
  (u : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    TensorProduct.Balanced k S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced k S P Q), u (r • b) = r * u b)

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), the object D_X=G(FX) is an
E_R^k-module in W. Its coefficient carrier is the nested tensor (P⊗_S((Q⊗_R X)⊗_R P))⊗_S Q. -/
def returnCompositeObject (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
  ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), the raw coefficient object A_X=T(X)
uses X's extracted ground k-action and endpoint R-actions. It has the ordered P–Q–X–P–Q tensor
carrier in W and computed outer R-actions. -/
def returnCoefficientObject (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact rawReturnObject k R S P Q X

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. The isomorphism e_X
preserves the ground k-action and both R-actions, and takes each composite outer class to the
same raw ordered tensor class. -/
def returnCoordinateIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCompositeObject k R S P Q X ≅ returnCoefficientObject k R S P Q X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact returnCoordinates k R S P Q X

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. The forward map
e_X.hom:D_X→A_X is E_R^k-linear. On each outer class (p₀⊗c)⊗q₁ it retains p₀,c,q₁ in raw
coefficient coordinates. -/
def returnCoordinateHom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCompositeObject k R S P Q X ⟶ returnCoefficientObject k R S P Q X := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  let E : D ≅ A := returnCoordinateIso k R S P Q X
  let L : D →ₗ[R ⊗[k] Rᵐᵒᵖ] A :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D A E.hom
  exact @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ D.carrier A.carrier
    D.isAddCommGroup D.isModule A.isAddCommGroup A.isModule L

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. The inverse map
e_X.inv:A_X→D_X restores the composite presentation of the same ordered tensor coefficient. It
is E_R^k-linear at carrier height W. -/
def returnCoordinateInv (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoefficientObject k R S P Q X ⟶ returnCompositeObject k R S P Q X := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  let E : D ≅ A := returnCoordinateIso k R S P Q X
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] D :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A D E.inv
  exact @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ A.carrier D.carrier
    A.isAddCommGroup A.isModule D.isAddCommGroup D.isModule L

private theorem returnCoordinateHom_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateHom k R S P Q X = (returnCoordinateIso k R S P Q X).hom := by
  change ModuleCat.ofHom ((returnCoordinateIso k R S P Q X).hom.hom) = _
  exact ModuleCat.ofHom_hom (returnCoordinateIso k R S P Q X).hom

private theorem returnCoordinateInv_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateInv k R S P Q X = (returnCoordinateIso k R S P Q X).inv := by
  change ModuleCat.ofHom ((returnCoordinateIso k R S P Q X).inv.hom) = _
  exact ModuleCat.ofHom_hom (returnCoordinateIso k R S P Q X).inv

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. The equation
e_X.hom≫e_X.inv=id_{D_X} holds in ModuleCat_W(E_R^k). Thus coordinate transport to A_X and back
fixes every composite coefficient. -/
theorem returnCoordinateHom_inv (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateHom k R S P Q X ≫ returnCoordinateInv k R S P Q X =
      𝟙 (returnCompositeObject k R S P Q X) := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  exact (congrArg₂ (fun (f : D ⟶ A) (g : A ⟶ D) => f ≫ g)
    (returnCoordinateHom_eq k R S P Q X) (returnCoordinateInv_eq k R S P Q X)).trans
      (returnCoordinateIso k R S P Q X).hom_inv_id

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. The equation
e_X.inv≫e_X.hom=id_{A_X} holds. Restoring the composite presentation and then taking raw
coordinates leaves the coefficient object unchanged. -/
theorem returnCoordinateInv_hom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateInv k R S P Q X ≫ returnCoordinateHom k R S P Q X =
      𝟙 (returnCoefficientObject k R S P Q X) := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  exact (congrArg₂ (fun (f : A ⟶ D) (g : D ⟶ A) => f ≫ g)
    (returnCoordinateInv_eq k R S P Q X) (returnCoordinateHom_eq k R S P Q X)).trans
      (returnCoordinateIso k R S P Q X).inv_hom_id

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The morphism c_X.hom:A_X→B_X is E_R^k-linear. Its
five-factor value is α(p₀⊗q₀)•(op(α(p₁⊗q₁))•x) using the endpoint actions of B_X. -/
def returnContractionHom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoefficientObject k R S P Q X ⟶ ModuleCat.Bimodule.Over.reconstructedObject k R X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B := rawReturnLinear k R S P Q X u hu
  exact @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ A.carrier B.carrier
    A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule L

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The E_R^k-linear inverse c_X.inv:B_X→A_X inserts α⁻¹(1)
into both paired tensor positions and reverses the return reassociation. -/
def returnContractionInv (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.Bimodule.Over.reconstructedObject k R X ⟶ returnCoefficientObject k R S P Q X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : B →ₗ[R ⊗[k] Rᵐᵒᵖ] A := rawReturnInverseLinear k R S P Q X u hu
  exact @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ B.carrier A.carrier
    B.isAddCommGroup B.isModule A.isAddCommGroup A.isModule L

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The contraction and its inverse form the isomorphism
c_X:A_X≅B_X. It retains the ground k-action and both endpoint R-actions at the common height W. -/
def returnContractionIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoefficientObject k R S P Q X ≅ ModuleCat.Bimodule.Over.reconstructedObject k R X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact rawReturnModuleIso k R S P Q X u hu

include u hu in
private theorem returnContractionHom_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnContractionHom k R S P Q u hu X = (returnContractionIso k R S P Q u hu X).hom := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B := rawReturnLinear k R S P Q X u hu
  apply ModuleCat.hom_ext
  exact (ModuleCat.hom_ofHom L).trans (ModuleCat.hom_ofHom L).symm

include u hu in
private theorem returnContractionInv_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnContractionInv k R S P Q u hu X = (returnContractionIso k R S P Q u hu X).inv := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : B →ₗ[R ⊗[k] Rᵐᵒᵖ] A := rawReturnInverseLinear k R S P Q X u hu
  apply ModuleCat.hom_ext
  exact (ModuleCat.hom_ofHom L).trans (ModuleCat.hom_ofHom L).symm

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The equality c_X.hom≫c_X.inv=id_{A_X} holds. The paired
α-contractions and their inverses recover every raw return coefficient. -/
theorem returnContractionHom_inv (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnContractionHom k R S P Q u hu X ≫ returnContractionInv k R S P Q u hu X =
      𝟙 (returnCoefficientObject k R S P Q X) := by
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  exact (congrArg₂ (fun (f : A ⟶ B) (g : B ⟶ A) => f ≫ g)
    (returnContractionHom_eq k R S P Q u hu X)
    (returnContractionInv_eq k R S P Q u hu X)).trans
      (returnContractionIso k R S P Q u hu X).hom_inv_id

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The equality c_X.inv≫c_X.hom=id_{B_X} holds, giving the
identity on the reconstructed ground and endpoint module. -/
theorem returnContractionInv_hom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnContractionInv k R S P Q u hu X ≫ returnContractionHom k R S P Q u hu X =
      𝟙 (ModuleCat.Bimodule.Over.reconstructedObject k R X) := by
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  exact (congrArg₂ (fun (f : B ⟶ A) (g : A ⟶ B) => f ≫ g)
    (returnContractionInv_eq k R S P Q u hu X)
    (returnContractionHom_eq k R S P Q u hu X)).trans
      (returnContractionIso k R S P Q u hu X).inv_hom_id

private theorem threeHom_inverse {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞}
    (c : A ⟶ B) (f : B ⟶ C) (h : C ⟶ D)
    (ci : B ⟶ A) (fi : C ⟶ B) (hi : D ⟶ C)
    (hc : c ≫ ci = 𝟙 A) (hf : f ≫ fi = 𝟙 B) (hh : h ≫ hi = 𝟙 C) :
    (c ≫ (f ≫ h)) ≫ ((hi ≫ fi) ≫ ci) = 𝟙 A := by
  calc
    (c ≫ (f ≫ h)) ≫ ((hi ≫ fi) ≫ ci) =
        c ≫ (f ≫ ((h ≫ hi) ≫ (fi ≫ ci))) := by simp only [Category.assoc]
    _ = c ≫ (f ≫ (fi ≫ ci)) := by rw [hh, Category.id_comp]
    _ = c ≫ ((f ≫ fi) ≫ ci) := by simp only [Category.assoc]
    _ = c ≫ ci := by rw [hf, Category.id_comp]
    _ = 𝟙 A := hc

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The forward return r_X:D_X→X is
e_X.hom≫(c_X.hom≫j_X.hom). Its three maps preserve the given ground and endpoint actions. -/
def returnHom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCompositeObject k R S P Q X ⟶ X :=
  returnCoordinateHom k R S P Q X ≫
    (returnContractionHom k R S P Q u hu X ≫
      (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom)

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The return morphism satisfies
r_X=e_X.hom≫(c_X.hom≫j_X.hom):D_X→X. The order is raw coordinate comparison, α-contraction to
B_X, then the identity-coefficient reconstruction comparison. -/
theorem returnHom_parts (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnHom k R S P Q u hu X = returnCoordinateHom k R S P Q X ≫
      (returnContractionHom k R S P Q u hu X ≫
        (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom) := rfl

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The inverse s_X:X→D_X is (j_X.inv≫c_X.inv)≫e_X.inv. It
passes first to the reconstructed module, then to raw return coefficients, then to the composite
presentation. -/
def returnInverse (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    X ⟶ returnCompositeObject k R S P Q X :=
  ((ModuleCat.Bimodule.Over.reconstructedIso k R X).inv ≫
    returnContractionInv k R S P Q u hu X) ≫ returnCoordinateInv k R S P Q X

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. For r_X=e_X.hom≫c_X.hom≫j_X.hom and
s_X=j_X.inv≫c_X.inv≫e_X.inv, one has r_X≫s_X=id_{D_X}. -/
theorem returnHom_inverse (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnHom k R S P Q u hu X ≫ returnInverse k R S P Q u hu X =
      𝟙 (returnCompositeObject k R S P Q X) := by
  exact threeHom_inverse (returnCoordinateHom k R S P Q X)
    (returnContractionHom k R S P Q u hu X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom
    (returnCoordinateInv k R S P Q X) (returnContractionInv k R S P Q u hu X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).inv
    (returnCoordinateHom_inv k R S P Q X) (returnContractionHom_inv k R S P Q u hu X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom_inv_id

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The maps s_X:X→D_X and r_X:D_X→X satisfy s_X≫r_X=id_X.
Both composites use the same coordinate, contraction, and reconstruction isomorphisms. -/
theorem returnInverse_hom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnInverse k R S P Q u hu X ≫ returnHom k R S P Q u hu X = 𝟙 X := by
  have h := threeHom_inverse (ModuleCat.Bimodule.Over.reconstructedIso k R X).inv
    (returnContractionInv k R S P Q u hu X) (returnCoordinateInv k R S P Q X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom
    (returnContractionHom k R S P Q u hu X) (returnCoordinateHom k R S P Q X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).inv_hom_id
    (returnContractionInv_hom k R S P Q u hu X) (returnCoordinateInv_hom k R S P Q X)
  simpa only [returnHom, returnInverse, Category.assoc] using h

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The isomorphism D_X≅X has forward map
r_X=e_X.hom≫c_X.hom≫j_X.hom and inverse s_X=j_X.inv≫c_X.inv≫e_X.inv. -/
def returnObjectIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCompositeObject k R S P Q X ≅ X where
  hom := returnHom k R S P Q u hu X
  inv := returnInverse k R S P Q u hu X
  hom_inv_id := returnHom_inverse k R S P Q u hu X
  inv_hom_id := returnInverse_hom k R S P Q u hu X

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), the comparison G(FX)≅D_X is the
identity isomorphism of the same composite module object. Both coefficient maps send every
tensor class to itself. -/
def returnObjectViewIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X ≅
      returnCompositeObject k R S P Q X :=
  Iso.refl (returnCompositeObject k R S P Q X)

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), put D_X=G(FX), A_X=T(X) for the raw
return coefficient object, and e_X:D_X≅A_X for the coordinate comparison. Let α:P⊗_S Q≃R be
right R-linear and satisfy α(r•b)=rα(b). Let B_X=X_rec be the module reconstructed from the
ground and endpoint actions of X, with identity-coefficient isomorphism j_X:B_X≅X. Let
c_X:A_X≅B_X be the α-return contraction. The isomorphism κ_{α,X}:G(FX)≅X is the composite-object
identity comparison followed by D_X≅X. Its forward map is the coordinate comparison followed by
contraction and the reconstruction comparison. -/
def returnIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X ≅ X :=
  (returnObjectViewIso k R S P Q X).trans (returnObjectIso k R S P Q u hu X)

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let H=GF, D_X=H(X), and t_X:H(X)≅D_X be the identity object
comparison. The transported functor H_D has object D_X and map t_X.inv≫H(f)≫t_Y.hom. It is an
endofunctor of ModuleCat_W(E_R^k). -/
def returnCompositeViewFunctor :
    ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤ ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
  ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).copyObj
    (returnCompositeObject k R S P Q) (returnObjectViewIso k R S P Q)

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For f:X→Y in ModuleCat_W(E_R^k), put D_X=G(FX) and D_Y=G(FY).
The map D_X→D_Y is (GF)(f). It is the composite tensor map acting on the middle X-coefficient
while retaining the four outer P,Q factors. -/
def returnCompositeMap {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    returnCompositeObject k R S P Q X ⟶ returnCompositeObject k R S P Q Y :=
  ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).map f

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For f:X→Y in ModuleCat_W(E_R^k), put D_X=G(FX), D_Y=G(FY). The
return-composite morphism D_X→D_Y equals (GF)(f) with the same source and target object
presentations. It has the same underlying E_R^k-linear map. -/
theorem returnCompositeMap_eq {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    returnCompositeMap k R S P Q f =
      (show returnCompositeObject k R S P Q X ⟶ returnCompositeObject k R S P Q Y from
        ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).map f) := by
  rfl

private theorem abstractCopyObj_map {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) (obj : 𝒞 → 𝒟) (e : ∀ X, F.obj X ≅ obj X)
    {X Y : 𝒞} (f : X ⟶ Y) :
    (F.copyObj obj e).map f = (e X).inv ≫ F.map f ≫ (e Y).hom := rfl

private def abstractViewMap {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) (obj : 𝒞 → 𝒟) (e : ∀ Z, F.obj Z ≅ obj Z)
    {X Y : 𝒞} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  (e X).inv ≫ F.map f ≫ (e Y).hom

private theorem abstractViewMap_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) (obj : 𝒞 → 𝒟) (e : ∀ Z, F.obj Z ≅ obj Z)
    {X Y : 𝒞} (f : X ⟶ Y) :
    (F.copyObj obj e).map f = abstractViewMap F obj e f :=
  abstractCopyObj_map F obj e f

private theorem abstractIdentityViewMap_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) {X Y : 𝒞} (f : X ⟶ Y) :
    abstractViewMap F F.obj (fun Z => Iso.refl (F.obj Z)) f = F.map f := by
  simp only [abstractViewMap, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]

private def returnViewMap {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) :
    returnCompositeObject k R S P Q X ⟶ returnCompositeObject k R S P Q Y := by
  let H : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)
  exact abstractViewMap H (returnCompositeObject k R S P Q)
    (returnObjectViewIso k R S P Q) (X := X) (Y := Y) f

private theorem returnViewMap_eq {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) :
    returnViewMap k R S P Q f = returnCompositeMap k R S P Q f := by
  let H : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)
  exact abstractIdentityViewMap_eq H (X := X) (Y := Y) f

private def returnCoordinateValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    P → returnIntermediateCarrier k R S P Q X → Q →
      (returnCoefficientObject k R S P Q X).carrier := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  let L : D →ₗ[R ⊗[k] Rᵐᵒᵖ] A :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D A (returnCoordinateHom k R S P Q X)
  exact fun p₀ c q₁ => L (returnOuterMk k R S P Q X p₀ c q₁)

private def returnCoordinateTargetValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    P → returnIntermediateCarrier k R S P Q X → Q →
      (returnCoefficientObject k R S P Q X).carrier := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact fun p₀ c q₁ => rawReturnOuterMk k R S P Q X p₀ c q₁

private theorem returnCoordinateValue_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateValue k R S P Q X = returnCoordinateTargetValue k R S P Q X := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  funext p₀ c q₁
  let z : D := returnOuterMk k R S P Q X p₀ c q₁
  have h := congrArg
    (fun f : D ⟶ A => (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D A f) z)
    (returnCoordinateHom_eq k R S P Q X)
  exact h.trans (returnCoordinates_mk k R S P Q X p₀ c q₁)

private theorem returnCoordinateHom_mk (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ))
    (p₀ : P) (c : returnIntermediateCarrier k R S P Q X) (q₁ : Q) :
    returnCoordinateValue k R S P Q X p₀ c q₁ =
      returnCoordinateTargetValue k R S P Q X p₀ c q₁ :=
  congrFun (congrFun (congrFun (returnCoordinateValue_eq k R S P Q X) p₀) c) q₁

include u hu in
private def returnContractionValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    (returnCoefficientObject k R S P Q X).carrier → X := by
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B (returnContractionHom k R S P Q u hu X)
  exact fun b => L b

private theorem ofHomFunction_heq {R' : Type*} [Ring R']
    {A B : ModuleCat R'} (L : A →ₗ[R'] B) :
    HEq (fun x : A.carrier =>
      (@ModuleCat.Hom.hom R' _ A B
        (@ModuleCat.ofHom R' _ A.carrier B.carrier
          A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule L)) x) L.toFun :=
  heq_of_eq (congrArg (fun f : A →ₗ[R'] B => f.toFun) (ModuleCat.hom_ofHom L))

private theorem applyFunctionHEq (A B : Type v) (M : Type*)
    (f : A → M) (g : B → M)
    (x : A) (y : B) (hf : HEq f g) (hx : HEq x y) : f x = g y := by
  cases hx
  exact congrFun (eq_of_heq hf) x

include u hu in
private theorem rawReturnLinearFunction_heq
    (M : Type (max p q v)) [gM : AddCommGroup M] [dK : Module k M]
    [dR : Module R M] [dRop : Module Rᵐᵒᵖ M]
    [cM : SMulCommClass R Rᵐᵒᵖ M]
    [tL : IsScalarTower k R M] [tR : IsScalarTower k Rᵐᵒᵖ M] :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    HEq (rawReturnLinear k R S P Q M u hu).toFun
      (rawReturnModuleHom.{u, r, s, p, q, v} k R S P Q M u hu) := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  have hField : HEq (rawReturnLinear k R S P Q M u hu).toFun
      (rawReturnIso k R S P Q M u hu).toFun := HEq.rfl
  exact hField.trans (rawReturnModuleHom_heq.{u, r, s, p, q, v} k R S P Q M u hu).symm

include u hu in
private theorem returnContractionValue_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    letI := ModuleCat.Bimodule.Over.groundModule k R X
    letI := ModuleCat.Bimodule.Over.leftModule k R X
    letI := ModuleCat.Bimodule.Over.rightModule k R X
    letI := ModuleCat.Bimodule.Over.leftTower k R X
    letI := ModuleCat.Bimodule.Over.rightTower k R X
    letI := ModuleCat.Bimodule.Over.commute k R X
    HEq (returnContractionValue k R S P Q u hu X)
      (rawReturnModuleHom k R S P Q X u hu) := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let rawDomain : Type (max p q v) := (rawReturnObject k R S P Q X).carrier
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B := rawReturnLinear k R S P Q X u hu
  have hSame : returnContractionValue k R S P Q u hu X =
      (fun b : A.carrier => (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B
        (returnContractionIso k R S P Q u hu X).hom) b) :=
    congrArg (fun f : A ⟶ B => fun b : A.carrier =>
      (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B f) b)
      (returnContractionHom_eq k R S P Q u hu X)
  have hField : HEq
      (fun b : A.carrier => (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B
        (returnContractionIso k R S P Q u hu X).hom) b) L.toFun :=
    ofHomFunction_heq L
  have hRaw := rawReturnLinearFunction_heq.{u, r, s, p, q, v}
    (k := k) (R := R) (S := S) (P := P) (Q := Q) (u := u) (hu := hu)
    (M := X.carrier) (gM := X.isAddCommGroup)
    (dK := ModuleCat.Bimodule.Over.groundModule k R X)
    (dR := ModuleCat.Bimodule.Over.leftModule k R X)
    (dRop := ModuleCat.Bimodule.Over.rightModule k R X)
    (cM := ModuleCat.Bimodule.Over.commute k R X)
    (tL := ModuleCat.Bimodule.Over.leftTower k R X)
    (tR := ModuleCat.Bimodule.Over.rightTower k R X)
  exact (heq_of_eq hSame).trans (hField.trans hRaw)

include u hu in
private def returnOrderedValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    P → Q → X → P → Q → X :=
  fun p₀ q₀ x p₁ q₁ => X.isModule.smul
    (contractionScalar k R S P Q u p₀ q₀ ⊗ₜ[k]
      op (contractionScalar k R S P Q u p₁ q₁)) x

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). For
X∈ModuleCat_W(E_R^k), define V_X:P→Q→X→P→Q→X by evaluating r_X on (p₀⊗((q₀⊗x)⊗p₁))⊗q₁. Here r_X
is the complete return morphism G(FX)→X. Its coefficient value is (α(p₀⊗q₀)⊗_k op(α(p₁⊗q₁)))•_X
x. -/
private def returnIsoValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    P → Q → X → P → Q → X := by
  let T := returnCompositeObject k R S P Q X
  let L : T →ₗ[R ⊗[k] Rᵐᵒᵖ] X :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ T X (returnHom k R S P Q u hu X)
  exact fun p₀ q₀ x p₁ q₁ =>
    L (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁)

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). For
X∈ModuleCat_W(E_R^k), the full function V_X equals (p₀,q₀,x,p₁,q₁)↦(α(p₀⊗q₀)⊗_k op(α(p₁⊗q₁)))•_X
x. The scalar acts through the given enveloping-module structure of X. -/
private theorem returnIsoValue_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnIsoValue k R S P Q u hu X = returnOrderedValue (k := k) (R := R) (S := S) (P := P)
        (Q := Q) (u := u) X := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let T := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let cMap : T →ₗ[R ⊗[k] Rᵐᵒᵖ] A :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ T A (returnCoordinateHom k R S P Q X)
  let fMap : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B (returnContractionHom k R S P Q u hu X)
  let hMap : B →ₗ[R ⊗[k] Rᵐᵒᵖ] X :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ B X
      (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom
  have hIso : returnHom k R S P Q u hu X = returnCoordinateHom k R S P Q X ≫
      (returnContractionHom k R S P Q u hu X ≫
        (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom) :=
    returnHom_parts k R S P Q u hu X
  funext p₀ q₀ x p₁ q₁
  let c : tensorObj k R S P Q X := tensorMk k R S P Q X q₀ x p₁
  let z : T := returnOuterMk k R S P Q X p₀ c q₁
  let b : A := rawReturnModuleMk k R S P Q X p₀ q₀ x p₁ q₁
  have hC : cMap z = b := returnCoordinateHom_mk k R S P Q X p₀ c q₁
  have hF : fMap b = orderedReturnValue k R S P Q X u p₀ q₀ x p₁ q₁ := by
    let rawPoint : rawReturnObject k R S P Q X :=
      rawReturnModuleMk k R S P Q X p₀ q₀ x p₁ q₁
    have hPoint : HEq b rawPoint := HEq.rfl
    have hNative : fMap b = rawReturnModuleHom k R S P Q X u hu rawPoint :=
      applyFunctionHEq A.carrier (rawReturnObject k R S P Q X).carrier X.carrier
        (returnContractionValue k R S P Q u hu X) (rawReturnModuleHom k R S P Q X u hu)
        b rawPoint (returnContractionValue_eq k R S P Q u hu X) hPoint
    exact hNative.trans
      ((nativeReturnValue_apply k R S P Q X u hu p₀ q₀ x p₁ q₁).symm.trans
        (rawReturnModuleIso_hom_mk k R S P Q X u hu p₀ q₀ x p₁ q₁))
  have hApply : returnIsoValue k R S P Q u hu X p₀ q₀ x p₁ q₁ =
      hMap (fMap (cMap z)) := by
    have h := congrArg
      (fun f : T ⟶ X => (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ T X f) z) hIso
    exact h
  exact hApply.trans
    ((congrArg (fun y : A => hMap (fMap y)) hC).trans
      ((ModuleCat.Bimodule.Over.reconstructedIso_hom_apply k R X (fMap b)).trans
        (hF.trans ((orderedReturnValue_apply k R S P Q X u p₀ q₀ x p₁ q₁).trans
          (ModuleCat.Bimodule.Over.smul_tmul k R X
            (contractionScalar k R S P Q u p₀ q₀)
            (op (contractionScalar k R S P Q u p₁ q₁)) x)))))

-- keeps the actual composite-object getter for rw; Functor.comp_obj simplifies its source
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). For
X∈ModuleCat_W(E_R^k), the return κ_{α,X} sends (p₀⊗((q₀⊗x)⊗p₁))⊗q₁ to (α(p₀⊗q₀)⊗_k
op(α(p₁⊗q₁)))•_X x. The order of all five coefficients is retained. -/

@[simp, nolint simpNF]
theorem returnIso_mk (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ))
    (p₀ : P) (q₀ : Q) (x : X) (p₁ : P) (q₁ : Q) :
    letI := ModuleCat.Bimodule.Over.groundModule k R X
    letI := ModuleCat.Bimodule.Over.leftModule k R X
    letI := ModuleCat.Bimodule.Over.rightModule k R X
    letI := ModuleCat.Bimodule.Over.leftTower k R X
    letI := ModuleCat.Bimodule.Over.rightTower k R X
    letI := ModuleCat.Bimodule.Over.commute k R X
    letI := TensorProduct.Balanced.rightModule k R R Q X
    let T : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
      ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X
    (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ T X
      (show T ⟶ X from (returnIso k R S P Q u hu X).hom))
        (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁) =
      X.isModule.smul
        (contractionScalar k R S P Q u p₀ q₀ ⊗ₜ[k]
          op (contractionScalar k R S P Q u p₁ q₁)) x := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let := TensorProduct.Balanced.rightModule k R R Q X
  change returnIsoValue k R S P Q u hu X p₀ q₀ x p₁ q₁ =
    returnOrderedValue (k := k) (R := R) (S := S) (P := P) (Q := Q) (u := u) X p₀ q₀ x p₁ q₁
  exact congrFun (congrFun (congrFun (congrFun (congrFun
    (returnIsoValue_eq k R S P Q u hu X) p₀) q₀) x) p₁) q₁

include u hu in
private def returnNaturalityHomLeft {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) : returnCompositeObject k R S P Q X ⟶ Y :=
  returnCompositeMap k R S P Q f ≫ returnHom k R S P Q u hu Y

include u hu in
private def returnNaturalityHomRight {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) : returnCompositeObject k R S P Q X ⟶ Y :=
  returnHom k R S P Q u hu X ≫ f

include u hu in
private def returnNaturalityLeft {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) : P → Q → X → P → Q → Y := by
  let D := returnCompositeObject k R S P Q X
  let E := returnCompositeObject k R S P Q Y
  let F : D →ₗ[R ⊗[k] Rᵐᵒᵖ] E :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D E (returnCompositeMap k R S P Q f)
  let G : E →ₗ[R ⊗[k] Rᵐᵒᵖ] Y :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ E Y (returnHom k R S P Q u hu Y)
  exact fun p₀ q₀ x p₁ q₁ => G (F
    (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁))

include u hu in
private def returnNaturalityRight {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) : P → Q → X → P → Q → Y :=
  fun p₀ q₀ x p₁ q₁ => f.hom (returnIsoValue k R S P Q u hu X p₀ q₀ x p₁ q₁)

private def returnCompositePureValue
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y := by
  let D := returnCompositeObject k R S P Q X
  let E := returnCompositeObject k R S P Q Y
  let L : D →ₗ[R ⊗[k] Rᵐᵒᵖ] E :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D E (returnCompositeMap k R S P Q f)
  exact fun p₀ q₀ x p₁ q₁ =>
    L (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁)

private def returnCompositeMappedPureValue
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y :=
  fun p₀ q₀ x p₁ q₁ =>
    returnOuterMk k R S P Q Y p₀ (tensorMk k R S P Q Y q₀ (f.hom x) p₁) q₁

private theorem returnCompositeMapValues_eq
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    (returnCompositePureValue.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f :
      P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y) =
      returnCompositeMappedPureValue.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let G : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) := tensorFunctor k S R Q P
  let D := returnCompositeObject k R S P Q X
  let E := returnCompositeObject k R S P Q Y
  let pre (h : P → returnIntermediateCarrier k R S P Q X → Q →
      returnCompositeCarrier k R S P Q Y) :
      P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y :=
    fun p₀ q₀ x p₁ q₁ => h p₀ (tensorMk k R S P Q X q₀ x p₁) q₁
  have hArrow : returnCompositeMap k R S P Q f =
      (show D ⟶ E from tensorMap k S R Q P (F.map f)) :=
    (returnCompositeMap_eq k R S P Q f).trans
      (returnComposite_map.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f)
  have hArrowValues := congrArg
    (fun a : D ⟶ E => fun (p₀ : P)
      (c : returnIntermediateCarrier k R S P Q X) (q₁ : Q) =>
      (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D E a)
        (returnOuterMk k R S P Q X p₀ c q₁)) hArrow
  have hNative : returnCompositePureValue k R S P Q f =
      pre (returnOuterMapValue k R S P Q f) :=
    congrArg pre hArrowValues
  have hOuter := congrArg pre
    (returnOuterMapValue_eq.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f)
  let innerActual : Q → X → P → returnIntermediateCarrier k R S P Q Y :=
    fun q₀ x p₁ => (tensorMap k R S P Q f).hom (tensorMk k R S P Q X q₀ x p₁)
  let innerExpected : Q → X → P → returnIntermediateCarrier k R S P Q Y :=
    fun q₀ x p₁ => tensorMk k R S P Q Y q₀ (f.hom x) p₁
  have hInner : innerActual = innerExpected := by
    funext q₀ x p₁
    exact tensorMap_mk k R S P Q f q₀ x p₁
  let put (h : Q → X → P → returnIntermediateCarrier k R S P Q Y) :
      P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y :=
    fun p₀ q₀ x p₁ q₁ => returnOuterMk k R S P Q Y p₀ (h q₀ x p₁) q₁
  exact hNative.trans (hOuter.trans (congrArg put hInner))

include u hu in
private theorem returnHom_pure_value (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ))
    (p₀ : P) (q₀ : Q) (x : X) (p₁ : P) (q₁ : Q) :
    (returnHom k R S P Q u hu X).hom
      (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁) =
    X.isModule.smul
      (contractionScalar k R S P Q u p₀ q₀ ⊗ₜ[k]
        op (contractionScalar k R S P Q u p₁ q₁)) x := by
  exact congrFun (congrFun (congrFun (congrFun (congrFun
    (returnIsoValue_eq.{u, r, s, p, q, v} k R S P Q u hu X) p₀) q₀) x) p₁) q₁

include u hu in
private theorem returnNaturalityValue_eq
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    (returnNaturalityLeft.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f :
      P → Q → X → P → Q → Y) =
      returnNaturalityRight.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f := by
  let E := returnCompositeObject k R S P Q Y
  let L : E →ₗ[R ⊗[k] Rᵐᵒᵖ] Y :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ E Y (returnHom k R S P Q u hu Y)
  let post (h : P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y) :
      P → Q → X → P → Q → Y := fun p₀ q₀ x p₁ q₁ => L (h p₀ q₀ x p₁ q₁)
  have hMap := congrArg post
    (returnCompositeMapValues_eq.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f)
  let inY (h : P → Q → Y → P → Q → Y) : P → Q → X → P → Q → Y :=
    fun p₀ q₀ x p₁ q₁ => h p₀ q₀ (f.hom x) p₁ q₁
  let outX (h : P → Q → X → P → Q → X) : P → Q → X → P → Q → Y :=
    fun p₀ q₀ x p₁ q₁ => f.hom (h p₀ q₀ x p₁ q₁)
  have hY := congrArg inY (returnIsoValue_eq.{u, r, s, p, q, v} k R S P Q u hu Y)
  have hX := congrArg outX (returnIsoValue_eq.{u, r, s, p, q, v} k R S P Q u hu X)
  have hScalar :
      inY (returnOrderedValue.{u, r, s, p, q, v} k R S P Q u Y) =
      outX (returnOrderedValue.{u, r, s, p, q, v} k R S P Q u X) := by
    funext p₀ q₀ x p₁ q₁
    exact (f.hom.map_smul
      (contractionScalar k R S P Q u p₀ q₀ ⊗ₜ[k]
        op (contractionScalar k R S P Q u p₁ q₁)) x).symm
  exact hMap.trans (hY.trans (hScalar.trans hX.symm))

private theorem abstractCompositionAdditive_apply {T : Type*} [Ring T]
    {A B C : ModuleCat T} (f : A ⟶ B) (g : B ⟶ C) (x : A.carrier) :
    ((f ≫ g).hom.toAddMonoidHom) x = g.hom (f.hom x) :=
  congrArg (fun L : A →ₗ[T] C => L.toAddMonoidHom x) (ModuleCat.hom_comp f g)

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). Let
r_Z:G(FZ)→Z be the two-contraction return for each Z. For f:X→Y in ModuleCat_W(E_R^k),
(GF)(f)≫r_Y=r_X≫f as maps G(FX)→Y. The return morphisms r_X,r_Y use the same α-contractions and
the given enveloping scalar actions. -/
private theorem returnIso_naturality
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    returnNaturalityHomLeft.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f =
      returnNaturalityHomRight.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f := by

  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let := ModuleCat.Bimodule.Over.groundModule k R Y
  let := ModuleCat.Bimodule.Over.leftModule k R Y
  let := ModuleCat.Bimodule.Over.rightModule k R Y
  let := ModuleCat.Bimodule.Over.leftTower k R Y
  let := ModuleCat.Bimodule.Over.rightTower k R Y
  let := ModuleCat.Bimodule.Over.commute k R Y
  let := TensorProduct.Balanced.rightModule k R R Q X
  let := TensorProduct.Balanced.rightModule k R R Q Y
  let H : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)
  let left : H.obj X ⟶ Y :=
    show H.obj X ⟶ Y from
      returnNaturalityHomLeft.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f
  let right : H.obj X ⟶ Y :=
    show H.obj X ⟶ Y from
      returnNaturalityHomRight.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f
  let L : H.obj X →+ Y.carrier :=
    (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ (H.obj X) Y left).toAddMonoidHom
  let R' : H.obj X →+ Y.carrier :=
    (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ (H.obj X) Y right).toAddMonoidHom
  have hAdd : L = R' := by
    refine returnHom_ext.{u, r, s, p, q, v} k R S P Q X
      (C' := Y.carrier) (f := L) (g := R') ?_
    intro p₀ q₀ x p₁ q₁
    let z : H.obj X := returnOuterMk k R S P Q X p₀
      (TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q X) P
        (TensorProduct.Balanced.mk k R Q X q₀ x) p₁) q₁
    have hLeft := abstractCompositionAdditive_apply
      (returnCompositeMap k R S P Q f) (returnHom k R S P Q u hu Y) z
    have hRight := abstractCompositionAdditive_apply
      (returnHom k R S P Q u hu X) f z
    have hPoint := congrFun (congrFun (congrFun (congrFun (congrFun
      (returnNaturalityValue_eq.{u, r, s, p, q, v} k R S P Q u hu
        (X := X) (Y := Y) f) p₀) q₀) x) p₁) q₁
    exact hLeft.trans (hPoint.trans hRight.symm)
  exact ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective hAdd)

/-- Let 𝒞,𝒟 be arbitrary categories with independent object and morphism universes, F,G:𝒞→𝒟
functors, O:𝒞→Ob(𝒟) an object assignment, e_Z:F(Z)≅O(Z), and a_Z:O(Z)≅G(Z). Assume for every
f:X→Y that (e_X.inv≫F(f)≫e_Y.hom)≫a_Y.hom=a_X.hom≫G(f). The transported functor F_O, with these
objects and transported maps, is naturally isomorphic to G with components a_Z. -/
def abstractViewComponents {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F G : 𝒞 ⥤ 𝒟) (obj : 𝒞 → 𝒟) (e : ∀ Z, F.obj Z ≅ obj Z)
    (app : ∀ Z, obj Z ≅ G.obj Z)
    (naturality : ∀ {X Y : 𝒞} (f : X ⟶ Y),
      ((e X).inv ≫ F.map f ≫ (e Y).hom) ≫ (app Y).hom =
        (app X).hom ≫ G.map f) :
    F.copyObj obj e ≅ G :=
  NatIso.ofComponents (F := F.copyObj obj e) (G := G) app
    (fun {X Y} f => by
      have hMap : (F.copyObj obj e).map f =
          (e X).inv ≫ F.map f ≫ (e Y).hom := rfl
      exact (congrArg (fun g : obj X ⟶ obj Y => g ≫ (app Y).hom) hMap).trans
        (naturality f))

include u hu in
private theorem returnObjectIso_hom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    (returnObjectIso.{u, r, s, p, q, v} k R S P Q u hu X).hom =
      returnHom.{u, r, s, p, q, v} k R S P Q u hu X := rfl

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). Put
D_X=G(FX) and let H_D be GF transported to these object presentations. The isomorphisms D_X≅X
with forward maps r_X given by coordinate comparison, α-contraction, and reconstruction form a
natural isomorphism H_D≅Id on ModuleCat_W(E_R^k). Its naturality is H_D(f)≫r_Y=r_X≫f. -/
def returnTypedNatIso :
    returnCompositeViewFunctor k R S P Q ≅
      𝟭 (ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) := by
  let H : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    (tensorFunctor.{u, r, s, p, q, max p q v} k R S P Q) ⋙
      (tensorFunctor.{u, s, r, q, p, max p q v} k S R Q P)
  exact abstractViewComponents H
    (𝟭 (ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)))
    (returnCompositeObject.{u, r, s, p, q, v} k R S P Q)
    (returnObjectViewIso.{u, r, s, p, q, v} k R S P Q)
    (returnObjectIso.{u, r, s, p, q, v} k R S P Q u hu)
    (fun {X Y} f => by
      have hNative := returnIso_naturality.{u, r, s, p, q, v}
        k R S P Q u hu (X := X) (Y := Y) f
      change returnCompositeMap k R S P Q f ≫ returnHom k R S P Q u hu Y =
        returnHom k R S P Q u hu X ≫ f at hNative
      have hAccessor := congrArg
        (fun g : returnCompositeObject k R S P Q X ⟶ returnCompositeObject k R S P Q Y =>
          g ≫ returnHom k R S P Q u hu Y)
        (returnViewMap_eq.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f)
      have hReal := hAccessor.trans hNative
      calc
        _ = returnViewMap k R S P Q f ≫ returnHom k R S P Q u hu Y :=
          congrArg
            (fun g : returnCompositeObject k R S P Q Y ⟶ Y =>
              returnViewMap k R S P Q f ≫ g)
            (returnObjectIso_hom.{u, r, s, p, q, v} k R S P Q u hu Y)
        _ = returnHom k R S P Q u hu X ≫ f := hReal
        _ = _ := congrArg
          (fun g : returnCompositeObject k R S P Q X ⟶ X => g ≫ f)
          (returnObjectIso_hom.{u, r, s, p, q, v} k R S P Q u hu X).symm)

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). The
object comparisons κ_{α,X}:G(FX)≅X define a natural isomorphism GF≅Id on ModuleCat_W(E_R^k). It
is obtained by transporting the natural return on D_X back along the composite-object identity
comparison. -/
def returnNatIso :
    (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P) ≅
      𝟭 (ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :=
  (((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).isoCopyObj
    (returnCompositeObject k R S P Q) (returnObjectViewIso k R S P Q)).trans
      (returnTypedNatIso k R S P Q u hu)

variable
  (w : letI := TensorProduct.Balanced.leftModule k R S Q P
    letI := TensorProduct.Balanced.rightModule k R S Q P
    TensorProduct.Balanced k R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := TensorProduct.Balanced.leftModule k R S Q P
    letI := TensorProduct.Balanced.rightModule k R S Q P
    ∀ (s : S) (b : TensorProduct.Balanced k R Q P), w (s • b) = s * w b)

include u hu w hw in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). Let
β:Q⊗_R P≃S be right S-linear with β(s•b)=sβ(b). The categories ModuleCat_W(R⊗_kRᵒᵖ) and
ModuleCat_W(S⊗_kSᵒᵖ) are equivalent with functor F and inverse G. The counit is the β-return
FG≅Id; the unit is adjusted from the inverse α-return using this counit. -/
def equivalence :
    ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ≌ ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) :=
  CategoryTheory.Equivalence.mk (tensorFunctor k R S P Q) (tensorFunctor k S R Q P)
    (returnNatIso k R S P Q u hu).symm (returnNatIso k S R Q P w hw)

@[simp]
theorem equivalence_functor : (equivalence k R S P Q u hu w hw).functor =
    tensorFunctor k R S P Q := rfl

@[simp]
theorem equivalence_inverse : (equivalence k R S P Q u hu w hw).inverse =
    tensorFunctor k S R Q P := rfl

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). Let
β:Q⊗_R P≃S be right S-linear with β(s•b)=sβ(b). The equivalence counit FG≅Id on
ModuleCat_W(S⊗_kSᵒᵖ) equals κ_β. Its component at Y contracts the two Q⊗_R P pairs and applies
their S-enveloping scalar to the given coefficient y. -/
theorem equivalence_counitIso : (equivalence k R S P Q u hu w hw).counitIso =
    returnNatIso k S R Q P w hw := rfl

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). Let
β:Q⊗_R P≃S be right S-linear with β(s•b)=sβ(b). Let κ_α,κ_β be the two tensor-return
contractions. Put η⁰_X=κ_{α,X}⁻¹ and ε_Y=κ_{β,Y}. The chosen unit component is
η_X=η⁰_X≫G(ε_{FX}⁻¹)≫GF((η⁰_X)⁻¹):X→G(FX). This is the unit determined by adjointifying those
two natural return isomorphisms. -/
theorem equivalence_unitIso : (equivalence k R S P Q u hu w hw).unitIso =
    Equivalence.adjointifyη (returnNatIso k R S P Q u hu).symm
      (returnNatIso k S R Q P w hw) := rfl

-- keeps the actual equivalence counit formula for rw; functor-object and quotient getters
-- simplify its input
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Put W=max(p,q,v) and E_R^k=R⊗_kRᵒᵖ. At height W, write F(X)=(Q⊗_R
X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). Let
β:Q⊗_R P≃S be right S-linear with β(s•b)=sβ(b). For Y∈ModuleCat_W(S⊗_kSᵒᵖ), the counit sends
(q₀⊗((p₀⊗y)⊗q₁))⊗p₁ to (β(q₀⊗p₀)⊗_k op(β(q₁⊗p₁)))•_Y y. The value uses the given S-enveloping
action and all four ordered outer coefficients. -/


@[simp, nolint simpNF]
theorem equivalence_counitIso_mk (Y : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ))
    (q₀ : Q) (p₀ : P) (y : Y) (q₁ : Q) (p₁ : P) :
    letI := ModuleCat.Bimodule.Over.groundModule k S Y
    letI := ModuleCat.Bimodule.Over.leftModule k S Y
    letI := ModuleCat.Bimodule.Over.rightModule k S Y
    letI := ModuleCat.Bimodule.Over.leftTower k S Y
    letI := ModuleCat.Bimodule.Over.rightTower k S Y
    letI := ModuleCat.Bimodule.Over.commute k S Y
    letI := TensorProduct.Balanced.rightModule k S S P Y
    ((equivalence k R S P Q u hu w hw).counitIso.hom.app Y).hom
        (returnOuterMk k S R Q P Y q₀
          (TensorProduct.Balanced.mk k S (TensorProduct.Balanced k S P Y) Q
              (TensorProduct.Balanced.mk k S P Y p₀ y) q₁) p₁) =
      (w (TensorProduct.Balanced.mk k R Q P q₀ p₀) ⊗ₜ[k] op
          (w (TensorProduct.Balanced.mk k R Q P q₁ p₁))) • y :=
  returnIso_mk k S R Q P w hw Y q₀ p₀ y q₁ p₁

end ModuleCat.Bimodule.Over.Morita
