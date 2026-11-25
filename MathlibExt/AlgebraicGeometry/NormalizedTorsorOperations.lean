/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ContractedTorsorModels

/-!
# Point-normalized contracted torsor operations

Tensor and pullback objects reuse the actual fppf quotient and Cartesian
models. The unit is identified with the actual G times X torsor. Unit,
associativity and symmetry maps are fixed on every actual quotient point.
Pushout functors are fixed by the actual inverse-diagonal quotient maps,
including their action on all bundle arrows.

These are comparison data for the displayed operations, not arbitrary
tensor or pushout functors. Construction requests specialize them to the
actual split tori, where inversion is a group homomorphism.
Source: Stacks Project, Tags 04UR and 0CQJ; Donagi--Gaitsgory,
arXiv:math/0005132v3, Sections 4--6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NormalizedTorsorOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ContractedTorsorModels

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

structure UnitModel (X : Over S) where
  bundle : Bundle G X
  total : bundle.torsor.total ≅ G ⊗ X
  projection : total.hom ≫ snd G X = bundle.torsor.projection
  action : ∀ (U : Over S) (g : U ⟶ G) (p : U ⟶ bundle.torsor.total),
    CartesianMonoidalCategory.lift g p ≫ γ[G,bundle.torsor.total] ≫ total.hom =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.lift g (p ≫ total.hom ≫ fst G X) ≫ μ[G])
        (p ≫ total.hom ≫ snd G X)

def unitPoint {X : Over S} (M : UnitModel G X) {U : Over S} (x : U ⟶ X) :
    U ⟶ M.bundle.torsor.total :=
  CartesianMonoidalCategory.lift (toUnit U ≫ η[G]) x ≫ M.total.inv

theorem unitPoint_over {X : Over S} (M : UnitModel G X) {U : Over S} (x : U ⟶ X) :
    unitPoint G M x ≫ M.bundle.torsor.projection = x := by
  rw [unitPoint, ← M.projection]
  simp

def tensorObj (T : TensorOperations G) {X : Over S} (P Q : Bundle G X) : Bundle G X :=
  (T.tensor X).obj (P, Q)

def tensorMap (T : TensorOperations G) {X : Over S} {P Q P' Q' : Bundle G X}
    (a : P ⟶ P') (b : Q ⟶ Q') : tensorObj G T P Q ⟶ tensorObj G T P' Q' :=
  (T.tensor X).map (a, b)

def tensorIso (T : TensorOperations G) {X : Over S} {P Q P' Q' : Bundle G X}
    (a : P ≅ P') (b : Q ≅ Q') : tensorObj G T P Q ≅ tensorObj G T P' Q' :=
  (T.tensor X).mapIso {
    hom := (a.hom, b.hom)
    inv := (a.inv, b.inv)
    hom_inv_id := by ext <;> simp
    inv_hom_id := by ext <;> simp }

structure TensorCalculus where
  tensor : TensorOperations G
  baseChange : ContractedTorsorModels.Families (G := G)
  unit : ∀ X : Over S, UnitModel G X
  associator : ∀ (X : Over S) (P Q R : Bundle G X),
    tensorObj G tensor (tensorObj G tensor P Q) R ≅
      tensorObj G tensor P (tensorObj G tensor Q R)
  associator_normalized : ∀ (X : Over S) (P Q R : Bundle G X) (U : Over S)
      (p : U ⟶ P.torsor.total) (q : U ⟶ Q.torsor.total) (r : U ⟶ R.torsor.total)
      (hPQ : p ≫ P.torsor.projection = q ≫ Q.torsor.projection)
      (hQR : q ≫ Q.torsor.projection = r ≫ R.torsor.projection)
      (hL : tensorPoint (tensor.model X P Q) p q hPQ ≫
          (tensorObj G tensor P Q).torsor.projection = r ≫ R.torsor.projection)
      (hR : p ≫ P.torsor.projection = tensorPoint (tensor.model X Q R) q r hQR ≫
          (tensorObj G tensor Q R).torsor.projection),
    tensorPoint (tensor.model X (tensorObj G tensor P Q) R)
      (tensorPoint (tensor.model X P Q) p q hPQ) r hL ≫
        (associator X P Q R).hom.iso.hom =
      tensorPoint (tensor.model X P (tensorObj G tensor Q R)) p
        (tensorPoint (tensor.model X Q R) q r hQR) hR
  symmetry : ∀ (X : Over S) (P Q : Bundle G X), tensorObj G tensor P Q ≅ tensorObj G tensor Q P
  symmetry_normalized : ∀ (X : Over S) (P Q : Bundle G X) (U : Over S)
      (p : U ⟶ P.torsor.total) (q : U ⟶ Q.torsor.total)
      (h : p ≫ P.torsor.projection = q ≫ Q.torsor.projection),
    tensorPoint (tensor.model X P Q) p q h ≫ (symmetry X P Q).hom.iso.hom =
      tensorPoint (tensor.model X Q P) q p h.symm
  leftUnit : ∀ (X : Over S) (P : Bundle G X), tensorObj G tensor (unit X).bundle P ≅ P
  left_normalized : ∀ (X : Over S) (P : Bundle G X) (U : Over S)
      (p : U ⟶ P.torsor.total)
      (h : unitPoint G (unit X) (p ≫ P.torsor.projection) ≫ (unit X).bundle.torsor.projection =
        p ≫ P.torsor.projection),
    tensorPoint (tensor.model X (unit X).bundle P)
      (unitPoint G (unit X) (p ≫ P.torsor.projection)) p h ≫ (leftUnit X P).hom.iso.hom = p
  rightUnit : ∀ (X : Over S) (P : Bundle G X), tensorObj G tensor P (unit X).bundle ≅ P
  right_normalized : ∀ (X : Over S) (P : Bundle G X) (U : Over S)
      (p : U ⟶ P.torsor.total)
      (h : p ≫ P.torsor.projection = unitPoint G (unit X) (p ≫ P.torsor.projection) ≫
        (unit X).bundle.torsor.projection),
    tensorPoint (tensor.model X P (unit X).bundle) p
      (unitPoint G (unit X) (p ≫ P.torsor.projection)) h ≫ (rightUnit X P).hom.iso.hom = p
  baseTensor : ∀ {X X' : Over S} (f : X' ⟶ X) (P Q : Bundle G X),
    (baseChange.change f).obj (tensorObj G tensor P Q) ≅
      tensorObj G tensor ((baseChange.change f).obj P) ((baseChange.change f).obj Q)
  baseTensor_normalized : ∀ {X X' : Over S} (f : X' ⟶ X) (P Q : Bundle G X) (U : Over S)
      (p : U ⟶ ((baseChange.change f).obj P).torsor.total)
      (q : U ⟶ ((baseChange.change f).obj Q).torsor.total)
      (h : p ≫ ((baseChange.change f).obj P).torsor.projection =
        q ≫ ((baseChange.change f).obj Q).torsor.projection)
      (h' : (p ≫ original (baseChange.pullback f P)) ≫ P.torsor.projection =
        (q ≫ original (baseChange.pullback f Q)) ≫ Q.torsor.projection),
    tensorPoint (tensor.model X' ((baseChange.change f).obj P)
      ((baseChange.change f).obj Q)) p q h ≫
      (baseTensor f P Q).inv.iso.hom ≫ original (baseChange.pullback f (tensorObj G tensor P Q)) =
        tensorPoint (tensor.model X P Q) (p ≫ original (baseChange.pullback f P))
          (q ≫ original (baseChange.pullback f Q)) h'
  baseUnit : ∀ {X X' : Over S} (f : X' ⟶ X),
    (baseChange.change f).obj (unit X).bundle ≅ (unit X').bundle
  baseUnit_normalized : ∀ {X X' : Over S} (f : X' ⟶ X),
    (baseUnit f).hom.iso.hom ≫ (unit X').total.hom =
      CartesianMonoidalCategory.lift
        (original (baseChange.pullback f (unit X).bundle) ≫ (unit X).total.hom ≫ fst G X)
        ((baseChange.change f).obj (unit X).bundle).torsor.projection

variable (H : Over S) [GrpObj H] (δ : G ⟶ H) [IsMonHom δ]

structure PushoutFunctor where
  map : ∀ X : Over S, Bundle G X ⥤ Bundle H X
  diagram : ∀ (X : Over S) (P : Bundle G X), Pushout H δ P ((map X).obj P)
  arrows : ∀ (X : Over S) {P Q : Bundle G X} (a : P ⟶ Q),
    tensorHom a.iso.hom (𝟙 H) ≫ (diagram X Q).quotient =
      (diagram X P).quotient ≫ ((map X).map a).iso.hom

def pushoutObj (D : PushoutFunctor G H δ) {X : Over S} (P : Bundle G X) : Bundle H X :=
  (D.map X).obj P

end MathlibExt.AlgebraicGeometry.NormalizedTorsorOperations
