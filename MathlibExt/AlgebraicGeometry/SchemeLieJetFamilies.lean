/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineGroupLieModels
public import MathlibExt.AlgebraicGeometry.RegularCentralizerAffineModels
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Scheme-valued Lie jets and the actual adjoint action

Lie jets are actual maps from the dual-number scheme to the actual
group, reducing to its identity. Their coefficient on every coordinate
function is the native tensor extension of the identity derivation.
The adjoint action is normalized by conjugation of these actual jets on
every coefficient algebra. These are source-integration data, with
constructors deferred separately; no unrelated representation is called
the adjoint action.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections0.5 and1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.SchemeLieJetFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open RegularCentralizerAffineModels
open scoped TensorProduct

variable {k : Type} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  (V : Type) [LieRing V] [LieAlgebra k V] [FiniteDimensional k V]
  (L : AffineGroupLieModels.LieModel G V)

def affine (A : CommAlgCat.{0} k) : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap k A)

def doubled (A : CommAlgCat.{0} k) : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap A (TrivSqZeroExt A A) ≫ Spec.algebraMap k A)

def projection (A : CommAlgCat.{0} k) : doubled A ⟶ affine A :=
  Over.homMk (Spec.algebraMap A (TrivSqZeroExt A A)) rfl

def squareMap {A B : CommAlgCat.{0} k} (u : A ⟶ B) :
    TrivSqZeroExt A A →ₐ[k] TrivSqZeroExt B B where
  toFun x := ⟨u.hom x.fst, u.hom x.snd⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp [map_add, map_mul]
  commutes' x := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', u.hom.commutes]

def affineMap {A B : CommAlgCat.{0} k} (u : A ⟶ B) : affine B ⟶ affine A :=
  Over.homMk (Spec.map (CommRingCat.ofHom u.hom.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom u.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A)) =
        Spec.map (CommRingCat.ofHom (algebraMap k B))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact u.hom.commutes x)

def changeLie {A B : CommAlgCat.{0} k} (u : A ⟶ B) : LieAt V A →ₗ[k] LieAt V B :=
  TensorProduct.map u.hom.toLinearMap (LinearMap.id : V →ₗ[k] V)

def Jets (A : CommAlgCat.{0} k) :=
  {f : L.coordinate →ₐ[k] TrivSqZeroExt A A //
    ∀ x : L.coordinate, (f x).fst = algebraMap k A (L.augmentation x)}

structure TangentFamilies where
  coefficients : ∀ (A : CommAlgCat.{0} k) (_f : L.coordinate), LieAt V A →ₗ[A] A
  pure : letI : Algebra L.coordinate k := L.augmentation.toRingHom.toAlgebra
    ∀ (A : CommAlgCat.{0} k) (a : A) (v : V) (f : L.coordinate),
      coefficients A f (a ⊗ₜ[k] v) = a * algebraMap k A (L.tangent v f)
  jets : ∀ A : CommAlgCat.{0} k, LieAt V A ≃ Jets G V L A
  normalized : ∀ (A : CommAlgCat.{0} k) (v : LieAt V A) (f : L.coordinate),
    ((jets A v).val f).snd = coefficients A f v
  naturality : ∀ {A B : CommAlgCat.{0} k} (u : A ⟶ B) (v : LieAt V A),
    (jets B (changeLie V u v)).val = (squareMap u).comp (jets A v).val

def jetPoint (J : TangentFamilies G V L) (A : CommAlgCat.{0} k) (v : LieAt V A) :
    doubled A ⟶ G :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (J.jets A v).val.toRingHom) ≫ L.affine.hom.left) (by
      change (Spec.map (CommRingCat.ofHom (J.jets A v).val.toRingHom) ≫
        L.affine.hom.left) ≫ G.hom =
          Spec.algebraMap A (TrivSqZeroExt A A) ≫ Spec.algebraMap k A
      rw [Category.assoc, Over.w L.affine.hom]
      change Spec.map (CommRingCat.ofHom (J.jets A v).val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k L.coordinate)) =
          Spec.map (CommRingCat.ofHom (algebraMap A (TrivSqZeroExt A A))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap k A))
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp [TrivSqZeroExt.algebraMap_eq_inl'])

def multiply {X : Over (Spec (.of k))} (f g : X ⟶ G) : X ⟶ G :=
  CartesianMonoidalCategory.lift f g ≫ μ[G]

def conjugate {X : Over (Spec (.of k))} (g f : X ⟶ G) : X ⟶ G :=
  multiply G (multiply G g f) (g ≫ ι[G])

structure AdjointFamilies (J : TangentFamilies G V L) where
  adjoint : ∀ A : CommAlgCat.{0} k, (affine A ⟶ G) → (LieAt V A ≃ₗ[A] LieAt V A)
  conjugation : ∀ (A : CommAlgCat.{0} k) (g : affine A ⟶ G) (v : LieAt V A),
    jetPoint G V L J A (adjoint A g v) =
      conjugate G (projection A ≫ g) (jetPoint G V L J A v)
  identity : ∀ (A : CommAlgCat.{0} k) (v : LieAt V A),
    adjoint A (toUnit (affine A) ≫ η[G]) v = v
  multiplication : ∀ (A : CommAlgCat.{0} k) (g h : affine A ⟶ G) (v : LieAt V A),
    adjoint A (multiply G g h) v = adjoint A g (adjoint A h v)
  bracket : ∀ (A : CommAlgCat.{0} k) (g : affine A ⟶ G) (v w : LieAt V A),
    adjoint A g ⁅v, w⁆ = ⁅adjoint A g v, adjoint A g w⁆
  naturality : ∀ {A B : CommAlgCat.{0} k} (u : A ⟶ B)
      (g : affine A ⟶ G) (v : LieAt V A),
    adjoint B (affineMap u ≫ g) (changeLie V u v) = changeLie V u (adjoint A g v)

end MathlibExt.AlgebraicGeometry.SchemeLieJetFamilies
