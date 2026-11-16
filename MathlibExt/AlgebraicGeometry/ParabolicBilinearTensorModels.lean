/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ParabolicSheafCategories
public import MathlibExt.AlgebraicGeometry.RootWeightEvaluations
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Native balanced bilinear tensors and the DF parabolic unit

Tensor bilinear maps use actual scheme-module tensors, every labelled
weight arrow, all group periods of A and every étale restriction. The
balance moves the actual line L_a between the two arguments through the
native symmetry and associator. A tensor object is characterized by the
universal property of exactly these concrete bilinear maps in the actual
parabolic category.

The unit is characterized by the actual colimit of the groupified DF line
functor along A^wt → B^wt, with its weight and étale arrow formulas fixed
on every colimit leg. Neither operator is defined using a presumed
root/parabolic equivalence.

Reference: Borne–Vistoli arXiv:1001.0466v2, Definitions5.6/5.8,
Section5.3 and Theorem6.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ParabolicBilinearTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open DeligneFaltingsCategories DeligneFaltingsSheaves ParabolicSheafCategories RootWeightEvaluations
open CoherentCurveLinearSeries AlgebraicLineBundleFamilies LineBundleTaskContracts
open NativeTensorComparisons ModuleTensorPullbackSections

universe u

def weightProduct {Q : CommMonCat.{u}} (v w : Weight Q) : Weight Q := ⟨v.value * w.value⟩

def weightProductMap {Q : CommMonCat.{u}} {v v' w w' : Weight Q}
    (a : v ⟶ v') (b : w ⟶ w') : weightProduct v w ⟶ weightProduct v' w' :=
  ⟨a.label * b.label, by
    change Algebra.GrothendieckGroup.of (a.label * b.label) * (v.value * w.value) = v'.value * w'.value
    rw [map_mul]
    calc
      (Algebra.GrothendieckGroup.of a.label * Algebra.GrothendieckGroup.of b.label) *
          (v.value * w.value) =
        (Algebra.GrothendieckGroup.of a.label * v.value) *
          (Algebra.GrothendieckGroup.of b.label * w.value) := by ac_rfl
      _ = v'.value * w'.value := by rw [a.equation, b.equation]⟩

theorem product_leftShift {P Q : CommMonCat.{u}} (j : P →* Q) (p : Groupification P)
    (v w : Weight Q) : weightProduct (shift j p v) w = shift j p (weightProduct v w) := by
  apply Weight.ext
  exact mul_assoc _ _ _

theorem product_balance {P Q : CommMonCat.{u}} (j : P →* Q) (p : Groupification P)
    (v w : Weight Q) : weightProduct v (shift j p w) = weightProduct (shift j p v) w := by
  apply Weight.ext
  change v.value * (groupMap j p * w.value) = (groupMap j p * v.value) * w.value
  ac_rfl

theorem product_restriction {P Q : CommMonCat.{u}} (f : P →* Q) (v w : Weight P) :
    weightProduct ((weightMap f).obj v) ((weightMap f).obj w) = (weightMap f).obj (weightProduct v w) := by
  apply Weight.ext
  exact (map_mul (groupMap f) v.value w.value).symm

/-- The balancing arrow is computed from the source's actual period
isomorphisms, native line symmetry and native module associator. -/
def balanceArrow {Y : Scheme.{u}} {P Q : CommMonCat.{u}} {D : DeligneFaltingsChart Y P}
    {G : GroupifiedChart D} {j : P →* Q} (E F : LocalParabolic G j)
    (p : Groupification P) (v w : Weight Q) :
    moduleTensor Y (E.functor.obj (shift j p v)) (F.functor.obj w) ⟶
      moduleTensor Y (E.functor.obj v) (F.functor.obj (shift j p w)) :=
  tensorMap (E.periodic p v).hom (𝟙 (F.functor.obj w)) ≫
    tensorMap (tensorSwap Y (G.line p) (E.functor.obj v)).hom (𝟙 (F.functor.obj w)) ≫
    (tensorAssociator Y (E.functor.obj v) (G.line p) (F.functor.obj w)).hom ≫
    tensorMap (𝟙 (E.functor.obj v)) (F.periodic p w).inv

variable {X : Scheme.{u}} {A B : MonoidSheaf X} {D : Structure A}
  (G : GroupifiedDF D) (j : A ⟶ B)

/-- Concrete bilinear maps in the existing global parabolic category.
Both source periods and all actual étale pullbacks are part of the type. -/
structure Bilinear (E F H : Parabolic G j) where
  map : ∀ (U : X.Etale) (v w : Weight (B.obj.obj (op U))),
    moduleTensor U.left ((E.localObject U).functor.obj v) ((F.localObject U).functor.obj w) ⟶
      (H.localObject U).functor.obj (weightProduct v w)
  weight_naturality : ∀ (U : X.Etale) {v v' w w' : Weight (B.obj.obj (op U))}
    (a : v ⟶ v') (b : w ⟶ w'),
    tensorMap ((E.localObject U).functor.map a) ((F.localObject U).functor.map b) ≫ map U v' w' =
      map U v w ≫ (H.localObject U).functor.map (weightProductMap a b)
  period : ∀ (U : X.Etale) (p : Groupification (A.obj.obj (op U)))
    (v w : Weight (B.obj.obj (op U))),
    map U (shift (j.hom.app (op U)).hom p v) w ≫
      eqToHom (congrArg (H.localObject U).functor.obj
        (product_leftShift (j.hom.app (op U)).hom p v w)) ≫
      ((H.localObject U).periodic p (weightProduct v w)).hom =
    tensorMap ((E.localObject U).periodic p v).hom (𝟙 ((F.localObject U).functor.obj w)) ≫
      (tensorAssociator U.left ((G.chart U).line p) ((E.localObject U).functor.obj v)
        ((F.localObject U).functor.obj w)).hom ≫
      tensorMap (𝟙 ((G.chart U).line p)) (map U v w)
  balance : ∀ (U : X.Etale) (p : Groupification (A.obj.obj (op U)))
    (v w : Weight (B.obj.obj (op U))),
    map U (shift (j.hom.app (op U)).hom p v) w =
      balanceArrow (E.localObject U) (F.localObject U) p v w ≫
      map U v (shift (j.hom.app (op U)).hom p w) ≫
      eqToHom (congrArg (H.localObject U).functor.obj
        (product_balance (j.hom.app (op U)).hom p v w))
  restriction : ∀ {U V : X.Etale} (f : V ⟶ U) (v w : Weight (B.obj.obj (op U))),
    (Scheme.Modules.pullback f.left).map (map U v w) ≫ (H.reindex f).hom.app (weightProduct v w) =
      ((D.tensorPullback f).comparison ((E.localObject U).functor.obj v)
        ((F.localObject U).functor.obj w)).hom ≫
      tensorMap ((E.reindex f).hom.app v) ((F.reindex f).hom.app w) ≫
      map V ((weightMap (B.obj.map f.op).hom).obj v) ((weightMap (B.obj.map f.op).hom).obj w) ≫
      eqToHom (congrArg (H.localObject V).functor.obj (product_restriction (B.obj.map f.op).hom v w))

/-- A tensor is universal for these actual balanced bilinear maps. Its
action on coefficient arrows is fixed on every universal component. -/
structure TensorModel where
  functor : Parabolic G j ⥤ Parabolic G j ⥤ Parabolic G j
  universal : ∀ E F, Bilinear G j E F ((functor.obj E).obj F)
  lift : ∀ {E F H}, Bilinear G j E F H → ((functor.obj E).obj F ⟶ H)
  factorization : ∀ {E F H} (b : Bilinear G j E F H) (U : X.Etale)
    (v w : Weight (B.obj.obj (op U))),
    (universal E F).map U v w ≫ ((lift b).localMap U).map.app (weightProduct v w) = b.map U v w
  uniqueness : ∀ {E F H} (a b : (functor.obj E).obj F ⟶ H),
    (∀ (U : X.Etale) (v w : Weight (B.obj.obj (op U))),
      (universal E F).map U v w ≫ (a.localMap U).map.app (weightProduct v w) =
        (universal E F).map U v w ≫ (b.localMap U).map.app (weightProduct v w)) → a = b
  coefficient_naturality : ∀ {E E' F F'} (a : E ⟶ E') (b : F ⟶ F')
    (U : X.Etale) (v w : Weight (B.obj.obj (op U))),
    (universal E F).map U v w ≫
      ((((functor.map a).app F) ≫ (functor.obj E').map b).localMap U).map.app (weightProduct v w) =
    tensorMap ((a.localMap U).map.app v) ((b.localMap U).map.app w) ≫ (universal E' F').map U v w

variable (K : ∀ U : X.Etale, LineFunctorLaws (G.chart U))

def unitDiagram (U : X.Etale) (w : Weight (B.obj.obj (op U))) :
    CostructuredArrow (weightMap (j.hom.app (op U)).hom) w ⥤ U.left.Modules :=
  CostructuredArrow.proj _ _ ⋙ lineFunctor (K U)

/-- The source unit has its literal DF-weight left-Kan colimit and every
weight/étale leg normalization. It is independent of the root equivalence. -/
structure UnitModel where
  object : Parabolic G j
  cocone : ∀ (U : X.Etale) (w : Weight (B.obj.obj (op U))), Cocone (unitDiagram G j K U w)
  point : ∀ (U : X.Etale) (w : Weight (B.obj.obj (op U))),
    (cocone U w).pt = (object.localObject U).functor.obj w
  isColimit : ∀ (U : X.Etale) (w : Weight (B.obj.obj (op U))), IsColimit (cocone U w)
  weight_arrows : ∀ (U : X.Etale) {v w : Weight (B.obj.obj (op U))} (a : v ⟶ w)
    (s : CostructuredArrow (weightMap (j.hom.app (op U)).hom) v),
    (cocone U v).ι.app s ≫ eqToHom (point U v) ≫ (object.localObject U).functor.map a =
      (cocone U w).ι.app (CostructuredArrow.mk (s.hom ≫ a)) ≫ eqToHom (point U w)
  restriction : ∀ {U V : X.Etale} (f : V ⟶ U)
    (p : Weight (A.obj.obj (op U))) (w : Weight (B.obj.obj (op U)))
    (a : (weightMap (j.hom.app (op U)).hom).obj p ⟶ w)
    (a' : (weightMap (j.hom.app (op V)).hom).obj ((weightMap (A.obj.map f.op).hom).obj p) ⟶
      (weightMap (B.obj.map f.op).hom).obj w),
    a'.label = (B.obj.map f.op).hom a.label →
    (Scheme.Modules.pullback f.left).map
      ((cocone U w).ι.app (CostructuredArrow.mk a) ≫ eqToHom (point U w)) ≫ (object.reindex f).hom.app w =
      (G.reindex f p.value).hom ≫
        (cocone V ((weightMap (B.obj.map f.op).hom).obj w)).ι.app (CostructuredArrow.mk a') ≫
          eqToHom (point V ((weightMap (B.obj.map f.op).hom).obj w))

end MathlibExt.AlgebraicGeometry.ParabolicBilinearTensorModels
