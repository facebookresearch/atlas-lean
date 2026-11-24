/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ExpandedTargetChainGeometry
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Actual expansion parameters and scaling tori

The parameter space is the native product of m affine lines. The scaling
torus is Spec of the actual coordinate polynomial ring with the product
of its coordinate variables inverted. Scheme-valued units are normalized
on these coordinates, their actual products, and native base restriction.
Source: Jun Li arXiv:math/0009097v1, Sections 1.2 and4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ExpansionParameterModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open scoped BigOperators

variable (k : Type) [Field k]

def affineLine : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))

def affineCoordinate : Γ((affineLine k).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X

def zeroPoint : 𝟙_ (Over (Spec (.of k))) ⟶ affineLine k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))) (by
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = 𝟙 _
    rw [← Spec.map_comp]
    rw [show CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom 0) = 𝟙 (CommRingCat.of k) by ext x; simp]
    exact Spec.map_id _)

def ParameterSpace : ℕ → Over (Spec (.of k))
  | 0 => 𝟙_ (Over (Spec (.of k)))
  | m + 1 => prod (ParameterSpace m) (affineLine k)

def origin : ∀ m : ℕ, 𝟙_ (Over (Spec (.of k))) ⟶ ParameterSpace k m
  | 0 => 𝟙 _
  | m + 1 => prod.lift (origin m) (zeroPoint k)

def lastCoordinate (m : ℕ) : Γ((ParameterSpace k (m + 1)).left, ⊤) :=
  (prod.snd : ParameterSpace k (m + 1) ⟶ affineLine k).left.appTop.hom (affineCoordinate k)

def parameterProjection : ∀ m : ℕ, Fin m → (ParameterSpace k m ⟶ affineLine k)
  | 0, i => Fin.elim0 i
  | m + 1, i => Fin.lastCases
      (prod.snd : ParameterSpace k (m + 1) ⟶ affineLine k)
      (fun j => (prod.fst : ParameterSpace k (m + 1) ⟶ ParameterSpace k m) ≫ parameterProjection m j) i

def parameterCoordinate (m : ℕ) (i : Fin m) : Γ((ParameterSpace k m).left, ⊤) :=
  (parameterProjection k m i).left.appTop.hom (affineCoordinate k)

def lastParameterOpen (m : ℕ) : Over (Spec (.of k)) :=
  Over.mk (((ParameterSpace k (m + 1)).left.basicOpen (lastCoordinate k m)).ι ≫
    (ParameterSpace k (m + 1)).hom)

def lastOpenInclusion (m : ℕ) : lastParameterOpen k m ⟶ ParameterSpace k (m + 1) :=
  Over.homMk ((ParameterSpace k (m + 1)).left.basicOpen (lastCoordinate k m)).ι rfl

abbrev TorusPolynomial (m : ℕ) := MvPolynomial (Fin m) k

def torusDenominator (m : ℕ) : TorusPolynomial k m := ∏ i : Fin m, MvPolynomial.X i

abbrev TorusRing (m : ℕ) := Localization.Away (torusDenominator k m)

def torusScheme (m : ℕ) : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (TorusRing k m))))

def torusCoordinate (m : ℕ) (i : Fin m) : Γ((torusScheme k m).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (TorusRing k m))).inv.hom
    (algebraMap (TorusPolynomial k m) (TorusRing k m) (MvPolynomial.X i))

structure TorusTheory (m : ℕ) where
  [group : GrpObj (torusScheme k m)]
  units : ∀ T : Over (Spec (.of k)), (T ⟶ torusScheme k m) ≃ (Fin m → Γ(T.left, ⊤)ˣ)
  coordinates : ∀ (T : Over (Spec (.of k))) (f : T ⟶ torusScheme k m) (i : Fin m),
    f.left.appTop.hom (torusCoordinate k m i) = (units T f i : Γ(T.left, ⊤))
  identity : ∀ T, units T (toUnit T ≫ η[torusScheme k m]) = fun _ => 1
  multiply : ∀ (T : Over (Spec (.of k))) (f g : T ⟶ torusScheme k m),
    units T (CartesianMonoidalCategory.lift f g ≫ μ[torusScheme k m]) = units T f * units T g
  naturality : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (g : U ⟶ torusScheme k m),
    units T (f ≫ g) = fun i => Units.map f.left.appTop.hom (units U g i)

end MathlibExt.AlgebraicGeometry.ExpansionParameterModels
