/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiCechChartModules
public import MathlibExt.AlgebraicGeometry.LiMarkedCurveExtensions
public import MathlibExt.AlgebraicGeometry.AffineSquareZeroCotangentClasses

/-!
# Actual local lifted-map differences in Li's complex

Local rings are flat extensions over the actual split extension of their
etale base chart. Their kernel is the actual scalar extension of I.
The two target maps are actual ring homomorphisms, with parameter values
in that base extension. Normal logarithms are the kernel coordinates of
their actual unit ratios, including their base product at a node.
Source: Jun Li arXiv:math/0110113v1, Lemma1.12, equations1.18--1.19,
and the relative boundary modification in1.23--1.25.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiLocalLiftDifferences

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open LiAffineMapCharts LiCechChartModules AffineSquareZeroCotangentClasses
open scoped TensorProduct

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm LiMarkedCurveExtensions.oppositeTower

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
  {C X Z : Scheme.{0}} {p : C ⟶ Spec (.of A)} {q : X ⟶ Spec (.of k)} {f : C ⟶ X}
  (g : X ⟶ Z) {b m : ℕ} (J : Fin b → X.IdealSheafData) (t : Fin m → Γ(X, ⊤))
  (a : Chart p q f) (I : ModuleCat.{0} A)

def baseCoefficientObject : ModuleCat.{0} a.base := ModuleCat.of a.base (baseCoefficient a I)

structure LocalExtension where
  extension : AffineSquareZeroCotangentClasses.Extension A a.source
  coefficient : extension.coefficient ≅ ModuleCat.of a.source (sourceCoefficient a I)
  baseMap : TrivSqZeroExt a.base (baseCoefficientObject a I) →+* extension.ring
  base_scalar : ∀ r : A, baseMap (TrivSqZeroExt.inl (algebraMap A a.base r)) =
    algebraMap A extension.ring r
  base_reduction : ∀ x, extension.projection (baseMap x) = algebraMap a.base a.source x.fst
  flat : letI := baseMap.toAlgebra
    Module.Flat (TrivSqZeroExt a.base (baseCoefficientObject a I)) extension.ring
  base_coefficient : ∀ x : baseCoefficientObject a I,
    coefficient.hom (extension.kernel ⟨baseMap (TrivSqZeroExt.inr x), by
      change extension.projection (baseMap (TrivSqZeroExt.inr x)) = 0
      rw [base_reduction]
      simp⟩) = baseCoefficientMap a I x

variable (E : LocalExtension a I)

structure Pair where
  first : a.target →+* E.extension.ring
  second : a.target →+* E.extension.ring
  first_reduction : ∀ x, E.extension.projection (first x) = algebraMap a.target a.source x
  second_reduction : ∀ x, E.extension.projection (second x) = algebraMap a.target a.source x
  first_scalar : ∀ r : k, first (algebraMap k a.target r) =
    algebraMap A E.extension.ring (algebraMap k A r)
  second_scalar : ∀ r : k, second (algebraMap k a.target r) =
    algebraMap A E.extension.ring (algebraMap k A r)
  first_parameter : ∀ i : Fin m, ∃ v : TrivSqZeroExt a.base (baseCoefficientObject a I),
    first (parameterValue t a i) = E.baseMap v
  second_parameter : ∀ i : Fin m, ∃ v : TrivSqZeroExt a.base (baseCoefficientObject a I),
    second (parameterValue t a i) = E.baseMap v

variable (P : Pair t a I E)

def differenceValue (x : a.target) : sourceCoefficient a I :=
  E.coefficient.hom (E.extension.kernel ⟨P.first x - P.second x, by
    change E.extension.projection (_ - _) = 0
    rw [map_sub, P.first_reduction, P.second_reduction, sub_self]⟩)

def unitValue (u : E.extension.ringˣ) (h : E.extension.projection u = 1) : sourceCoefficient a I :=
  E.coefficient.hom (E.extension.kernel ⟨(u : E.extension.ring) - 1, by
    change E.extension.projection (_ - _) = 0
    rw [map_sub, h, map_one, sub_self]⟩)

structure BoundaryRatio (z : a.target) where
  unit : E.extension.ringˣ
  reduction : E.extension.projection unit = 1
  coordinate : P.first z = P.second z * (unit : E.extension.ring)

structure NodeRatios (z : Fin 2 → a.target) where
  unit : Fin 2 → E.extension.ringˣ
  reduction : ∀ i, E.extension.projection (unit i) = 1
  coordinate : ∀ i, P.first (z i) = P.second (z i) * (unit i : E.extension.ring)
  baseUnit : (TrivSqZeroExt a.base (baseCoefficientObject a I))ˣ
  baseReduction : baseUnit.val.fst = 1
  product : (unit 0 : E.extension.ring) * (unit 1 : E.extension.ring) = E.baseMap baseUnit

def Ratios : Mode g J t a → Type
  | .ordinary _ _ _ _ => PUnit
  | .boundary _ o _ _ _ _ => BoundaryRatio (t := t) (a := a) (I := I) (E := E) (P := P) o.coordinate
  | .node o _ _ _ => NodeRatios (t := t) (a := a) (I := I) (E := E) (P := P) o.coordinate

def Normalized (o : Mode g J t a) (r : Ratios g J t a I E P o) (x : value g J t I o) : Prop :=
  (∀ s : a.target, derivative g J t I o x s = differenceValue t a I E P s) ∧
  match o, r, x with
  | .ordinary _ _ _ _, _, _ => True
  | .boundary _ z pr pt hp h, u, y =>
      boundaryLog g J t I z pr pt hp h y = unitValue a I E u.unit u.reduction
  | .node z pr pure h, u, y =>
      ∀ i : Fin 2, nodeLog g J t I z pr pure h y i = unitValue a I E (u.unit i) (u.reduction i)

end MathlibExt.AlgebraicGeometry.LiLocalLiftDifferences
