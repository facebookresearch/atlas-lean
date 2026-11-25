/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ExpansionParameterModels
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import MathlibExt.AlgebraicGeometry.LinearizedLineBundles

/-!
# Actual first-order torus points and action jets

The i-th torus generator is the actual unit1 plus epsilon in coordinate i,
and1 in the other coordinates, on Spec(B plus epsilon B). A target action
jet is an actual etale lift of that scheme action, with reduction identity.
Its function derivative is the literal epsilon coefficient of that ring map.
Source: Jun Li arXiv:math/0009097v1, torus actions in Sections1 and4;
ordinary Lie differentiation of the actual multiplicative group action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ExpansionParameterModels

def unit (B : Type) [CommRing B] (v : B) : (TrivSqZeroExt B B)ˣ where
  val := TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr v
  inv := TrivSqZeroExt.inl 1 - TrivSqZeroExt.inr v
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

variable {k : Type} [Field k] {m : ℕ} (H : TorusTheory k m)
  (B : Type) [CommRing B] [Algebra k B]

def doubled : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap B (TrivSqZeroExt B B) ≫ Spec.algebraMap k B)

def projection : doubled B ⟶ Over.mk (Spec.algebraMap k B) :=
  Over.homMk (Spec.algebraMap B (TrivSqZeroExt B B)) rfl

def point (i : Fin m) : doubled B ⟶ torusScheme k m :=
  (H.units (doubled B)).symm
    (fun j => Units.map (Scheme.ΓSpecIso (.of (TrivSqZeroExt B B))).inv.hom.toMonoidHom
      (unit B (if j = i then 1 else 0)))

variable (W : Over (Spec (.of k))) (action : letI := H.group; ModObj (torusScheme k m) W)
  (a : Over.mk (Spec.algebraMap k B) ⟶ W)

def actionJet (i : Fin m) : doubled B ⟶ W :=
  letI := H.group
  letI := action
  CartesianMonoidalCategory.lift (point H B i) (projection B ≫ a) ≫ γ[torusScheme k m,W]

structure EtaleJet (i : Fin m) where
  map : B →+* TrivSqZeroExt B B
  reduction : ∀ x, (map x).fst = x
  geometric : Spec.map (CommRingCat.ofHom map) ≫ a.left = (actionJet H B W action a i).left

def functionDerivative {i : Fin m} (J : EtaleJet H B W action a i) (x : B) : B := (J.map x).snd

end MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints
