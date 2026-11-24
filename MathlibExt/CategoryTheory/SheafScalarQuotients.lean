/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Sheaf reduction and p-localization on all site objects

Commutative ring-sheaf coproducts are native tensor products over the
initial integer sheaf. Tensoring with the actual constant `Z/p` sheaf
therefore gives reduction modulo `p`; tensoring with the actual constant
`Z[1/p]` sheaf gives p-localization. The sheaf colimit retains locally
varying denominators and includes empty objects.

References: Scholze, arXiv:1205.3463v2, Definition 6.1;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Definition 5.4.
Native ring coproduct, localization and sheaf operations use Mathlib,
Apache 2.0, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.SheafScalarQuotients

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{1}]

def constantRing (A : Type) [CommRing A] : Sheaf J CommRingCat.{1} :=
  (presheafToSheaf J CommRingCat.{1}).obj
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{1} A)))

variable (p : ℕ) (R : Sheaf J CommRingCat.{1})

/-- The actual ring-sheaf quotient by p. -/
def modP : Sheaf J CommRingCat.{1} :=
  coprod R (constantRing (J := J) (ZMod p))

def modPUnit : R ⟶ modP p R := coprod.inl

theorem modP_zero (U : Cᵒᵖ) : (p : (modP p R).obj.obj U) = 0 := by
  let q : ULift.{1} (ZMod p) →+* (modP p R).obj.obj U :=
    ((coprod.inr : constantRing (J := J) (ZMod p) ⟶ modP p R).hom.app U).hom.comp
      ((toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (ULift.{1} (ZMod p))))).app U).hom
  have h : (p : ULift.{1} (ZMod p)) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self p
  have hq := congrArg q h
  rw [map_natCast, map_zero] at hq
  exact hq

abbrev IntegerPInversion := Localization.Away (p : ℤ)

/-- Actual p-localization as a ring-sheaf colimit. -/
def localizeP : Sheaf J CommRingCat.{1} :=
  coprod R (constantRing (J := J) (IntegerPInversion p))

def localizePUnit : R ⟶ localizeP p R := coprod.inl

def localizePMap {R S : Sheaf J CommRingCat.{1}} (f : R ⟶ S) :
    localizeP p R ⟶ localizeP p S :=
  coprod.desc (f ≫ localizePUnit p S) coprod.inr

end MathlibExt.CategoryTheory.SheafScalarQuotients
