/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TwistedRankTwoRepresentations
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

/-!
# The actual affine twisted character quotient

The invariant ring is the equalizer of actual regular-function pullbacks
along conjugation and projection. Its complex scalar map is induced by
the structure morphism. The Betti character scheme is its actual Spec,
and its quotient map is the native map to Spec of global functions
followed by the inclusion of that invariant ring.

The construction target proves the categorical quotient property and
the source smooth-variety properties of this fixed scheme. It does not
replace coefficient-scheme points by orbits of matrices over one field.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TwistedCharacterQuotientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels TwistedRankTwoRepresentations
open CoherentCurveLinearSeries

variable [F : FrameTheory 2] [M : GL2MatrixTheory] (g : ℕ) [C : Conjugation g]

def actionMap : frameScheme 2 ⊗ representation g ⟶ representation g :=
  γ[frameScheme 2,representation g]

def projectionMap : frameScheme 2 ⊗ representation g ⟶ representation g :=
  snd (frameScheme 2) (representation g)

def actionPull : Γ((representation g).left, ⊤) →+*
    Γ((frameScheme 2 ⊗ representation g).left, ⊤) := (actionMap g).left.appTop.hom

def projectionPull : Γ((representation g).left, ⊤) →+*
    Γ((frameScheme 2 ⊗ representation g).left, ⊤) := (projectionMap g).left.appTop.hom

def invariantRing : Subring Γ((representation g).left, ⊤) where
  carrier := {a | actionPull g a = projectionPull g a}
  zero_mem' := (actionPull g).map_zero.trans (projectionPull g).map_zero.symm
  one_mem' := (actionPull g).map_one.trans (projectionPull g).map_one.symm
  add_mem' {a b} ha hb := by
    change actionPull g (a + b) = projectionPull g (a + b)
    rw [map_add, map_add, ha, hb]
  mul_mem' {a b} ha hb := by
    change actionPull g (a * b) = projectionPull g (a * b)
    rw [map_mul, map_mul, ha, hb]
  neg_mem' {a} ha := by
    change actionPull g (-a) = projectionPull g (-a)
    rw [map_neg, map_neg, ha]

theorem scalar_invariant (c : ℂ) : globalScalarMap (representation g).hom c ∈ invariantRing g := by
  have h : (actionMap g).left ≫ (representation g).hom =
      (projectionMap g).left ≫ (representation g).hom :=
    (Over.w (actionMap g)).trans (Over.w (projectionMap g)).symm
  have hs := congrArg (fun f => f.appTop.hom ((Scheme.ΓSpecIso (.of ℂ)).inv.hom c)) h
  change actionPull g (globalScalarMap (representation g).hom c) =
    projectionPull g (globalScalarMap (representation g).hom c)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    globalScalarMap, actionPull, projectionPull] using hs

def complexScalars : ℂ →+* invariantRing g where
  toFun c := ⟨globalScalarMap (representation g).hom c, scalar_invariant g c⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext (map_add _ c d)
  map_mul' c d := Subtype.ext (map_mul _ c d)

def bettiScheme : Over (Spec (.of ℂ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (complexScalars g)))

def quotientMap : representation g ⟶ bettiScheme g :=
  Over.homMk ((representation g).left.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (invariantRing g).subtype)) (by
      change ((representation g).left.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (invariantRing g).subtype)) ≫
          Spec.map (CommRingCat.ofHom (complexScalars g)) = (representation g).hom
      rw [Category.assoc, ← Spec.map_comp]
      change (representation g).left.toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (representation g).hom.appTop) =
          (representation g).hom
      rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id])

class CharacterQuotient where
  quotient : LinearizedLineBundles.CategoricalQuotient
    (frameScheme 2) (representation g) (bettiScheme g)
  normalized : quotient.quotient = quotientMap g
  representation_affine : IsIso (representation g).left.toSpecΓ
  variety : PerverseSheaves.IsComplexVariety (bettiScheme g)
  smooth : Smooth (bettiScheme g).hom

attribute [instance] CharacterQuotient.variety CharacterQuotient.smooth

end MathlibExt.AlgebraicGeometry.TwistedCharacterQuotientModels
