/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels
public import MathlibExt.AlgebraicGeometry.GeneralMotivicBundleFrameMaps
public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Actual finite constant groups and free permutation quotients

The constant group carrier is literally Spec of the finite product of k.
Its group multiplication is normalized on the original component points,
which cover this finite split scheme. Free quotient data use the native
fppf torsor relation and an actual smooth scheme presentation.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.3. The associated
permutation bundle and cycle descent are separate source constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicFinitePermutationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory _root_.CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels GroupTorsorGeometry

variable {k : Type} [Field k] {H : Type}

/-- The coefficient ring of the actual finite split constant scheme. -/
abbrev constantRing (k H : Type) [Field k] := H → k

/-- The original constant coefficient map, without a chosen scheme carrier. -/
def constantCoefficients : k →+* constantRing k H :=
  RingHom.pi (fun _ : H => RingHom.id k)

/-- The actual constant scheme over the original field. -/
def constantScheme : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (constantCoefficients (H := H))))

/-- Each original group element is its native component-point ring evaluation. -/
def constantPoint (h : H) : Over.mk (𝟙 (Spec (.of k))) ⟶
    constantScheme (k := k) (H := H) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : H => k) h))) (by
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : H => k) h)) ≫
      Spec.map (CommRingCat.ofHom (constantCoefficients (H := H))) = 𝟙 _
    have hc : CommRingCat.ofHom (constantCoefficients (k := k) (H := H)) ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : H => k) h) = 𝟙 _ := by
      ext a
      rfl
    rw [← Spec.map_comp, hc, Spec.map_id])

/-- The original idempotent coordinate of a component of the constant scheme. -/
def componentIdempotent (h : H) : constantRing k H := by
  classical
  exact fun g => if g = h then 1 else 0

/-- Coordinates use the actual whole scheme map on global sections. -/
def componentCoordinate (T : Over (Spec (.of k)))
    (g : T ⟶ constantScheme (k := k) (H := H)) (h : H) : Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (constantRing k H))).inv ≫ g.left.appTop).hom
    (componentIdempotent (k := k) h)

variable [Group H]

/-- The source group structure is on the fixed finite split carrier. -/
class ConstantGroupGeometry where
  [group : GrpObj (constantScheme (k := k) (H := H))]
  [finite : IsFinite (constantScheme (k := k) (H := H)).hom]
  [etale : Etale (constantScheme (k := k) (H := H)).hom]
  multiplication : ∀ a b : H,
    lift (constantPoint (k := k) a) (constantPoint (k := k) b) ≫
      μ[constantScheme (k := k) (H := H)] = constantPoint (k := k) (a * b)

attribute [instance_reducible, instance] ConstantGroupGeometry.group
attribute [instance] ConstantGroupGeometry.finite
  ConstantGroupGeometry.etale

variable [C : ConstantGroupGeometry (k := k) (H := H)]

/-- A free smooth quotient uses an actual torsor and its original total scheme. -/
structure FreeQuotient where
  base : SmoothScheme k
  total : SmoothScheme k
  torsor : GroupTorsorGeometry.Torsor (constantScheme (k := k) (H := H)) base.scheme
  totalIso : total.scheme ≅ torsor.total

/-- The quotient projection is the original torsor projection. -/
def FreeQuotient.projection (P : FreeQuotient (k := k) (H := H)) :
    P.total.scheme ⟶ P.base.scheme :=
  P.totalIso.hom ≫ P.torsor.projection

/-- The actual group action is transported through the original total-space isomorphism. -/
def FreeQuotient.actPoint (P : FreeQuotient (k := k) (H := H)) (T : Over (Spec (.of k)))
    (g : T ⟶ constantScheme (k := k) (H := H)) (u : T ⟶ P.total.scheme) :
    T ⟶ P.total.scheme :=
  lift g (u ≫ P.totalIso.hom) ≫
    γ[constantScheme (k := k) (H := H), P.torsor.total] ≫ P.totalIso.inv

/-- The transported action retains the actual quotient base as a whole scheme map. -/
theorem FreeQuotient.actPoint_projection (P : FreeQuotient (k := k) (H := H))
    (T : Over (Spec (.of k))) (g : T ⟶ constantScheme (k := k) (H := H))
    (u : T ⟶ P.total.scheme) :
    P.actPoint T g u ≫ P.projection = u ≫ P.projection := by
  simp only [FreeQuotient.actPoint, FreeQuotient.projection, Category.assoc,
    Iso.inv_hom_id_assoc, P.torsor.invariant, lift_snd_assoc]

end MathlibExt.AlgebraicGeometry.MotivicFinitePermutationModels
