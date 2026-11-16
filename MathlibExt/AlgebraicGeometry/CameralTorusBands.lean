/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ExpansionParameterModels
public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Actual cameral covers and the ramification torus band

Sections are actual W-equivariant maps from the pulled cameral scheme
to the torus. The root character is restricted to the actual scheme
equalizer of its reflection and the identity, where it equals the unit
map +1. All coefficient schemes, including nonreduced schemes, remain
in the test category.

The local cameral model uses actual etale pullbacks of the specified
Chevalley morphism. Its geometric source is bound separately to the
actual torus Lie algebra and invariant algebra.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections1--4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CameralTorusBands

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.MonObj _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open ExpansionParameterModels
open scoped BigOperators

variable {k : Type} [Field k] {r : ℕ}
  (T : TorusTheory k r) (Gm : TorusTheory k 1)
  (W : Type) [Group W] [Fintype W]

structure Roots where
  count : ℕ
  character : Fin count → (torusScheme k r ⟶ torusScheme k 1)
  exponent : Fin count → Fin r → ℤ
  coroot : Fin count → (torusScheme k 1 ⟶ torusScheme k r)
  coexponent : Fin count → Fin r → ℤ
  reflection : Fin count → W
  reflection_square : ∀ i, reflection i * reflection i = 1
  action : W →* Aut (torusScheme k r)
  action_unit : letI := T.group;
    ∀ (X : Over (Spec (.of k))) (w : W),
      T.units X (toUnit X ≫ η[torusScheme k r] ≫ (action w).asIso.hom) = fun _ => 1
  action_multiply : letI := T.group;
    ∀ (X : Over (Spec (.of k))) (w : W) (f g : X ⟶ torusScheme k r),
      T.units X (CartesianMonoidalCategory.lift f g ≫ μ[torusScheme k r] ≫ (action w).asIso.hom) =
        T.units X (f ≫ (action w).asIso.hom) * T.units X (g ≫ (action w).asIso.hom)
  character_values : ∀ (X : Over (Spec (.of k))) (f : X ⟶ torusScheme k r) (i : Fin count),
    Gm.units X (f ≫ character i) 0 = ∏ j : Fin r, (T.units X f j) ^ exponent i j
  coroot_values : ∀ (X : Over (Spec (.of k))) (f : X ⟶ torusScheme k 1) (i : Fin count) (j : Fin r),
    T.units X (f ≫ coroot i) j = (Gm.units X f 0) ^ coexponent i j
  reflected_values : ∀ (X : Over (Spec (.of k))) (f : X ⟶ torusScheme k r) (i : Fin count),
    Gm.units X (f ≫ (action (reflection i)).asIso.hom ≫ character i) 0 =
      (Gm.units X (f ≫ character i) 0)⁻¹

structure WCover (X : Over (Spec (.of k))) where
  scheme : Over X.left
  [finite : IsFinite scheme.hom]
  [flat : Flat scheme.hom]
  action : W →* Aut scheme
  regular : ∀ x : X.left, ∃ U : X.left.affineOpens, x ∈ U.val ∧
    letI : Algebra Γ(X.left, U.val) Γ(scheme.left, scheme.hom ⁻¹ᵁ U.val) :=
      (scheme.hom.appLE U.val (scheme.hom ⁻¹ᵁ U.val) le_rfl).hom.toAlgebra
    ∃ basis : Γ(scheme.left, scheme.hom ⁻¹ᵁ U.val) ≃ₗ[Γ(X.left, U.val)] (W → Γ(X.left, U.val)),
      ∀ (w i : W) (s : Γ(scheme.left, scheme.hom ⁻¹ᵁ U.val)),
        basis (((action w).asIso.inv.left.appLE (scheme.hom ⁻¹ᵁ U.val) (scheme.hom ⁻¹ᵁ U.val) (by
          intro y hy
          change scheme.hom ((action w).asIso.inv.left y) ∈ U.val
          rw [← Scheme.Hom.comp_apply, Over.w (action w).asIso.inv]
          exact hy)).hom s) i =
          basis s (w⁻¹ * i)

attribute [instance] WCover.finite WCover.flat

@[implicit_reducible] def pulled {X : Over (Spec (.of k))} (C : WCover W X)
    (U : Over X.left) : Over (Spec (.of k)) :=
  Over.mk (pullback.snd C.scheme.hom U.hom ≫ U.hom ≫ X.hom)

def pulledAction {X : Over (Spec (.of k))} (C : WCover W X) (U : Over X.left) (w : W) :
    (pulled W C U).left ≅ (pulled W C U).left :=
  (Over.forget U.left).mapIso ((Over.pullback U.hom).mapIso (C.action w).asIso)

def fixed {X : Over (Spec (.of k))} (C : WCover W X) (U : Over X.left) (w : W) :
    Over (Spec (.of k)) :=
  Over.mk (equalizer.ι (pulledAction W C U w).hom (𝟙 (pulled W C U).left) ≫ (pulled W C U).hom)

def fixedInclusion {X : Over (Spec (.of k))} (C : WCover W X) (U : Over X.left) (w : W) :
    fixed W C U w ⟶ pulled W C U :=
  Over.homMk (equalizer.ι (pulledAction W C U w).hom (𝟙 (pulled W C U).left)) rfl

variable (R : Roots T Gm W)

def Equivariant {X : Over (Spec (.of k))} (C : WCover W X) (U : Over X.left)
    (f : pulled W C U ⟶ torusScheme k r) : Prop :=
  ∀ w : W, (pulledAction W C U w).hom ≫ f.left = f.left ≫ (R.action w).asIso.hom.left

def RamifiedUnit {X : Over (Spec (.of k))} (C : WCover W X) (U : Over X.left)
    (f : pulled W C U ⟶ torusScheme k r) : Prop :=
  letI := Gm.group
  ∀ i : Fin R.count,
    fixedInclusion W C U (R.reflection i) ≫ f ≫ R.character i =
      toUnit (fixed W C U (R.reflection i)) ≫ η[torusScheme k 1]

def Sections {X : Over (Spec (.of k))} (C : WCover W X) (U : Over X.left) :=
  {f : pulled W C U ⟶ torusScheme k r // Equivariant T Gm W R C U f ∧ RamifiedUnit T Gm W R C U f}

structure ChevalleyCover where
  base : Over (Spec (.of k))
  cover : WCover W base

variable (H : ChevalleyCover (k := k) W)

structure LocalModel {X : Over (Spec (.of k))} (C : WCover W X) (x : X.left) where
  neighborhood : Over X.left
  etale : Etale neighborhood.hom
  contains : x ∈ Set.range neighborhood.hom
  value : Over.mk (neighborhood.hom ≫ X.hom) ⟶ H.base
  comparison : pulled W C neighborhood ≅ pulled W H.cover (Over.mk value.left)
  projection : comparison.hom.left ≫ pullback.snd H.cover.scheme.hom value.left =
    pullback.snd C.scheme.hom neighborhood.hom
  equivariant : ∀ w : W,
    (pulledAction W C neighborhood w).hom ≫ comparison.hom.left =
      comparison.hom.left ≫ (pulledAction W H.cover (Over.mk value.left) w).hom

structure CameralCover (X : Over (Spec (.of k))) where
  cover : WCover W X
  charts : ∀ x : X.left, LocalModel W H cover x

def schemeBaseMap {X : Over (Spec (.of k))} (C : WCover W X) {U V : Over X.left} (h : V ⟶ U) :
    pullback C.scheme.hom V.hom ⟶ pullback C.scheme.hom U.hom :=
  pullback.lift (pullback.fst C.scheme.hom V.hom)
    (pullback.snd C.scheme.hom V.hom ≫ h.left) (by
      rw [Category.assoc, Over.w h]
      exact pullback.condition)

def baseMap {X : Over (Spec (.of k))} (C : WCover W X) {U V : Over X.left} (h : V ⟶ U) :
    pulled W C V ⟶ pulled W C U :=
  Over.homMk (schemeBaseMap W C h) (by
    dsimp only [schemeBaseMap, pulled, Over.mk_left, Over.mk_hom]
    rw [← Category.assoc, pullback.lift_snd, Category.assoc,
      ← Category.assoc h.left U.hom X.hom, Over.w h])

structure BandModel {X : Over (Spec (.of k))} (C : CameralCover W H X) where
  scheme : Over X.left
  [group : GrpObj scheme]
  [smooth : Smooth scheme.hom]
  commutative : μ[scheme] = (β_ scheme scheme).hom ≫ μ[scheme]
  points : ∀ U : Over X.left, (U ⟶ scheme) ≃ Sections T Gm W R C.cover U
  naturality : ∀ {U V : Over X.left} (h : V ⟶ U) (f : U ⟶ scheme),
    (points V (h ≫ f)).val = baseMap W C.cover h ≫ (points U f).val
  identity : letI := T.group
    ∀ U : Over X.left,
      (points U (toUnit U ≫ η[scheme])).val =
        toUnit (pulled W C.cover U) ≫ η[torusScheme k r]
  multiply : letI := T.group
    ∀ (U : Over X.left) (f g : U ⟶ scheme),
      (points U (CartesianMonoidalCategory.lift f g ≫ μ[scheme])).val =
        CartesianMonoidalCategory.lift (points U f).val (points U g).val ≫
          μ[torusScheme k r]

end MathlibExt.AlgebraicGeometry.CameralTorusBands
