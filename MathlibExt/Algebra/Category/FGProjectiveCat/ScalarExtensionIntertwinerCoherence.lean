/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionIntertwiner
public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionFunctorCoherence

/-!
# Coherence of scalar-extension coefficient intertwiners

The original unit coefficient compares scalar extension along equal ring
maps. Coefficient transformations commute with postcomposition and
precomposition of arbitrary associative-ring homomorphisms through the
canonical native tensor-composition isomorphisms. All readers retain the
original balanced tensor and shrink coordinates.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory
open ModuleCat.RingHomScalarExtension

universe uR uS uT

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

/-- Morphisms out of native scalar extension are determined by the original pure classes. -/
theorem ringScalarExtension_hom_ext (f : R →+* S) (X : FGProjectiveCat.{uR} R)
    {Y : FGProjectiveCat.{uS} S} {a b : (ringScalarExtension f).obj X ⟶ Y}
    (h : ∀ s x, a.hom.hom ((ringScalarExtensionCoordinates f X).symm (pure f X s x)) =
      b.hom.hom ((ringScalarExtensionCoordinates f X).symm (pure f X s x))) : a = b := by
  apply FGProjectiveCat.hom_ext
  have hm : a.hom.hom.comp (ringScalarExtensionCoordinates f X).symm.toLinearMap =
      b.hom.hom.comp (ringScalarExtensionCoordinates f X).symm.toLinearMap := by
    apply linearMap_ext f X
    exact h
  apply LinearMap.ext
  intro z
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
    using LinearMap.congr_fun hm (ringScalarExtensionCoordinates f X z)

private theorem nativeThreeCompose_ext (f : R →+* S) (X : FGProjectiveCat.{uR} R)
    {A B Z : FGProjectiveCat.{uS} S}
    (a : (ringScalarExtension f).obj X ⟶ A) (b : A ⟶ B) (d : B ⟶ Z)
    {c : (ringScalarExtension f).obj X ⟶ Z}
    (h : ∀ s x, d.hom.hom (b.hom.hom (a.hom.hom
      ((ringScalarExtensionCoordinates f X).symm (pure f X s x)))) =
        c.hom.hom ((ringScalarExtensionCoordinates f X).symm (pure f X s x))) :
    a ≫ b ≫ d = c := by
  apply ringScalarExtension_hom_ext f X
  exact h

private theorem nativeThreeCompare_ext (f : R →+* S) (X : FGProjectiveCat.{uR} R)
    {A B B' Z : FGProjectiveCat.{uS} S}
    (a : (ringScalarExtension f).obj X ⟶ A) (b : A ⟶ B) (d : B ⟶ Z)
    (b' : A ⟶ B') (d' : B' ⟶ Z)
    (h : ∀ s x, d.hom.hom (b.hom.hom (a.hom.hom
      ((ringScalarExtensionCoordinates f X).symm (pure f X s x)))) =
        d'.hom.hom (b'.hom.hom (a.hom.hom
          ((ringScalarExtensionCoordinates f X).symm (pure f X s x))))) :
    a ≫ b ≫ d = a ≫ b' ≫ d' := by
  apply ringScalarExtension_hom_ext f X
  exact h

/-- Native scalar extension maps the original pure class through the original module map. -/
theorem ringScalarExtension_map_pure (f : R →+* S)
    {X Y : FGProjectiveCat.{uR} R} (a : X ⟶ Y) (s : S) (x : X) :
    ((ringScalarExtension f).map a).hom.hom
      ((ringScalarExtensionCoordinates f X).symm (pure f X s x)) =
        (ringScalarExtensionCoordinates f Y).symm (pure f Y s (a.hom.hom x)) := by
  apply (ringScalarExtensionCoordinates f Y).injective
  have h := LinearMap.congr_fun (ringScalarExtensionCoordinates_naturality f a)
    ((ringScalarExtensionCoordinates f X).symm (pure f X s x))
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, linearMap_pure] using h

/-- The native composition map returns the original ordered pure class in target coordinates. -/
theorem ringScalarExtensionCompIso_hom_apply_pure (f : R →+* S) (g : S →+* T)
    (X : FGProjectiveCat.{uR} R) (t : T) (s : S) (x : X) :
    ((ringScalarExtensionCompIso f g).hom.app X).hom.hom
        ((ringScalarExtensionCoordinates g ((ringScalarExtension f).obj X)).symm
          (pure g ((ringScalarExtension f).obj X) t
            ((ringScalarExtensionCoordinates f X).symm (pure f X s x)))) =
      (ringScalarExtensionCoordinates (g.comp f) X).symm
        (pure (g.comp f) X (t * g s) x) := by
  apply (ringScalarExtensionCoordinates (g.comp f) X).injective
  simpa only [LinearEquiv.apply_symm_apply]
    using ringScalarExtensionCompIso_hom_nested_pure f g X t s x

/-- Compare the same original scalar extensions by their actual unit coefficient maps. -/
def ringScalarExtensionHomEqualityIso (f g : R →+* S) (h : f = g) :
    ringScalarExtension f ≅ ringScalarExtension g where
  hom := ringScalarExtensionIntertwiner f g 1 (Intertwines.of_eq h)
  inv := ringScalarExtensionIntertwiner g f 1 (Intertwines.of_eq h.symm)
  hom_inv_id := by
    rw [ringScalarExtensionIntertwiner_comp]
    simp only [one_mul, ringScalarExtensionIntertwiner_one]
  inv_hom_id := by
    rw [ringScalarExtensionIntertwiner_comp]
    simp only [one_mul, ringScalarExtensionIntertwiner_one]

/-- The equality comparison keeps the same coefficient and original target coordinates. -/
theorem ringScalarExtensionHomEqualityIso_hom_pure (f g : R →+* S) (h : f = g)
    (X : FGProjectiveCat.{uR} R) (s : S) (x : X) :
    ((ringScalarExtensionHomEqualityIso f g h).hom.app X).hom.hom
        ((ringScalarExtensionCoordinates f X).symm (pure f X s x)) =
      (ringScalarExtensionCoordinates g X).symm (pure g X s x) := by
  change ((ringScalarExtensionIntertwiner f g 1 (Intertwines.of_eq h)).app X).hom.hom _ = _
  rw [ringScalarExtensionIntertwiner_apply_pure, mul_one]

/-- The original inverse equality comparison also retains every actual pure coefficient. -/
theorem ringScalarExtensionHomEqualityIso_inv_pure (f g : R →+* S) (h : f = g)
    (X : FGProjectiveCat.{uR} R) (s : S) (x : X) :
    ((ringScalarExtensionHomEqualityIso f g h).inv.app X).hom.hom
        ((ringScalarExtensionCoordinates g X).symm (pure g X s x)) =
      (ringScalarExtensionCoordinates f X).symm (pure f X s x) :=
  ringScalarExtensionHomEqualityIso_hom_pure g f h.symm X s x

private theorem nativeIntertwinerMap_pure (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (k : S →+* T) (X : FGProjectiveCat.{uR} R)
    (t : T) (s : S) (x : X) :
    (((ringScalarExtension k).map
        ((ringScalarExtensionIntertwiner f g c hc).app X)).hom.hom)
        ((ringScalarExtensionCoordinates k ((ringScalarExtension f).obj X)).symm
          (pure k ((ringScalarExtension f).obj X) t
            ((ringScalarExtensionCoordinates f X).symm (pure f X s x)))) =
      (ringScalarExtensionCoordinates k ((ringScalarExtension g).obj X)).symm
        (pure k ((ringScalarExtension g).obj X) t
          ((ringScalarExtensionCoordinates g X).symm (pure g X (s * c) x))) := by
  rw [ringScalarExtension_map_pure, ringScalarExtensionIntertwiner_apply_pure]

private theorem nativeIntertwinerComposite_pure (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (k : S →+* T) (X : FGProjectiveCat.{uR} R)
    (t : T) (s : S) (x : X) :
    ((ringScalarExtensionCompIso g k).hom.app X).hom.hom
        ((((ringScalarExtension k).map
          ((ringScalarExtensionIntertwiner f g c hc).app X)).hom.hom)
          ((ringScalarExtensionCoordinates k ((ringScalarExtension f).obj X)).symm
            (pure k ((ringScalarExtension f).obj X) t
              ((ringScalarExtensionCoordinates f X).symm (pure f X s x))))) =
      (ringScalarExtensionCoordinates (k.comp g) X).symm
        (pure (k.comp g) X (t * k (s * c)) x) :=
  (congrArg (((ringScalarExtensionCompIso g k).hom.app X).hom.hom)
    (nativeIntertwinerMap_pure f g c hc k X t s x)).trans
      (ringScalarExtensionCompIso_hom_apply_pure g k X t (s * c) x)

private theorem coefficientPushforward_app (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (k : S →+* T) (X : FGProjectiveCat.{uR} R) :
    (ringScalarExtension k).map ((ringScalarExtensionIntertwiner f g c hc).app X) ≫
        (ringScalarExtensionCompIso g k).hom.app X =
      (ringScalarExtensionCompIso f k).hom.app X ≫
        (ringScalarExtensionIntertwiner (k.comp f) (k.comp g) (k c)
          (Intertwines.map hc k)).app X := by
  have hzero : (ringScalarExtensionCompIso f k).inv.app X ≫
      ((ringScalarExtension k).map ((ringScalarExtensionIntertwiner f g c hc).app X) ≫
      (ringScalarExtensionCompIso g k).hom.app X) =
      (ringScalarExtensionIntertwiner (k.comp f) (k.comp g) (k c)
        (Intertwines.map hc k)).app X := by
    apply nativeThreeCompose_ext (k.comp f) X
      ((ringScalarExtensionCompIso f k).inv.app X)
      ((ringScalarExtension k).map ((ringScalarExtensionIntertwiner f g c hc).app X))
      ((ringScalarExtensionCompIso g k).hom.app X)
    intro t x
    calc
      _ = ((ringScalarExtensionCompIso g k).hom.app X).hom.hom
          (((ringScalarExtension k).map
              ((ringScalarExtensionIntertwiner f g c hc).app X)).hom.hom
            ((ringScalarExtensionCoordinates k ((ringScalarExtension f).obj X)).symm
              (pure k ((ringScalarExtension f).obj X) t
                ((ringScalarExtensionCoordinates f X).symm (pure f X 1 x))))) :=
        congrArg (fun z => ((ringScalarExtensionCompIso g k).hom.app X).hom.hom
          (((ringScalarExtension k).map
            ((ringScalarExtensionIntertwiner f g c hc).app X)).hom.hom z))
          (ringScalarExtensionCompIso_inv_pure f k X t x)
      _ = (ringScalarExtensionCoordinates (k.comp g) X).symm
          (pure (k.comp g) X (t * k c) x) := by
        simpa only [one_mul] using nativeIntertwinerComposite_pure f g c hc k X t 1 x
      _ = _ := (ringScalarExtensionIntertwiner_apply_pure
        (k.comp f) (k.comp g) (k c) (Intertwines.map hc k) X t x).symm
  exact ((ringScalarExtensionCompIso f k).app X).inv_comp_eq.mp hzero

/-- Whole naturality of original coefficient maps through actual scalar composition. -/
theorem ringScalarExtensionIntertwiner_pushforward (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (k : S →+* T) :
    Functor.whiskerRight (ringScalarExtensionIntertwiner f g c hc) (ringScalarExtension k) ≫
        (ringScalarExtensionCompIso g k).hom =
      (ringScalarExtensionCompIso f k).hom ≫
        ringScalarExtensionIntertwiner (k.comp f) (k.comp g) (k c)
          (Intertwines.map hc k) := by
  apply NatTrans.ext
  funext X
  exact coefficientPushforward_app f g c hc k X

private theorem coefficientPrecompose_app (k : R →+* S) (f g : S →+* T) (c : T)
    (hc : Intertwines f g c) (X : FGProjectiveCat.{uR} R) :
    (ringScalarExtensionIntertwiner f g c hc).app ((ringScalarExtension k).obj X) ≫
        (ringScalarExtensionCompIso k g).hom.app X =
      (ringScalarExtensionCompIso k f).hom.app X ≫
        (ringScalarExtensionIntertwiner (f.comp k) (g.comp k) c
          (Intertwines.precomp hc k)).app X := by
  have hzero : (ringScalarExtensionCompIso k f).inv.app X ≫
      ((ringScalarExtensionIntertwiner f g c hc).app ((ringScalarExtension k).obj X) ≫
        (ringScalarExtensionCompIso k g).hom.app X) =
      (ringScalarExtensionIntertwiner (f.comp k) (g.comp k) c
        (Intertwines.precomp hc k)).app X := by
    apply ringScalarExtension_hom_ext (f.comp k) X
    intro t x
    apply (ringScalarExtensionCoordinates (g.comp k) X).injective
    change ringScalarExtensionCoordinates (g.comp k) X
        (((ringScalarExtensionCompIso k g).hom.app X).hom.hom
          (((ringScalarExtensionIntertwiner f g c hc).app
              ((ringScalarExtension k).obj X)).hom.hom
            (((ringScalarExtensionCompIso k f).inv.app X).hom.hom
              ((ringScalarExtensionCoordinates (f.comp k) X).symm
                (pure (f.comp k) X t x))))) = _
    rw [ringScalarExtensionCompIso_inv_pure, ringScalarExtensionIntertwiner_apply_pure,
      ringScalarExtensionIntertwiner_pure, ringScalarExtensionCompIso_hom_apply_pure,
      LinearEquiv.apply_symm_apply, map_one, mul_one]
  exact ((ringScalarExtensionCompIso k f).app X).inv_comp_eq.mp hzero

/-- Whole source-ring naturality of the actual coefficient transformations. -/
theorem ringScalarExtensionIntertwiner_precompose (k : R →+* S) (f g : S →+* T) (c : T)
    (hc : Intertwines f g c) :
    Functor.whiskerLeft (ringScalarExtension k) (ringScalarExtensionIntertwiner f g c hc) ≫
        (ringScalarExtensionCompIso k g).hom =
      (ringScalarExtensionCompIso k f).hom ≫
        ringScalarExtensionIntertwiner (f.comp k) (g.comp k) c
          (Intertwines.precomp hc k) := by
  apply NatTrans.ext
  funext X
  exact coefficientPrecompose_app k f g c hc X

/-- A comparison with the displayed original pure reader commutes with coefficients preserved
by the ring map. -/
theorem ringScalarExtensionIntertwiner_commuting_naturality (a : R →+* R) (b : S →+* S)
    (k : R →+* S)
    (β : ringScalarExtension a ⋙ ringScalarExtension k ≅
      ringScalarExtension k ⋙ ringScalarExtension b)
    (hβ : ∀ (X : FGProjectiveCat.{uR} R) (t : S) (s : R) (x : X),
      (β.hom.app X).hom.hom
          ((ringScalarExtensionCoordinates k ((ringScalarExtension a).obj X)).symm
            (pure k ((ringScalarExtension a).obj X) t
              ((ringScalarExtensionCoordinates a X).symm (pure a X s x)))) =
        (ringScalarExtensionCoordinates b ((ringScalarExtension k).obj X)).symm
          (pure b ((ringScalarExtension k).obj X) (t * k s)
            ((ringScalarExtensionCoordinates k X).symm (pure k X 1 x))))
    (cR : R) (cS : S) (hcR : Intertwines a a cR) (hcS : Intertwines b b cS)
    (hmap : k cR = cS) :
    Functor.whiskerRight (ringScalarExtensionIntertwiner a a cR hcR)
        (ringScalarExtension k) ≫ β.hom =
      β.hom ≫ Functor.whiskerLeft (ringScalarExtension k)
        (ringScalarExtensionIntertwiner b b cS hcS) := by
  apply NatTrans.ext
  funext X
  apply (cancel_epi ((ringScalarExtensionCompIso a k).inv.app X)).1
  apply nativeThreeCompare_ext (k.comp a) X
    ((ringScalarExtensionCompIso a k).inv.app X)
    ((ringScalarExtension k).map ((ringScalarExtensionIntertwiner a a cR hcR).app X))
    (β.hom.app X) (β.hom.app X)
    ((ringScalarExtensionIntertwiner b b cS hcS).app ((ringScalarExtension k).obj X))
  intro t x
  simp only [ringScalarExtensionCompIso_inv_pure, hβ, map_one, mul_one]
  have hp := nativeIntertwinerMap_pure a a cR hcR k X t 1 x
  simp only [one_mul] at hp
  rw [hp, hβ, hmap]
  exact (ringScalarExtensionIntertwiner_apply_pure b b cS hcS
    ((ringScalarExtension k).obj X) t
    ((ringScalarExtensionCoordinates k X).symm (pure k X 1 x))).symm

end FGProjectiveCat

end
