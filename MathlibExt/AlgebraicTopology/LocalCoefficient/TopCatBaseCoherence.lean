/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.SSetBaseCoherence
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseFunctoriality

/-!
# Identity and composition coherence for TopCat local-coefficient pullback

Topological pullback local systems are pseudofunctorial through canonical
identity and composition Isos.  Compatibility of the singular-pullback Iso
with these comparisons transports the landed SSet coherence laws to TopCat.

This file makes no CGWH, homology, equivalence, acyclicity, or
plus-construction claim.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uX

namespace TopCat

namespace LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y Z : TopCat.{uX}}

/-- Canonical comparison from topological pullback along the identity to the
original local system. -/
noncomputable def pullbackIdIso (L : TopCat.LocalSystem R X) :
    L.pullback (𝟙 X) ≅ L :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y p
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact congrArg L.map (eq_of_heq (Functor.hcongr_hom
      (_root_.FundamentalGroupoid.map_id (X := X)) p)))

/-- Canonical comparison from topological pullback along a composite to
iterated pullback. -/
noncomputable def pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : TopCat.LocalSystem R Z) :
    L.pullback (f ≫ g) ≅ (L.pullback g).pullback f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y p
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact congrArg L.map (eq_of_heq (Functor.hcongr_hom
      (_root_.FundamentalGroupoid.map_comp g.hom f.hom) p)))

/-- The identity-pullback comparison is the identity on each coefficient
object. -/
@[simp]
theorem pullbackIdIso_hom_app (L : TopCat.LocalSystem R X)
    (x : _root_.FundamentalGroupoid X) :
    (pullbackIdIso L).hom.app x = 𝟙 _ :=
  rfl

/-- The composite-pullback comparison is the identity on each coefficient
object. -/
@[simp]
theorem pullbackCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : TopCat.LocalSystem R Z) (x : _root_.FundamentalGroupoid X) :
    (pullbackCompIso f g L).hom.app x = 𝟙 _ :=
  rfl

end LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y Z : TopCat.{uX}}

private theorem singularFundamentalGroupoidNaturalityObjEq
    (f : X ⟶ Y) (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f) ⋙
        TopCat.singularFundamentalGroupoidFunctor Y).obj
          (SSet.FundamentalGroupoid.mk x) =
      (TopCat.singularFundamentalGroupoidFunctor X ⋙
        _root_.FundamentalGroupoid.map f.hom).obj
          (SSet.FundamentalGroupoid.mk x) := by
  simp only [Functor.comp_obj,
    SSet.mapFundamentalGroupoid_obj_mk,
    TopCat.singularFundamentalGroupoidFunctor_obj_mk]
  apply _root_.FundamentalGroupoid.ext
  rfl

private theorem singularFundamentalGroupoidNaturality_hom_app_mk
    (f : X ⟶ Y) (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.singularFundamentalGroupoidNaturality f).hom.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom (singularFundamentalGroupoidNaturalityObjEq f x) := by
  unfold TopCat.singularFundamentalGroupoidNaturality
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    SSet.realizationFundamentalGroupoidNaturality_app_mk,
    eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans]

private theorem singularFundamentalGroupoidNaturality_inv_app_mk
    (f : X ⟶ Y) (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.singularFundamentalGroupoidNaturality f).inv.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom (singularFundamentalGroupoidNaturalityObjEq f x).symm := by
  apply (cancel_epi
    (eqToHom (singularFundamentalGroupoidNaturalityObjEq f x))).1
  calc
    eqToHom (singularFundamentalGroupoidNaturalityObjEq f x) ≫
        (TopCat.singularFundamentalGroupoidNaturality f).inv.app
          (SSet.FundamentalGroupoid.mk x) =
      (TopCat.singularFundamentalGroupoidNaturality f).hom.app
          (SSet.FundamentalGroupoid.mk x) ≫
        (TopCat.singularFundamentalGroupoidNaturality f).inv.app
          (SSet.FundamentalGroupoid.mk x) := by
            rw [singularFundamentalGroupoidNaturality_hom_app_mk]
    _ = 𝟙 _ :=
      (TopCat.singularFundamentalGroupoidNaturality f).hom_inv_id_app _
    _ = eqToHom (singularFundamentalGroupoidNaturalityObjEq f x) ≫
        eqToHom (singularFundamentalGroupoidNaturalityObjEq f x).symm := by
      rw [eqToHom_trans, eqToHom_refl]

private theorem singularPullbackIsoObjEq
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y)
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f) ⋙
          TopCat.singularFundamentalGroupoidFunctor Y) ⋙ L).obj
        (SSet.FundamentalGroupoid.mk x) =
      ((TopCat.singularFundamentalGroupoidFunctor X ⋙
          _root_.FundamentalGroupoid.map f.hom) ⋙ L).obj
        (SSet.FundamentalGroupoid.mk x) :=
  congrArg L.obj (singularFundamentalGroupoidNaturalityObjEq f x)

private theorem singularPullbackIso_hom_app_mk
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y)
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.LocalSystem.singularPullbackIso f L).hom.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom (singularPullbackIsoObjEq f L x) := by
  change L.map
    ((TopCat.singularFundamentalGroupoidNaturality f).hom.app
      (SSet.FundamentalGroupoid.mk x)) = _
  rw [singularFundamentalGroupoidNaturality_hom_app_mk,
    eqToHom_map]

private theorem singularPullbackIso_inv_app_mk
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y)
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.LocalSystem.singularPullbackIso f L).inv.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom (singularPullbackIsoObjEq f L x).symm := by
  change L.map
    ((TopCat.singularFundamentalGroupoidNaturality f).inv.app
      (SSet.FundamentalGroupoid.mk x)) = _
  rw [singularFundamentalGroupoidNaturality_inv_app_mk,
    eqToHom_map]

namespace LocalSystem

/-- SSet identity-pullback comparison with the connector supplied by
`TopCat.toSSet.map_id`. -/
noncomputable def sSetPullbackIdIso (L : TopCat.LocalSystem R X) :
    L.toSingular.pullback (TopCat.toSSet.map (𝟙 X)) ≅ L.toSingular :=
  SSet.LocalSystem.pullbackCongrIso
      (TopCat.toSSet.map_id X) L.toSingular ≪≫
    SSet.LocalSystem.pullbackIdIso L.toSingular

/-- SSet composite-pullback comparison with the connector supplied by
`TopCat.toSSet.map_comp`. -/
noncomputable def sSetPullbackCompIso
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : TopCat.LocalSystem R Z) :
    L.toSingular.pullback (TopCat.toSSet.map (f ≫ g)) ≅
      (L.toSingular.pullback (TopCat.toSSet.map g)).pullback
        (TopCat.toSSet.map f) :=
  SSet.LocalSystem.pullbackCongrIso
      (TopCat.toSSet.map_comp f g) L.toSingular ≪≫
    SSet.LocalSystem.pullbackCompIso
      (TopCat.toSSet.map f) (TopCat.toSSet.map g) L.toSingular

/-- The singular-pullback comparison is compatible with the identity
pullback Isos. -/
theorem singularPullbackIso_id (L : TopCat.LocalSystem R X) :
    (TopCat.LocalSystem.singularPullbackIso (𝟙 X) L).inv ≫
        (sSetPullbackIdIso L).hom =
      Functor.whiskerLeft
        (TopCat.singularFundamentalGroupoidFunctor X)
        (TopCat.LocalSystem.pullbackIdIso L).hom := by
  apply NatTrans.ext
  funext z
  induction z using SSet.FundamentalGroupoid.rec with
  | mk x =>
      simp only [NatTrans.comp_app, singularPullbackIso_inv_app_mk,
        sSetPullbackIdIso, Iso.trans_hom,
        SSet.LocalSystem.pullbackCongrIso_hom_app,
        SSet.LocalSystem.pullbackIdIso_hom_app,
        Category.comp_id]
      change _ = (TopCat.LocalSystem.pullbackIdIso L).hom.app
        ((TopCat.singularFundamentalGroupoidFunctor X).obj
          (SSet.FundamentalGroupoid.mk x))
      rw [TopCat.LocalSystem.pullbackIdIso_hom_app]
      unfold SSet.congrMapFundamentalGroupoidOfEq
      rw [eqToIso.hom, eqToHom_app, eqToHom_map,
        eqToHom_trans, eqToHom_refl]
      unfold TopCat.LocalSystem.toSingular
      rfl

private theorem singularPullbackIso_inv_whisker_app_mk
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : TopCat.LocalSystem R Z)
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.LocalSystem.singularPullbackIso g L).inv.app
        ((SSet.mapFundamentalGroupoid
          (TopCat.toSSet.map f)).obj
            (SSet.FundamentalGroupoid.mk x)) =
      eqToHom (singularPullbackIsoObjEq g L
        ((TopCat.toSSet.map f).app
          (Opposite.op (SimplexCategory.mk 0)) x)).symm := by
  change (TopCat.LocalSystem.singularPullbackIso g L).inv.app
      (SSet.FundamentalGroupoid.mk
        ((TopCat.toSSet.map f).app
          (Opposite.op (SimplexCategory.mk 0)) x)) = _
  exact singularPullbackIso_inv_app_mk g L _

/-- Two composites of equality transports with common endpoints agree even
when their intermediate objects use different presentations. -/
private theorem eqToHom_comp_eqToHom
    {C : Type*} [Category C] {A B B' D : C}
    (p : A = B) (q : B = D) (r : A = B') (s : B' = D) :
    eqToHom p ≫ eqToHom q = eqToHom r ≫ eqToHom s := by
  rw [CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans]

/-- The singular-pullback comparison is compatible with the composite
pullback Isos. -/
theorem singularPullbackIso_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : TopCat.LocalSystem R Z) :
    Functor.whiskerLeft
          (TopCat.singularFundamentalGroupoidFunctor X)
          (TopCat.LocalSystem.pullbackCompIso f g L).hom ≫
        (TopCat.LocalSystem.singularPullbackIso
          f (L.pullback g)).inv ≫
        Functor.whiskerLeft
          (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))
          (TopCat.LocalSystem.singularPullbackIso g L).inv =
      (TopCat.LocalSystem.singularPullbackIso (f ≫ g) L).inv ≫
        (sSetPullbackCompIso f g L).hom := by
  apply NatTrans.ext
  funext z
  induction z using SSet.FundamentalGroupoid.rec with
  | mk x =>
      change (TopCat.LocalSystem.pullbackCompIso f g L).hom.app
            ((TopCat.singularFundamentalGroupoidFunctor X).obj
              (SSet.FundamentalGroupoid.mk x)) ≫
          (TopCat.LocalSystem.singularPullbackIso
            f (L.pullback g)).inv.app
              (SSet.FundamentalGroupoid.mk x) ≫
          (TopCat.LocalSystem.singularPullbackIso g L).inv.app
            ((SSet.mapFundamentalGroupoid
              (TopCat.toSSet.map f)).obj
                (SSet.FundamentalGroupoid.mk x)) =
        (TopCat.LocalSystem.singularPullbackIso
            (f ≫ g) L).inv.app (SSet.FundamentalGroupoid.mk x) ≫
          (sSetPullbackCompIso f g L).hom.app
            (SSet.FundamentalGroupoid.mk x)
      rw [TopCat.LocalSystem.pullbackCompIso_hom_app,
        Category.id_comp, singularPullbackIso_inv_app_mk,
        singularPullbackIso_inv_whisker_app_mk,
        singularPullbackIso_inv_app_mk]
      simp only [sSetPullbackCompIso, Iso.trans_hom,
        NatTrans.comp_app,
        SSet.LocalSystem.pullbackCongrIso_hom_app,
        SSet.LocalSystem.pullbackCompIso_hom_app,
        Category.comp_id]
      unfold SSet.congrMapFundamentalGroupoidOfEq
      rw [eqToIso.hom, eqToHom_app, eqToHom_map]
      exact eqToHom_comp_eqToHom _ _ _ _

end LocalSystem

/-- TopCat local-coefficient pullback chain maps preserve identities through
the canonical topological pullback comparison. -/
theorem localCoefficientPullbackChainMap_id
    (L : TopCat.LocalSystem R X) :
    TopCat.localCoefficientPullbackChainMap (𝟙 X) L =
      SSet.localCoefficientChainMap
        (Functor.whiskerLeft
          (TopCat.singularFundamentalGroupoidFunctor X)
          (TopCat.LocalSystem.pullbackIdIso L).hom) := by
  unfold TopCat.localCoefficientPullbackChainMap
  rw [SSet.localCoefficientPullbackChainMap_congr
    (TopCat.toSSet.map_id X) L.toSingular]
  rw [SSet.localCoefficientPullbackChainMap_id]
  rw [← SSet.localCoefficientChainMap_comp]
  rw [← SSet.localCoefficientChainMap_comp]
  apply congrArg SSet.localCoefficientChainMap
  exact TopCat.LocalSystem.singularPullbackIso_id L

/-- TopCat local-coefficient pullback chain maps preserve composition through
the canonical topological pullback comparison. -/
theorem localCoefficientPullbackChainMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : TopCat.LocalSystem R Z) :
    TopCat.localCoefficientPullbackChainMap (f ≫ g) L =
      SSet.localCoefficientChainMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X)
            (TopCat.LocalSystem.pullbackCompIso f g L).hom) ≫
        TopCat.localCoefficientPullbackChainMap f (L.pullback g) ≫
        TopCat.localCoefficientPullbackChainMap g L := by
  have hBase :
      SSet.localCoefficientPullbackChainMap
          (TopCat.toSSet.map (f ≫ g)) L.toSingular =
        SSet.localCoefficientChainMap
            (TopCat.LocalSystem.sSetPullbackCompIso f g L).hom ≫
          SSet.localCoefficientPullbackChainMap
            (TopCat.toSSet.map f)
              (L.toSingular.pullback (TopCat.toSSet.map g)) ≫
          SSet.localCoefficientPullbackChainMap
            (TopCat.toSSet.map g) L.toSingular := by
    rw [SSet.localCoefficientPullbackChainMap_congr
      (TopCat.toSSet.map_comp f g) L.toSingular]
    rw [SSet.localCoefficientPullbackChainMap_comp]
    slice_lhs 1 2 => rw [← SSet.localCoefficientChainMap_comp]
    rfl
  have hCoeff :
      SSet.localCoefficientChainMap
            (TopCat.LocalSystem.singularPullbackIso (f ≫ g) L).inv ≫
          SSet.localCoefficientChainMap
            (TopCat.LocalSystem.sSetPullbackCompIso f g L).hom =
        SSet.localCoefficientChainMap
            (Functor.whiskerLeft
              (TopCat.singularFundamentalGroupoidFunctor X)
              (TopCat.LocalSystem.pullbackCompIso f g L).hom) ≫
          SSet.localCoefficientChainMap
            (TopCat.LocalSystem.singularPullbackIso
              f (L.pullback g)).inv ≫
          SSet.localCoefficientChainMap
            (SSet.LocalSystem.pullbackMap
              (TopCat.toSSet.map f)
              (TopCat.LocalSystem.singularPullbackIso g L).inv) := by
    rw [← SSet.localCoefficientChainMap_comp]
    rw [← SSet.localCoefficientChainMap_comp]
    rw [← SSet.localCoefficientChainMap_comp]
    apply congrArg SSet.localCoefficientChainMap
    exact (TopCat.LocalSystem.singularPullbackIso_comp f g L).symm
  have hNat := SSet.localCoefficientPullbackChainMap_naturality
    (TopCat.toSSet.map f)
    (TopCat.LocalSystem.singularPullbackIso g L).inv
  unfold TopCat.localCoefficientPullbackChainMap
  rw [hBase]
  slice_lhs 1 2 => exact hCoeff
  slice_lhs 3 4 => exact hNat
  simp only [Category.assoc]

end TopCat
