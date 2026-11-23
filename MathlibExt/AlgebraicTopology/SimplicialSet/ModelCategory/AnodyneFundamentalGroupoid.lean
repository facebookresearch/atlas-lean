/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveEquiv
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveKan
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AnodyneRelativeHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetAnodyneLifting

/-!
# Fundamental groupoids of anodyne extensions

An anodyne extension induces an equivalence of simplicial fundamental
groupoids.  The proof extends the canonical map to the nerve of the source
fundamental groupoid, uses the resulting strict retraction for one triangle,
and obtains the other triangle from a relative simplicial homotopy.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

private noncomputable def fundamentalGroupoidNerveUnit (X : SSet.{u}) :
    X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid X) :=
  SSet.fundamentalGroupoidNerveEquiv X
    (SSet.FundamentalGroupoid X) (𝟭 _)

private noncomputable def fundamentalGroupoidNerveCounit
    (G : Type u) [Groupoid.{u} G] :
    SSet.FundamentalGroupoid (CategoryTheory.nerve G) ⥤ G :=
  (SSet.fundamentalGroupoidNerveEquiv
    (CategoryTheory.nerve G) G).symm
      (𝟙 (CategoryTheory.nerve G))

private theorem fundamentalGroupoidNerveUnit_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ fundamentalGroupoidNerveUnit Y =
      fundamentalGroupoidNerveUnit X ≫
        CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f) := by
  calc
    f ≫ fundamentalGroupoidNerveUnit Y =
        SSet.fundamentalGroupoidNerveEquiv X
          (SSet.FundamentalGroupoid Y)
          (SSet.mapFundamentalGroupoid f ⋙ 𝟭 _) :=
      (SSet.fundamentalGroupoidNerveEquiv_precomp f (𝟭 _)).symm
    _ = SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y)
        (SSet.mapFundamentalGroupoid f) :=
      congrArg (SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y))
        (Functor.comp_id (SSet.mapFundamentalGroupoid f))
    _ = fundamentalGroupoidNerveUnit X ≫
        CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f) := by
      have h := SSet.fundamentalGroupoidNerveEquiv_postcomp
        (X := X) (𝟭 (SSet.FundamentalGroupoid X))
        (SSet.mapFundamentalGroupoid f)
      exact (congrArg (SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y))
          (Functor.id_comp (SSet.mapFundamentalGroupoid f))).symm.trans h

private theorem fundamentalGroupoidNerveDesc_eq_map_comp_counit
    {Z : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (q : Z ⟶ CategoryTheory.nerve G) :
    (SSet.fundamentalGroupoidNerveEquiv Z G).symm q =
      SSet.mapFundamentalGroupoid q ⋙
        fundamentalGroupoidNerveCounit G := by
  apply (SSet.fundamentalGroupoidNerveEquiv Z G).injective
  rw [SSet.fundamentalGroupoidNerveEquiv_precomp]
  rw [Equiv.apply_symm_apply]
  change q = q ≫ SSet.fundamentalGroupoidNerveEquiv
    (CategoryTheory.nerve G) G
      ((SSet.fundamentalGroupoidNerveEquiv
        (CategoryTheory.nerve G) G).symm
          (𝟙 (CategoryTheory.nerve G)))
  rw [Equiv.apply_symm_apply, Category.comp_id]

private noncomputable def fundamentalGroupoidNerveHomotopyIso
    {Z : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    {a b : Z ⟶ CategoryTheory.nerve G} (H : SSet.Homotopy a b) :
    (SSet.fundamentalGroupoidNerveEquiv Z G).symm a ≅
      (SSet.fundamentalGroupoidNerveEquiv Z G).symm b :=
  eqToIso (fundamentalGroupoidNerveDesc_eq_map_comp_counit a) ≪≫
    Functor.isoWhiskerRight (SSet.congrMapFundamentalGroupoid H)
      (fundamentalGroupoidNerveCounit G) ≪≫
    (eqToIso (fundamentalGroupoidNerveDesc_eq_map_comp_counit b)).symm

namespace anodyneExtensions

/-- An anodyne extension induces an equivalence of simplicial fundamental
groupoids. -/
theorem isEquivalence_mapFundamentalGroupoid
    {X Y : SSet.{u}} {i : X ⟶ Y} (hi : SSet.anodyneExtensions i) :
    (SSet.mapFundamentalGroupoid i).IsEquivalence := by
  let _ : SSet.KanComplex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid X)
  obtain ⟨rbar, hrbar⟩ :=
    SSet.anodyneExtensions.exists_lift_of_isFibrant
      (fundamentalGroupoidNerveUnit X) hi
  let R : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid X :=
    (SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid X)).symm rbar
  have hfirst : SSet.mapFundamentalGroupoid i ⋙ R = 𝟭 _ := by
    apply (SSet.fundamentalGroupoidNerveEquiv X
      (SSet.FundamentalGroupoid X)).injective
    rw [SSet.fundamentalGroupoidNerveEquiv_precomp]
    change i ≫ SSet.fundamentalGroupoidNerveEquiv Y
        (SSet.FundamentalGroupoid X) R =
      fundamentalGroupoidNerveUnit X
    rw [show SSet.fundamentalGroupoidNerveEquiv Y
        (SSet.FundamentalGroupoid X) R = rbar by
      exact (SSet.fundamentalGroupoidNerveEquiv Y
        (SSet.FundamentalGroupoid X)).apply_symm_apply rbar]
    exact hrbar
  let a : Y ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) :=
    rbar ≫ CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid i)
  let b : Y ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) :=
    fundamentalGroupoidNerveUnit Y
  have hab : i ≫ a = i ≫ b := by
    dsimp [a, b]
    calc
      i ≫ rbar ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid i) =
        fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid i) := by
            rw [← Category.assoc, hrbar]
      _ = i ≫ fundamentalGroupoidNerveUnit Y :=
        (fundamentalGroupoidNerveUnit_naturality i).symm
  let _ : SSet.KanComplex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid Y)) :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid Y)
  obtain ⟨H, _⟩ :=
    SSet.anodyneExtensions.exists_homotopy_rel hi hab
  have hpost : R ⋙ SSet.mapFundamentalGroupoid i =
      (SSet.fundamentalGroupoidNerveEquiv Y
        (SSet.FundamentalGroupoid Y)).symm a := by
    apply (SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid Y)).injective
    rw [SSet.fundamentalGroupoidNerveEquiv_postcomp]
    rw [(SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid Y)).apply_symm_apply]
    change SSet.fundamentalGroupoidNerveEquiv Y
        (SSet.FundamentalGroupoid X) R ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid i) = a
    rw [show SSet.fundamentalGroupoidNerveEquiv Y
        (SSet.FundamentalGroupoid X) R = rbar by
      exact (SSet.fundamentalGroupoidNerveEquiv Y
        (SSet.FundamentalGroupoid X)).apply_symm_apply rbar]
  have hb : (SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid Y)).symm b = 𝟭 _ := by
    exact (SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid Y)).left_inv (𝟭 _)
  let hsecond : R ⋙ SSet.mapFundamentalGroupoid i ≅ 𝟭 _ :=
    eqToIso hpost ≪≫ fundamentalGroupoidNerveHomotopyIso H ≪≫
      eqToIso hb
  exact (CategoryTheory.Equivalence.mk
    (SSet.mapFundamentalGroupoid i) R
      (eqToIso hfirst.symm) hsecond).isEquivalence_functor

end anodyneExtensions

end SSet

end
