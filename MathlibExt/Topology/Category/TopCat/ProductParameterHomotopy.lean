/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Basic

/-!
# Currying the whole original product homotopy

An actual continuous map on the ordinary product is curried in its second
variable. An actual homotopy on that whole product curries to a homotopy
in the compact-open mapping space, retaining every active parameter and
the exact original second-variable composition. No local compactness of
the active source and no pointwise-to-joint continuity inference is used.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace TopCat

variable {A X C : TopCat.{u}}

private def curriedProductRecipe (f : TopCat.of (A × X) ⟶ C) :
    X ⟶ TopCat.of C(A, C) :=
  TopCat.ofHom (f.hom.comp
    ((ContinuousMap.snd : C(X × A, A)).prodMk
      (ContinuousMap.fst : C(X × A, X)))).curry

private theorem curriedProductRecipe_apply (f : TopCat.of (A × X) ⟶ C)
    (x : X) (a : A) :
    curriedProductRecipe f x a = f (a, x) := by
  have hm : (curriedProductRecipe f).hom =
      (f.hom.comp
        ((ContinuousMap.snd : C(X × A, A)).prodMk
          (ContinuousMap.fst : C(X × A, X)))).curry := by
    unfold curriedProductRecipe
    exact TopCat.hom_ofHom _
  exact (congrArg (fun k : C(X, C(A, C)) => k x a) hm).trans (by
    rw [ContinuousMap.curry_apply, ContinuousMap.comp_apply]
    rfl)

/-- Currying in the original second variable, with the ordinary
compact-open target and the same two underlying spaces. -/
public def curriedProductMap (f : TopCat.of (A × X) ⟶ C) :
    X ⟶ TopCat.of C(A, C) :=
  curriedProductRecipe f

/-- Every original active and second-variable value is unchanged. -/
public theorem curriedProductMap_apply (f : TopCat.of (A × X) ⟶ C)
    (x : X) (a : A) :
    curriedProductMap f x a = f (a, x) := by
  unfold curriedProductMap
  exact curriedProductRecipe_apply f x a

private theorem curriedProductRecipe_comp_second
    {B : TopCat.{u}} (j : X ⟶ B) (f : TopCat.of (A × B) ⟶ C) :
    curriedProductRecipe (TopCat.ofHom ((ContinuousMap.id A).prodMap j.hom) ≫ f) =
      j ≫ curriedProductRecipe f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro a
  have hleft : (TopCat.ofHom ((ContinuousMap.id A).prodMap j.hom) ≫ f) (a, x) =
      f (a, j x) := by
    change (TopCat.ofHom ((ContinuousMap.id A).prodMap j.hom) ≫ f).hom (a, x) =
      f.hom (a, j.hom x)
    rw [TopCat.hom_comp, ContinuousMap.comp_apply, TopCat.hom_ofHom]
    rfl
  have hright : ((j ≫ curriedProductRecipe f).hom x) a =
      curriedProductRecipe f (j x) a := by
    rw [TopCat.hom_comp, ContinuousMap.comp_apply]
  exact (curriedProductRecipe_apply
    (TopCat.ofHom ((ContinuousMap.id A).prodMap j.hom) ≫ f) x a).trans
      (hleft.trans ((curriedProductRecipe_apply f (j x) a).symm.trans hright.symm))

/-- The literal second-variable source composition becomes the literal
composition in the compact-open target. -/
@[reassoc]
public theorem curriedProductMap_comp_second
    {B : TopCat.{u}} (j : X ⟶ B) (f : TopCat.of (A × B) ⟶ C) :
    curriedProductMap (TopCat.ofHom ((ContinuousMap.id A).prodMap j.hom) ≫ f) =
      j ≫ curriedProductMap f := by
  unfold curriedProductMap
  exact curriedProductRecipe_comp_second j f

private def curriedProductHomotopyRecipe
    {f g : TopCat.of (A × X) ⟶ C}
    (K : ContinuousMap.Homotopy f.hom g.hom) :
    ContinuousMap.Homotopy (curriedProductRecipe f).hom
      (curriedProductRecipe g).hom where
  toFun tx :=
    { toFun a := K (tx.1, (a, tx.2))
      continuous_toFun := K.continuous.comp
        (continuous_const.prodMk (continuous_id.prodMk continuous_const)) }
  continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
    (K.continuous.comp
      (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)))
  map_zero_left x := by
    apply ContinuousMap.ext
    intro a
    exact (K.map_zero_left (a, x)).trans (curriedProductRecipe_apply f x a).symm
  map_one_left x := by
    apply ContinuousMap.ext
    intro a
    exact (K.map_one_left (a, x)).trans (curriedProductRecipe_apply g x a).symm

private theorem curriedProductHomotopyRecipe_apply
    {f g : TopCat.of (A × X) ⟶ C}
    (K : ContinuousMap.Homotopy f.hom g.hom) (t : unitInterval) (x : X) (a : A) :
    curriedProductHomotopyRecipe K (t, x) a = K (t, (a, x)) := rfl

/-- A genuine whole product homotopy gives a compact-open homotopy of
the original curried maps. This retains its actual image-point trace;
it is not asserted to be a based homotopy. -/
public def curriedProductHomotopy
    {f g : TopCat.of (A × X) ⟶ C}
    (K : ContinuousMap.Homotopy f.hom g.hom) :
    ContinuousMap.Homotopy (curriedProductMap f).hom
      (curriedProductMap g).hom := by
  unfold curriedProductMap
  exact curriedProductHomotopyRecipe K

/-- The full parameterized homotopy evaluates to the same original
product homotopy at every time and every active/source point. -/
public theorem curriedProductHomotopy_apply
    {f g : TopCat.of (A × X) ⟶ C}
    (K : ContinuousMap.Homotopy f.hom g.hom) (t : unitInterval) (x : X) (a : A) :
    curriedProductHomotopy K (t, x) a = K (t, (a, x)) := by
  unfold curriedProductHomotopy
  exact curriedProductHomotopyRecipe_apply K t x a

end TopCat

end
