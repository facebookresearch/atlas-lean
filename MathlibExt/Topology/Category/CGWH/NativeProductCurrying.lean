/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianClosed
public import MathlibExt.Topology.Category.CGWH.GeneratedHomCompactOpen
public import Mathlib.Topology.Homotopy.Basic
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidalComputations
public import MathlibExt.Topology.Category.CGWH.InternalHomCompactOpen

/-!
# Original native product families in the compact-open mapping space

Native currying followed by the existing generated/compact-open comparison
retains the original product map at every parameter. A whole ordinary
homotopy on that native product curries as well: only its compact interval
parameter is converted through an ordinary-product homeomorphism. There
is no local-compactness condition on either classifying-space parameter.
All image-point traces remain the actual traces of the original homotopy.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology MonoidalCategory

universe u

namespace CGWH

variable {A X B : CGWH.{u, u}} [T2Space A]

private def nativeCompactOpenCurryRecipe (f : A ⊗ X ⟶ B) : C(X, C(A, B)) :=
  (internalHomToCompactOpen A B).comp
    (ConcreteCategory.hom (C := CGWH.{u, u}) (MonoidalClosed.curry f))

private theorem nativeCompactOpenCurryRecipe_apply
    (f : A ⊗ X ⟶ B) (x : X) (a : A) :
    nativeCompactOpenCurryRecipe f x a = f (tensorMk a x) := by
  have h := internalHom_curry_apply f (tensorMk a x)
  rw [tensorMk_fst, tensorMk_snd] at h
  exact (internalHomToCompactOpen_apply A B
    (MonoidalClosed.curry f x) a).trans h

/-- The RAW compact-open map of the original native product family. -/
public def nativeCurriedProductMap (f : A ⊗ X ⟶ B) :
    X.toTop ⟶ TopCat.of C(A, B) :=
  TopCat.ofHom (nativeCompactOpenCurryRecipe f)

private theorem nativeCurriedProductMap_hom_computed (f : A ⊗ X ⟶ B) :
    (nativeCurriedProductMap f).hom = nativeCompactOpenCurryRecipe f := by
  unfold nativeCurriedProductMap
  exact TopCat.hom_ofHom _

/-- The actual native pair is evaluated, without an ordinary-product
inverse or replacement of the family. -/
public theorem nativeCurriedProductMap_apply
    (f : A ⊗ X ⟶ B) (x : X) (a : A) :
    nativeCurriedProductMap f x a = f (tensorMk a x) :=
  (congrArg (fun k : C(X, C(A, B)) => k x a)
    (nativeCurriedProductMap_hom_computed f)).trans
      (nativeCompactOpenCurryRecipe_apply f x a)

/-- Original second-variable composition is literal after native currying. -/
public theorem nativeCurriedProductMap_comp_second
    {D : CGWH.{u, u}} (j : X ⟶ D) (f : A ⊗ D ⟶ B) :
    nativeCurriedProductMap ((A ◁ j) ≫ f) =
      cgwhToTop.map j ≫ nativeCurriedProductMap f := by
  have hcomp (x : X) (a : A) :
      (cgwhToTop.map j ≫ nativeCurriedProductMap f) x a =
        nativeCurriedProductMap f (j x) a := by
    have h := ConcreteCategory.comp_apply (C := TopCat.{u})
      (cgwhToTop.map j) (nativeCurriedProductMap f) x
    exact congrArg (fun k : C(A, B) => k a) h
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro a
  exact (nativeCurriedProductMap_apply ((A ◁ j) ≫ f) x a).trans
    ((congrArg f (tensorMk_whiskerLeft j a x)).trans
      ((nativeCurriedProductMap_apply f (j x) a).symm.trans (hcomp x a).symm))

private theorem cartesianLift_apply
    {S C D : CGWH.{u, u}} (f : S ⟶ C) (g : S ⟶ D) (s : S) :
    CartesianMonoidalCategory.lift f g s = tensorMk (f s) (g s) := by
  apply (tensorEquivProd C D).injective
  rw [tensorEquivProd_tensorMk]
  apply Prod.ext
  · rw [tensorEquivProd_apply_fst]
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst f g) s
  · rw [tensorEquivProd_apply_snd]
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd f g) s

private def parameterTranspose (A J X : CGWH.{u, u}) :
    A ⊗ (J ⊗ X) ⟶ J ⊗ (A ⊗ X) :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.snd A (J ⊗ X) ≫
      CartesianMonoidalCategory.fst J X)
    (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst A (J ⊗ X))
      (CartesianMonoidalCategory.snd A (J ⊗ X) ≫
        CartesianMonoidalCategory.snd J X))

private theorem parameterTranspose_apply (A J X : CGWH.{u, u})
    (a : A) (t : J) (x : X) :
    parameterTranspose A J X (tensorMk a (tensorMk t x)) =
      tensorMk t (tensorMk a x) := by
  rw [parameterTranspose, cartesianLift_apply]
  simp only [ConcreteCategory.comp_apply, tensorMk_fst, tensorMk_snd]
  rw [cartesianLift_apply]
  simp only [ConcreteCategory.comp_apply, tensorMk_fst, tensorMk_snd]

private structure NativeCurryHomotopyData
    {f g : A ⊗ X ⟶ B}
    (H : ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, u}) f) (ConcreteCategory.hom (C := CGWH.{u, u}) g)) where
  map : C(unitInterval × X, C(A, B))
  value : ∀ t x a, map (t, x) a = H (t, tensorMk a x)

private def nativeCurryHomotopyData
    {f g : A ⊗ X ⟶ B}
    (H : ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, u}) f) (ConcreteCategory.hom (C := CGWH.{u, u}) g)) :
    NativeCurryHomotopyData H := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  let Jc : CompHaus.{u} := CompHaus.of (ULift.{u} unitInterval)
  letI : IsGeneratedBy P Jc := by
    change IsGeneratedBy P (P Jc)
    infer_instance
  letI : UCompactlyGeneratedSpace.{u} Jc :=
    (isGeneratedBy_compactHausProbes_iff (Y := Jc)).mp inferInstance
  let J : CGWH.{u, u} := CGWH.of Jc
  let e : J ≃ₜ unitInterval := Homeomorph.ulift
  let U : CGWH.{u, u} := A ⊗ X
  let action : J ⊗ U ⟶ B := ConcreteCategory.ofHom
    (H.toContinuousMap.comp
      (((e : C(J, unitInterval)).prodMap (ContinuousMap.id U)).comp
        (prodComparisonToTop J U).hom))
  have haction (t : J) (z : U) :
      action (tensorMk t z) = H (e t, z) := by
    have hq : prodComparisonToTop J U (tensorMk t z) = (t, z) :=
      (tensorEquivProd_eq_prodComparisonToTop J U (tensorMk t z)).symm.trans
        (tensorEquivProd_tensorMk t z)
    exact congrArg (fun p : J × U => H (e p.1, p.2)) hq
  let h : (J ⊗ X : CGWH.{u, u}) ≃ₜ (unitInterval × X) :=
    (IsHomeomorph.homeomorph (prodComparisonToTop J X)
      (prodComparisonToTop_isHomeomorph_of_locallyCompact_left J X)).trans
        (Homeomorph.prodCongr e (Homeomorph.refl X))
  have hpoint (t : J) (x : X) : h (tensorMk t x) = (e t, x) := by
    have hq : prodComparisonToTop J X (tensorMk t x) = (t, x) :=
      (tensorEquivProd_eq_prodComparisonToTop J X (tensorMk t x)).symm.trans
        (tensorEquivProd_tensorMk t x)
    exact congrArg (Prod.map e id) hq
  let r := parameterTranspose A J X ≫ action
  let m : C(unitInterval × X, C(A, B)) :=
    (nativeCompactOpenCurryRecipe r).comp (h.symm : C(unitInterval × X, (J ⊗ X : CGWH.{u, u})))
  refine ⟨m, ?_⟩
  intro t x a
  let τ : J := e.symm t
  have hz : h.symm (t, x) = tensorMk τ x := by
    apply h.injective
    exact (h.apply_symm_apply (t, x)).trans
      ((hpoint τ x).trans (Prod.ext (e.apply_symm_apply t) rfl)).symm
  calc
    m (t, x) a = r (tensorMk a (h.symm (t, x))) :=
      nativeCompactOpenCurryRecipe_apply r (h.symm (t, x)) a
    _ = action (parameterTranspose A J X (tensorMk a (tensorMk τ x))) := by
      rw [hz]
      rfl
    _ = action (tensorMk τ (tensorMk a x)) :=
      congrArg action (parameterTranspose_apply A J X a τ x)
    _ = H (e τ, tensorMk a x) := haction τ (tensorMk a x)
    _ = H (t, tensorMk a x) :=
      congrArg (fun s => H (s, tensorMk a x)) (e.apply_symm_apply t)

private def nativeCurriedHomotopyRecipe
    {f g : A ⊗ X ⟶ B}
    (H : ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, u}) f) (ConcreteCategory.hom (C := CGWH.{u, u}) g)) :
    ContinuousMap.Homotopy (nativeCompactOpenCurryRecipe f)
      (nativeCompactOpenCurryRecipe g) := by
  let d := nativeCurryHomotopyData H
  exact
    { toContinuousMap := d.map
      map_zero_left := fun x => ContinuousMap.ext fun a =>
        (d.value 0 x a).trans ((H.map_zero_left (tensorMk a x)).trans
          (nativeCompactOpenCurryRecipe_apply f x a).symm)
      map_one_left := fun x => ContinuousMap.ext fun a =>
        (d.value 1 x a).trans ((H.map_one_left (tensorMk a x)).trans
          (nativeCompactOpenCurryRecipe_apply g x a).symm) }

/-- A whole homotopy of the original native product maps gives a genuine
compact-open homotopy of their original curried families. The actual
source-point trace is retained; it is not asserted to be stationary. -/
public def nativeCurriedProductHomotopy
    {f g : A ⊗ X ⟶ B}
    (H : ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, u}) f) (ConcreteCategory.hom (C := CGWH.{u, u}) g)) :
    ContinuousMap.Homotopy (nativeCurriedProductMap f).hom
      (nativeCurriedProductMap g).hom :=
  (nativeCurriedHomotopyRecipe H).cast
    (nativeCurriedProductMap_hom_computed f).symm
    (nativeCurriedProductMap_hom_computed g).symm

/-- Every time, second-variable point and active parameter is the same
original native product-homotopy value. -/
public theorem nativeCurriedProductHomotopy_apply
    {f g : A ⊗ X ⟶ B}
    (H : ContinuousMap.Homotopy (ConcreteCategory.hom (C := CGWH.{u, u}) f) (ConcreteCategory.hom (C := CGWH.{u, u}) g))
    (t : unitInterval) (x : X) (a : A) :
    nativeCurriedProductHomotopy H (t, x) a = H (t, tensorMk a x) := by
  unfold nativeCurriedProductHomotopy
  exact (nativeCurryHomotopyData H).value t x a

end CGWH

end
