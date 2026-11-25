/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Homology
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Functor.Const

/-!
# Degree-zero homology of bracket-presented models

The bracket differential of a Chevalley–Eilenberg model vanishes from exterior degree one to
degree zero. Consequently degree-zero homology identifies with the coefficient ring, naturally
in model morphisms.

The categorical comparison uses a universe lift of the ring. Its linear-equivalence form has
target the ring itself and allows independent ring and Lie carrier universes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable {R : Type u} [CommRing R]

namespace Model

/-- The canonical CE differential from exterior degree one to degree zero vanishes. -/
theorem differential_one_zero (X : Model.{u, v} R) :
    ((complexFunctor R).obj X).d 1 0 = 0 := by
  change X.data.toChainData.complex.d 1 0 = 0
  rw [ChainData.complex_d_succ, PresentedData.d_zero, ModuleCat.ofHom_zero]
  rfl

/-- Exterior degree zero is canonically the coefficient ring. -/
def zeroCoefficientIso (X : Model.{u, v} R) :
    ((complexFunctor R).obj X).X 0 ≅ ModuleCat.of R (ULift.{max u v, u} R) :=
  ((exteriorPower.zeroEquiv R X.carrier).trans ULift.moduleEquiv.symm).toModuleIso

private theorem zeroCoefficientIso_naturality
    {X Y : Model.{u, v} R} (f : X ⟶ Y) :
    ((complexFunctor R).map f).f 0 ≫ (zeroCoefficientIso Y).hom =
      (zeroCoefficientIso X).hom := by
  apply ModuleCat.hom_ext
  change (ULift.moduleEquiv.symm.toLinearMap.comp
        (exteriorPower.zeroEquiv R Y.carrier).toLinearMap).comp
      (exteriorPower.map 0 f.lieHom.toLinearMap) =
    ULift.moduleEquiv.symm.toLinearMap.comp
      (exteriorPower.zeroEquiv R X.carrier).toLinearMap
  rw [LinearMap.comp_assoc, exteriorPower.zeroEquiv_naturality]

/-- In degree zero, every chain is an opcycle. -/
def zeroOpcyclesIso (X : Model.{u, v} R) :
    ((complexFunctor R).obj X).X 0 ≅ ((complexFunctor R).obj X).opcycles 0 :=
  ((complexFunctor R).obj X).pOpcyclesIso 1 0 (by simp) (differential_one_zero X)

/-- Degree-zero homology of a bracket-presented CE model, identified with the coefficient module
in the universe of the model's exterior powers. -/
def homologyZeroIso (X : Model.{u, v} R) :
    X.H 0 ≅ ModuleCat.of R (ULift.{max u v, u} R) :=
  ((complexFunctor R).obj X).isoHomologyι₀ ≪≫
    (zeroOpcyclesIso X).symm ≪≫ zeroCoefficientIso X

private theorem homologyZeroIso_characteristic (X : Model.{u, v} R) :
    ((complexFunctor R).obj X).pOpcycles 0 ≫
        ((complexFunctor R).obj X).isoHomologyι₀.inv ≫
          (homologyZeroIso X).hom =
      (zeroCoefficientIso X).hom := by
  change (zeroOpcyclesIso X).hom ≫
      ((complexFunctor R).obj X).isoHomologyι₀.inv ≫
      (((complexFunctor R).obj X).isoHomologyι₀ ≪≫
        (zeroOpcyclesIso X).symm ≪≫ zeroCoefficientIso X).hom = _
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
  exact (zeroOpcyclesIso X).hom_inv_id_assoc (zeroCoefficientIso X).hom

private theorem homologyZeroIso_naturalityRaw
    {X Y : Model.{u, v} R} (f : X ⟶ Y) :
    (homologyFunctor R 0).map f ≫ (homologyZeroIso Y).hom =
      (homologyZeroIso X).hom := by
  simp only [homologyFunctor_obj, homologyFunctor_map, complexFunctor_obj]
  let : IsIso (((complexFunctor R).obj X).pOpcycles 0) :=
    ((complexFunctor R).obj X).isIso_pOpcycles 1 0 (by simp) (differential_one_zero X)
  have hι :
      ((complexFunctor R).obj X).isoHomologyι₀.inv ≫
          HomologicalComplex.homologyMap
              (ChainData.map (R := R) (L := X.carrier) f.lieHom f.comm) 0 ≫
            (homologyZeroIso Y).hom =
        HomologicalComplex.opcyclesMap
            (ChainData.map (R := R) (L := X.carrier) f.lieHom f.comm) 0 ≫
          ((complexFunctor R).obj Y).isoHomologyι₀.inv ≫
            (homologyZeroIso Y).hom := by
    exact ChainComplex.isoHomologyι₀_inv_naturality_assoc
      ((complexFunctor R).map f) (homologyZeroIso Y).hom
  apply (cancel_epi (((complexFunctor R).obj X).pOpcycles 0 ≫
    ((complexFunctor R).obj X).isoHomologyι₀.inv)).mp
  conv_lhs =>
    rw [Category.assoc, hι, HomologicalComplex.p_opcyclesMap_assoc]
  conv_rhs => rw [Category.assoc]
  rw [homologyZeroIso_characteristic, homologyZeroIso_characteristic]
  exact zeroCoefficientIso_naturality f

/-- Every model morphism induces the identity in coefficient coordinates on degree-zero homology. -/
@[reassoc]
theorem homologyZeroIso_naturality
    {X Y : Model.{u, v} R} (f : X ⟶ Y) :
    (homologyFunctor R 0).map f ≫ (homologyZeroIso Y).hom =
      (homologyZeroIso X).hom := by
  exact homologyZeroIso_naturalityRaw f

/-- The degree-zero CE homology functor is naturally isomorphic to the constant coefficient-module
functor. -/
def homologyZeroNatIso (R : Type u) [CommRing R] :
    homologyFunctor R 0 ≅
      (Functor.const (Model.{u, v} R)).obj
        (ModuleCat.of R (ULift.{max u v, u} R)) :=
  NatIso.ofComponents (fun X => homologyZeroIso X) fun f => by
    exact (homologyZeroIso_naturality f).trans (Category.comp_id _).symm

/-- The natural comparison has the canonical degree-zero comparison as its component at each
model. -/
@[simp]
theorem homologyZeroNatIso_app (X : Model.{u, v} R) :
    (homologyZeroNatIso R).app X = homologyZeroIso X :=
  rfl

/-- Degree-zero CE homology as an `R`-linear equivalence with `R`, without exposing the
categorical universe lift. -/
def homologyZeroLinearEquiv (X : Model.{u, v} R) : X.H 0 ≃ₗ[R] R :=
  (homologyZeroIso X).toLinearEquiv.trans ULift.moduleEquiv

/-- The coefficient coordinate of a degree-zero class is the canonical coordinate of its exterior
representative. -/
theorem homologyZeroLinearEquiv_class (X : Model.{u, v} R)
    (a : ⋀[R]^0 X.carrier) :
    homologyZeroLinearEquiv X
        (X.data.toChainData.complex.isoHomologyι₀.inv
          ((X.data.toChainData.complex.pOpcycles 0 :
            chainObject R X.carrier 0 ⟶
              X.data.toChainData.complex.opcycles 0) a)) =
      exteriorPower.zeroEquiv R X.carrier a := by
  have h := congrArg
    (fun k : chainObject R X.carrier 0 ⟶
        ModuleCat.of R (ULift.{max u v, u} R) => (k a).down)
    (homologyZeroIso_characteristic X)
  exact h

/-- A scalar is represented in degree-zero homology by the canonical exterior degree-zero
representative of that scalar. -/
@[simp]
theorem homologyZeroLinearEquiv_symm_apply (X : Model.{u, v} R) (r : R) :
    (homologyZeroLinearEquiv X).symm r =
      X.data.toChainData.complex.isoHomologyι₀.inv
        (X.data.toChainData.complex.pOpcycles 0
          ((exteriorPower.zeroEquiv R X.carrier).symm r)) := by
  apply (homologyZeroLinearEquiv X).injective
  rw [LinearEquiv.apply_symm_apply, homologyZeroLinearEquiv_class,
    LinearEquiv.apply_symm_apply]

/-- The scalar coordinates of degree-zero homology are preserved by every CE model morphism. -/
theorem homologyZeroLinearEquiv_naturality
    {X Y : Model.{u, v} R} (f : X ⟶ Y) (a : X.H 0) :
    homologyZeroLinearEquiv Y ((homologyFunctor R 0).map f a) =
      homologyZeroLinearEquiv X a := by
  have h := congrArg
    (fun k : X.H 0 ⟶ ModuleCat.of R (ULift.{max u v, u} R) => (k a).down)
    (homologyZeroIso_naturality f)
  exact h

end Model

end ChevalleyEilenberg
