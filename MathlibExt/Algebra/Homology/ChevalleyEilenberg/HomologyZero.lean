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
# Degree-zero homology of bracket-presented CE models

Let `R` be a commutative ring and `X` a bracket-presented CE model. The bracket differential
from exterior degree one to degree zero is zero. Since exterior degree zero is `R`, degree-
zero homology is linearly equivalent to the coefficient ring.

The categorical isomorphism uses a lifted regular module in the model's exterior carrier
universe. Its scalar-coordinate form maps an exterior degree-zero class to its scalar
representative. Every model morphism preserves these coordinates, so the degree-zero homology
functor is naturally constant.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable {R : Type u} [CommRing R]

namespace Model

/-- The zero differential from CE exterior degree one.

For every bracket-presented model, the chain differential from degree one to degree zero
vanishes. -/
theorem differential_one_zero (X : Model.{u, v} R) :
    ((complexFunctor R).obj X).d 1 0 = 0 := by
  change X.data.toChainData.complex.d 1 0 = 0
  rw [ChainData.complex_d_succ, PresentedData.d_zero, ModuleCat.ofHom_zero]
  rfl

/-- The lifted scalar coordinate of CE exterior degree zero.

The degree-zero chain module is isomorphic to the regular coefficient ring lifted into the
model's joint carrier universe. -/
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

/-- The opcycle coordinate of CE degree zero.

Since the incoming differential is zero, the degree-zero chain object maps isomorphically to
the degree-zero opcycle object. -/
def zeroOpcyclesIso (X : Model.{u, v} R) :
    ((complexFunctor R).obj X).X 0 ≅ ((complexFunctor R).obj X).opcycles 0 :=
  ((complexFunctor R).obj X).pOpcyclesIso 1 0 (by simp) (differential_one_zero X)

/-- The categorical scalar isomorphism of CE homology degree zero.

Degree-zero homology of a bracket-presented model is isomorphic to the lifted regular
coefficient module. -/
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

/-- Naturality of the lifted scalar coordinate in CE degree zero.

A model homology map followed by the target scalar isomorphism equals the source scalar
isomorphism. -/
@[reassoc]
theorem homologyZeroIso_naturality
    {X Y : Model.{u, v} R} (f : X ⟶ Y) :
    (homologyFunctor R 0).map f ≫ (homologyZeroIso Y).hom =
      (homologyZeroIso X).hom := by
  exact homologyZeroIso_naturalityRaw f

/-- The constant-functor comparison for CE homology degree zero.

The degree-zero homology functor is naturally isomorphic to the constant functor with value
the lifted regular coefficient module. -/
def homologyZeroNatIso (R : Type u) [CommRing R] :
    homologyFunctor R 0 ≅
      (Functor.const (Model.{u, v} R)).obj
        (ModuleCat.of R (ULift.{max u v, u} R)) :=
  NatIso.ofComponents (fun X => homologyZeroIso X) fun f => by
    exact (homologyZeroIso_naturality f).trans (Category.comp_id _).symm

/-- The components of the constant degree-zero homology comparison.

At a model `X`, the natural comparison component is its scalar homology isomorphism. -/
@[simp]
theorem homologyZeroNatIso_app (X : Model.{u, v} R) :
    (homologyZeroNatIso R).app X = homologyZeroIso X :=
  rfl

/-- The scalar linear equivalence of CE homology degree zero.

Removing the carrier lift from the categorical scalar comparison gives `X.H 0 ≃ₗ[R] R`. -/
def homologyZeroLinearEquiv (X : Model.{u, v} R) : X.H 0 ≃ₗ[R] R :=
  (homologyZeroIso X).toLinearEquiv.trans ULift.moduleEquiv

/-- The scalar coordinate of an exterior degree-zero homology class.

The linear homology coordinate of a degree-zero class is the scalar coordinate of its exterior
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

/-- The exterior representative of a degree-zero scalar homology class.

The inverse scalar equivalence represents `r ∈ R` by its inverse exterior-degree-zero
coordinate, then takes its degree-zero class. -/
@[simp]
theorem homologyZeroLinearEquiv_symm_apply (X : Model.{u, v} R) (r : R) :
    (homologyZeroLinearEquiv X).symm r =
      X.data.toChainData.complex.isoHomologyι₀.inv
        (X.data.toChainData.complex.pOpcycles 0
          ((exteriorPower.zeroEquiv R X.carrier).symm r)) := by
  apply (homologyZeroLinearEquiv X).injective
  rw [LinearEquiv.apply_symm_apply, homologyZeroLinearEquiv_class,
    LinearEquiv.apply_symm_apply]

/-- Preservation of scalar homology coordinates by CE model maps.

The degree-zero homology map of every model morphism retains the scalar coordinate under the
source and target linear equivalences. -/
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
