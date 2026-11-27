/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_CurveModel.lean`
and
`P2M/Sol/S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces

/-!
# Curve models of a function field

A curve model of a field extension `L / K` (`AlgebraicCurve.CurveModel K L`) is an integral
scheme `C`, proper and smooth of relative dimension one over `Spec K`, together with a
`K`-isomorphism of `L` with the function field of `C`, under which the closed points of `C`
correspond bijectively to the places of `L / K`, the local ring at a closed point being the
valuation ring of its place, and in which every finite set of points lies in an affine open.

Curve models transport along `K`-isomorphisms of fields (`AlgebraicCurve.CurveModel.congr`).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicCurve

/-- The map from `K` to the function field of an integral scheme over `Spec K`. -/
def baseToFunctionField {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) : K →+* C.functionField :=
  (C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

/-- A curve model of `L / K`: an integral scheme `C`, proper and smooth of relative dimension one
over `Spec K`, with a `K`-isomorphism of `L` with the function field of `C` and a bijection from
the closed points of `C` to the places of `L / K` under which the local ring at each closed point
is the valuation ring of its place, such that every finite set of points of `C` lies in an affine
open. -/
structure CurveModel (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] where
  /-- The underlying scheme. -/
  C : Scheme.{u}
  /-- The structure morphism to `Spec K`. -/
  toBase : C ⟶ Spec (CommRingCat.of K)
  [isIntegral : IsIntegral C]
  [isProper : IsProper toBase]
  [smooth : SmoothOfRelativeDimension 1 toBase]
  /-- The identification of `L` with the function field of `C`. -/
  ffEquiv : L ≃+* C.functionField
  ffEquiv_algebraMap : ∀ a : K, ffEquiv (algebraMap K L a) = baseToFunctionField toBase a
  /-- The place attached to a closed point. -/
  placeOfPoint : closedPoints C → Place K L
  placeOfPoint_bijective : Function.Bijective placeOfPoint
  range_stalk_eq : ∀ x : closedPoints C,
    ((ffEquiv.symm : C.functionField ≃+* L).toRingHom.comp
        (algebraMap (C.presheaf.stalk x.1) C.functionField)).range =
      (placeOfPoint x).toValuationSubring.toSubring
  finset_subset_affineOpen : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

attribute [instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The `K`-algebra structure on the function field of a curve model. -/
abbrev functionFieldAlgebra (M : CurveModel K L) : Algebra K M.C.functionField :=
  (baseToFunctionField M.toBase).toAlgebra

/-- The identification of `L` with the function field, as a `K`-algebra isomorphism. -/
def ffAlgEquiv (M : CurveModel K L) :
    letI := M.functionFieldAlgebra
    L ≃ₐ[K] M.C.functionField :=
  letI := M.functionFieldAlgebra
  AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap

theorem ffAlgEquiv_apply (M : CurveModel K L) (f : L) : M.ffAlgEquiv f = M.ffEquiv f := rfl

/-- Closed points of a curve model are the places of `L / K`. -/
def placeEquiv (M : CurveModel K L) : closedPoints M.C ≃ Place K L :=
  Equiv.ofBijective M.placeOfPoint M.placeOfPoint_bijective

theorem placeEquiv_apply (M : CurveModel K L) (x : closedPoints M.C) :
    M.placeEquiv x = M.placeOfPoint x := rfl

/-- Over an algebraically closed field, the `K`-points of a curve model are the places. -/
def pointEquivPlace [IsAlgClosed K] (M : CurveModel K L) :
    {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} ≃ Place K L :=
  (pointEquivClosedPoint M.toBase).trans M.placeEquiv

theorem pointEquivPlace_apply [IsAlgClosed K] (M : CurveModel K L)
    (p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M.pointEquivPlace p = M.placeOfPoint (pointEquivClosedPoint M.toBase p) := rfl

/-- Transport of a curve model along a `K`-isomorphism of fields. -/
def congr {L' : Type w} [Field L'] [Algebra K L'] (e : L' ≃ₐ[K] L) (M : CurveModel K L') :
    CurveModel K L where
  C := M.C
  toBase := M.toBase
  ffEquiv := e.symm.toRingEquiv.trans M.ffEquiv
  ffEquiv_algebraMap a := by
    change M.ffEquiv (e.symm (algebraMap K L a)) = _
    rw [e.symm.commutes]
    exact M.ffEquiv_algebraMap a
  placeOfPoint x := Place.congrEquiv e.toRingEquiv (fun a => e.commutes a) (M.placeOfPoint x)
  placeOfPoint_bijective :=
    (Place.congrEquiv e.toRingEquiv (fun a => e.commutes a)).bijective.comp
      M.placeOfPoint_bijective
  range_stalk_eq x := by
    have hM := M.range_stalk_eq x
    have hcomp : ((e.symm.toRingEquiv.trans M.ffEquiv).symm :
          M.C.functionField ≃+* L).toRingHom.comp
          (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField) =
        (e.toRingEquiv : L' →+* L).comp
          ((M.ffEquiv.symm : M.C.functionField ≃+* L').toRingHom.comp
            (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)) := by
      ext y
      rfl
    rw [hcomp, ← RingHom.map_range, hM, Subring.map_equiv_eq_comap_symm]
    rfl
  finset_subset_affineOpen := M.finset_subset_affineOpen

end CurveModel

end AlgebraicCurve
