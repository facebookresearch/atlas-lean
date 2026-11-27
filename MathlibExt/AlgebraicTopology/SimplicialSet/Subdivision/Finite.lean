/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateNerveFunctor
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
import Mathlib.Data.Fintype.Powerset

/-!
# Finiteness under simplicial subdivision

The categorical subdivision of every standard simplex has finitely many
nondegenerate simplices. Kan subdivision therefore preserves finite simplicial sets:
subdividing the finitely many nondegenerate carriers gives finitely many generating
finite subcomplexes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

private theorem finite_nonemptyFiniteChains
    (α : Type u) [PartialOrder α] [Finite α] :
    Finite (PartialOrder.NonemptyFiniteChains α) := by
  let _ := Fintype.ofFinite α
  exact Finite.of_injective
    (fun A : PartialOrder.NonemptyFiniteChains α => A.finset)
    (fun A B h => PartialOrder.NonemptyFiniteChains.ext h)

/--
The categorical subdivision of a standard simplex is a finite simplicial set
in every simplicial-set universe.
-/
theorem finite_sd_simplex (n : SimplexCategory) :
    SSet.Finite (SimplexCategory.sd.{u}.obj n) where
  finite := by
    let _ : Finite
        (PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1)))) :=
      finite_nonemptyFiniteChains _
    let P : PartOrd.{u} := PartOrd.of
      (PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))))
    let _ : Finite (PartialOrder.NonemptyFiniteChains P) :=
      finite_nonemptyFiniteChains _
    change Finite (CategoryTheory.nerve P).N
    exact Finite.of_equiv
      (PartialOrder.NonemptyFiniteChains P)
      (PartOrd.nerveNOrderIso P).symm.toEquiv

private theorem finite_sd_stdSimplex (n : SimplexCategory) :
    SSet.Finite (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) := by
  let _ : SSet.Finite (SimplexCategory.sd.{u}.obj n) :=
    finite_sd_simplex n
  exact SSet.finite_of_iso (SSet.stdSimplex.sdIso.app n).symm

private def carrierRange (A : SSet.{u}) (a : A.N) :
    (SSet.sd.obj A).Subcomplex :=
  SSet.Subcomplex.range
    (SSet.sd.map (SSet.yonedaEquiv.symm a.simplex))

private theorem finite_carrierRange (A : SSet.{u}) (a : A.N) :
    SSet.Finite (carrierRange A a) := by
  let _ : SSet.Finite (SSet.sd.obj (Δ[a.dim] : SSet.{u})) :=
    finite_sd_stdSimplex ⦋a.dim⦌
  dsimp only [carrierRange]
  infer_instance

private theorem iSup_range_sd_tautological_eq_top (A : SSet.{u}) :
    ⨆ (j : CostructuredArrow uliftYoneda A),
      SSet.Subcomplex.range (SSet.sd.map j.hom) = ⊤ := by
  let c := Presheaf.tautologicalCocone'
    (C := SimplexCategory) (P := A)
  have hc : IsColimit c := Presheaf.isColimitTautologicalCocone' A
  have hsd : IsColimit (SSet.sd.mapCocone c) :=
    isColimitOfPreserves SSet.sd hc
  exact SSet.iSup_range_eq_top_of_isColimit hsd

private theorem tautological_leg_range_le_carrier_iSup
    (A : SSet.{u}) (j : CostructuredArrow uliftYoneda A) :
    SSet.Subcomplex.range (SSet.sd.map j.hom) ≤
      ⨆ a : A.N, carrierRange A a := by
  let s : A.obj (Opposite.op j.left) :=
    CategoryTheory.uliftYonedaEquiv j.hom
  have hj0 : j.hom = CategoryTheory.uliftYonedaEquiv.symm s := by
    simp [s]
  obtain ⟨m, f, _hf, y, hs⟩ := A.exists_nonDegenerate s
  let y0 : A _⦋m⦌ := y
  let a : A.N := SSet.N.mk y0 y.property
  let f0 : CategoryTheory.uliftYoneda.obj j.left ⟶ Δ[m] :=
    SSet.stdSimplex.map f
  have hj : j.hom = f0 ≫ SSet.yonedaEquiv.symm y0 := by
    rw [hj0, hs]
    change SSet.yonedaEquiv.symm (A.map f.op y0) = _
    exact (SSet.yonedaEquiv_symm_naturality_left f y0).symm
  have hmap : SSet.sd.map j.hom =
      SSet.sd.map f0 ≫ SSet.sd.map (SSet.yonedaEquiv.symm y0) := by
    rw [hj, Functor.map_comp]
  rw [hmap, SSet.Subcomplex.range_comp]
  refine le_trans (SSet.Subcomplex.image_monotone _ le_top) ?_
  change (⊤ : (SSet.sd.obj (Δ[m] : SSet.{u})).Subcomplex).image
      (SSet.sd.map (SSet.yonedaEquiv.symm y0)) ≤ _
  rw [SSet.Subcomplex.image_top]
  exact le_iSup (carrierRange A) a

private theorem iSup_carrierRange_eq_top (A : SSet.{u}) :
    ⨆ a : A.N, carrierRange A a = ⊤ := by
  apply le_antisymm le_top
  rw [← iSup_range_sd_tautological_eq_top A]
  exact iSup_le (tautological_leg_range_le_carrier_iSup A)

/--
The Kan subdivision of a finite simplicial set is finite.
-/
theorem finite_sd (A : SSet.{u}) [A.Finite] :
    (SSet.sd.obj A).Finite := by
  rw [← SSet.finite_subcomplex_top_iff,
    ← iSup_carrierRange_eq_top A, SSet.finite_iSup_iff]
  exact finite_carrierRange A

instance (A : SSet.{u}) [A.Finite] : (SSet.sd.obj A).Finite :=
  finite_sd A

end SSet

end
